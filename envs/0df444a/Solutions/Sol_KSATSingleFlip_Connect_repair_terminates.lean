-- Prove2me | solution 1 for KSATSingleFlip.Connect.repair_terminates
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:23:17.557847+00:00
-- url     : https://prove2.me/submissions/064eee2a-891e-45e8-ac1a-513356ac6dc2

import Definitions.Def_KSATSingleFlip_Connect_Repair

open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-- Each tree-repair step strictly enlarges the repair set: its root is a new variable. -/
theorem audit_tree_add_strict {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (U : Finset (Fin n)) (T : ForcingTree Φ x)
    (h : Disjoint T.vars U) : U ⊂ U ∪ T.vars := by
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · exact Finset.subset_union_left
  · intro heq
    have hroot : T.root ∈ U := by
      rw [heq]
      exact Finset.mem_union_right _ T.root_mem
    exact (Finset.disjoint_left.mp h T.root_mem) hroot

/-- A pair matching on J covers exactly twice as many variables as clauses. -/
theorem audit_pair_matching_card {n : ℕ} (Φ : GFormula (Fin n))
    (J : Finset (Fin Φ.length)) (M : Fin Φ.length → Finset (Fin n))
    (h : IsPairMatching Φ J M) : (matchedVars Φ J M).card = 2 * J.card := by
  unfold matchedVars
  rw [Finset.card_biUnion]
  · calc
      ∑ c ∈ J, (M c).card = ∑ _c ∈ J, 2 := by
        apply Finset.sum_congr rfl
        intro c hc
        exact (h.1 c hc).2
      _ = 2 * J.card := by simp [Nat.mul_comm]
  · intro a ha b hb hne
    exact h.2 a ha b hb hne

/-- Every successful repair iteration strictly increases |U| + |J|. -/
theorem audit_step_potential {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool)
    (s s' : RState Φ x) (c : Fin Φ.length)
    (hstep : RStep k Φ I0 x s c (some s')) :
    s.U.card + s.J.card < s'.U.card + s'.J.card := by
  obtain ⟨hpend, htree | hmatch⟩ := hstep
  · obtain ⟨T, _, _, hdisj, heq⟩ := htree
    cases heq
    simp only
    have hs := audit_tree_add_strict Φ x s.U T hdisj
    have hc := Finset.card_lt_card hs
    omega
  · obtain ⟨_, hsuccess | hfail⟩ := hmatch
    · obtain ⟨M', _, _, heq⟩ := hsuccess
      cases heq
      have hc : c ∉ s.J := by
        intro hmem
        exact hpend.1 (Or.inr hmem)
      have hi := Finset.card_insert_of_notMem hc
      have hu := Finset.card_le_card (Finset.subset_union_left :
        s.U ⊆ s.U ∪ matchedVars Φ (insert c s.J) M')
      simp only at *
      omega
    · obtain ⟨_, heq⟩ := hfail
      contradiction

/-- Successful iterations preserve the pair-matching invariant. -/
theorem audit_step_preserves_matching {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool)
    (s s' : RState Φ x) (c : Fin Φ.length)
    (hstep : RStep k Φ I0 x s c (some s'))
    (hm : IsPairMatching Φ s.J s.M) : IsPairMatching Φ s'.J s'.M := by
  obtain ⟨_, htree | hmatch⟩ := hstep
  · obtain ⟨T, _, _, _, heq⟩ := htree
    cases heq
    exact hm
  · obtain ⟨_, hsuccess | hfail⟩ := hmatch
    · obtain ⟨M', hM, _, heq⟩ := hsuccess
      cases heq
      exact hM
    · obtain ⟨_, heq⟩ := hfail
      contradiction

/-- The number of completed steps is bounded by the growth of the potential,
while the final state still carries a valid pair matching. -/
theorem audit_reach_potential {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool)
    (s s' : RState Φ x) (j : ℕ)
    (h : RepairReach k Φ I0 x s s' j) :
    IsPairMatching Φ s.J s.M →
      IsPairMatching Φ s'.J s'.M ∧
      s.U.card + s.J.card + j ≤ s'.U.card + s'.J.card := by
  induction h with
  | refl s =>
      intro hm
      exact ⟨hm, by omega⟩
  | step s s' s'' c j hstep hreach ih =>
      intro hm
      have hm' := audit_step_preserves_matching k Φ I0 x s s' c hstep hm
      obtain ⟨hm'', hp⟩ := ih hm'
      have hs := audit_step_potential k Φ I0 x s s' c hstep
      exact ⟨hm'', by omega⟩

/-- Every partial Repair run started from the initial state has at most 2n steps. -/
theorem audit_repair_reach_steps {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ)
    (h : RepairReach k Φ I0 x (RState.init Φ x W) s j) : j ≤ 2 * n := by
  have hm : IsPairMatching Φ (RState.init Φ x W).J (RState.init Φ x W).M := by
    simp [IsPairMatching, RState.init]
  obtain ⟨hm', hp⟩ := audit_reach_potential k Φ I0 x _ _ _ h hm
  have hmatch := audit_pair_matching_card Φ s.J s.M hm'
  have hmatchingbound : (matchedVars Φ s.J s.M).card ≤ n := by
    simpa using Finset.card_le_univ (matchedVars Φ s.J s.M)
  have hU : s.U.card ≤ n := by simpa using Finset.card_le_univ s.U
  have hW : W.card ≤ n := by simpa using Finset.card_le_univ W
  simp only [RState.init, Finset.card_empty, Nat.add_zero] at hp
  omega

/-- A valid state has potential at most 2n. -/
theorem audit_potential_bound {n : ℕ} (Φ : GFormula (Fin n)) (x : Fin n → Bool)
    (s : RState Φ x) (hm : IsPairMatching Φ s.J s.M) :
    s.U.card + s.J.card ≤ 2 * n := by
  have hc := audit_pair_matching_card Φ s.J s.M hm
  have hmatched : (matchedVars Φ s.J s.M).card ≤ n := by
    simpa using Finset.card_le_univ (matchedVars Φ s.J s.M)
  have hU : s.U.card ≤ n := by simpa using Finset.card_le_univ s.U
  omega

/-- A completed run has at most 2n successful steps and one possible failing step. -/
theorem audit_repair_run_steps {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool)
    (s : RState Φ x) (r : Option (Finset (Fin n) × (Fin n → Bool))) (i : ℕ)
    (h : RepairRun k Φ I0 x s r i) :
    IsPairMatching Φ s.J s.M → s.U.card + s.J.card + i ≤ 2 * n + 1 := by
  induction h with
  | done s hdone =>
      intro hm
      have hp := audit_potential_bound Φ x s hm
      omega
  | fail s c hfail =>
      intro hm
      have hp := audit_potential_bound Φ x s hm
      omega
  | step s s' c r i hstep hrun ih =>
      intro hm
      have hm' := audit_step_preserves_matching k Φ I0 x s s' c hstep hm
      have hp := audit_step_potential k Φ I0 x s s' c hstep
      have hbound := ih hm'
      omega

theorem audit_repair_cost_bound {n q i : ℕ} (hn : 0 < n) (hi : i ≤ 2 * n + 1) :
    (repairCost n q i : ℝ) ≤ 5 * n * (n + q) := by
  unfold repairCost
  push_cast
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hir : (i : ℝ) ≤ 2 * n + 1 := by exact_mod_cast hi
  have hp : (0 : ℝ) ≤ (5 * n - ((i : ℝ) + 2)) * (n + q) := by
    apply mul_nonneg
    · linarith
    · positivity
  nlinarith

/-- The finished- and partial-run cost clauses of Lemma 7.4 hold with C = 5. -/
theorem audit_repair_cost_clauses (k : ℕ) (hk : 1 ≤ k) (n : ℕ)
    (Φp : List (OAI.FixedClauseThreshold.ProperClause n k))
    (I0 : Finset (Fin (ofList Φp).length)) (x : Fin n → Bool) (W : Finset (Fin n)) :
    (∀ (r : Option (Finset (Fin n) × (Fin n → Bool))) (i : ℕ),
      RepairRun k (ofList Φp) I0 x (RState.init (ofList Φp) x W) r i →
        (repairCost n Φp.length i : ℝ) ≤ 5 * n * (n + Φp.length)) ∧
    (∀ (s : RState (ofList Φp) x) (j : ℕ),
      RepairReach k (ofList Φp) I0 x (RState.init (ofList Φp) x W) s j →
        (repairCost n Φp.length j : ℝ) ≤ 5 * n * (n + Φp.length)) := by
  have hm : IsPairMatching (ofList Φp) (RState.init (ofList Φp) x W).J
      (RState.init (ofList Φp) x W).M := by simp [IsPairMatching, RState.init]
  by_cases hn : n = 0
  · subst n
    have hempty : Φp = [] := by
      cases Φp with
      | nil => rfl
      | cons c cs =>
        have hc := c.property
        have hz : (Finset.univ.filter fun i : Fin 0 => (c.val i).isSome) = ∅ := by
          ext i
          exact Fin.elim0 i
        rw [hz] at hc
        simp only [Finset.card_empty] at hc
        omega
    subst Φp
    simp [repairCost]
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    constructor
    · intro r i h
      have hi := audit_repair_run_steps k (ofList Φp) I0 x _ r i h hm
      have hibound : i ≤ 2 * n + 1 := by omega
      exact audit_repair_cost_bound hn' hibound
    · intro s j h
      have hj := audit_repair_reach_steps k (ofList Φp) I0 x W s j h
      have hjbound : j ≤ 2 * n + 1 := by omega
      exact audit_repair_cost_bound hn' hjbound

/-- If each well-formed nonterminal state admits a step, the potential bound
forces the Repair run to terminate. This isolates one-step matching extension
from the termination argument. -/
theorem audit_termination_of_progress {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool)
    (progress : ∀ s : RState Φ x, IsPairMatching Φ s.J s.M →
      (∀ c, ¬ s.Pending c) ∨ ∃ c r, RStep k Φ I0 x s c r) :
    ∀ s : RState Φ x, IsPairMatching Φ s.J s.M →
      ∃ r i, RepairRun k Φ I0 x s r i := by
  have hrun : ∀ fuel (s : RState Φ x), IsPairMatching Φ s.J s.M →
      2 * n < s.U.card + s.J.card + fuel →
      ∃ r i, RepairRun k Φ I0 x s r i := by
    intro fuel
    induction fuel with
    | zero =>
        intro s hm hbig
        have hp := audit_potential_bound Φ x s hm
        omega
    | succ fuel ih =>
        intro s hm hbig
        rcases progress s hm with hdone | ⟨c, r, hstep⟩
        · exact ⟨some (s.U, s.output), 0, RepairRun.done s hdone⟩
        · cases r with
          | none => exact ⟨none, 1, RepairRun.fail s c hstep⟩
          | some s' =>
              have hm' := audit_step_preserves_matching k Φ I0 x s s' c hstep hm
              have hp := audit_step_potential k Φ I0 x s s' c hstep
              have hbig' : 2 * n < s'.U.card + s'.J.card + fuel := by omega
              obtain ⟨r, i, hrest⟩ := ih s' hm' hbig'
              exact ⟨r, i + 1, RepairRun.step s s' c r i hstep hrest⟩
  intro s hm
  apply hrun (2 * n + 1) s hm
  omega

/-- Repair's one-step progress follows from the usual matching augmentation
property, stated here for pair matchings on its fixed formula. -/
theorem audit_progress_of_augmentation {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool)
    (augment : ∀ (J : Finset (Fin Φ.length)) (M : Fin Φ.length → Finset (Fin n))
      (c : Fin Φ.length), IsPairMatching Φ J M → c ∉ J →
      (∃ M', IsPairMatching Φ (insert c J) M') →
      ∃ M', IsPairMatching Φ (insert c J) M' ∧
        matchedVars Φ J M ⊆ matchedVars Φ (insert c J) M') :
    ∀ s : RState Φ x, IsPairMatching Φ s.J s.M →
      (∀ c, ¬ s.Pending c) ∨ ∃ c r, RStep k Φ I0 x s c r := by
  intro s hm
  by_cases hdone : ∀ c, ¬ s.Pending c
  · exact Or.inl hdone
  · right
    push Not at hdone
    obtain ⟨c, hpend⟩ := hdone
    by_cases ht : ∃ T : ForcingTree Φ x, IsSmallTree k Φ I0 x T ∧ T.root ∈ vbl (Φ.get c) ∧
        Disjoint T.vars s.U
    · obtain ⟨T, hsmall, hroot, hdisj⟩ := ht
      refine ⟨c, some ⟨s.U ∪ T.vars, s.F ++ [(T, c)], s.J, s.M⟩, ?_⟩
      exact ⟨hpend, Or.inl ⟨T, hsmall, hroot, hdisj, rfl⟩⟩
    · by_cases hmatch : ∃ M' : Fin Φ.length → Finset (Fin n),
          IsPairMatching Φ (insert c s.J) M'
      · have hc : c ∉ s.J := by
          intro hc
          exact hpend.1 (Or.inr hc)
        obtain ⟨M', hM, hsubset⟩ := augment s.J s.M c hm hc hmatch
        refine ⟨c, some ⟨s.U ∪ matchedVars Φ (insert c s.J) M',
          s.F.filter (fun p => Disjoint p.1.vars (matchedVars Φ (insert c s.J) M')),
          insert c s.J, M'⟩, ?_⟩
        exact ⟨hpend, Or.inr ⟨ht, Or.inl ⟨M', hM, hsubset, rfl⟩⟩⟩
      · exact ⟨c, none, hpend, Or.inr ⟨ht, Or.inr ⟨hmatch, rfl⟩⟩⟩

/-- Under pair-matching augmentation, the initial Repair state has a completed run. -/
theorem audit_repair_terminates_of_augmentation {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (augment : ∀ (J : Finset (Fin Φ.length)) (M : Fin Φ.length → Finset (Fin n))
      (c : Fin Φ.length), IsPairMatching Φ J M → c ∉ J →
      (∃ M', IsPairMatching Φ (insert c J) M') →
      ∃ M', IsPairMatching Φ (insert c J) M' ∧
        matchedVars Φ J M ⊆ matchedVars Φ (insert c J) M') :
    ∃ r i, RepairRun k Φ I0 x (RState.init Φ x W) r i := by
  apply audit_termination_of_progress k Φ I0 x
    (audit_progress_of_augmentation k Φ I0 x augment)
  simp [IsPairMatching, RState.init]

/-- The output assignment agrees with the input outside the repair set whenever
the retained-tree and matching variables are contained in that set. -/
theorem audit_output_agrees_off_U {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x)
    (htree : s.VF ⊆ s.U) (hmatch : matchedVars Φ s.J s.M ⊆ s.U)
    (u : Fin n) (hu : u ∉ s.U) : s.output u = x u := by
  have htree' : u ∉ s.VF := fun h => hu (htree h)
  have hmatch' : ¬ ∃ c ∈ s.J, u ∈ s.M c := by
    rintro ⟨c, hc, hv⟩
    apply hu
    apply hmatch
    exact Finset.mem_biUnion.mpr ⟨c, hc, hv⟩
  simp [RState.output, htree', hmatch']

/-- At a terminal state, each unassigned clause retains an x-true literal outside U. -/
theorem audit_unassigned_has_true_outside {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x)
    (hdone : ∀ c, ¬ s.Pending c) (c : Fin Φ.length) (hun : ¬ s.Assigned c) :
    ∃ u, u ∉ s.U ∧ (Φ.get c) u = some (x u) := by
  have hnot : ¬ satSet x (Φ.get c) ⊆ s.U := by
    intro hsubset
    exact hdone c ⟨hun, hsubset⟩
  obtain ⟨u, hu, hout⟩ := Finset.not_subset.mp hnot
  refine ⟨u, hout, ?_⟩
  simpa [satSet] using hu

/-- Every variable in a retained tree belongs to the state's retained-variable set. -/
theorem audit_tree_vars_in_VF {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x) (T : ForcingTree Φ x) (c : Fin Φ.length)
    (h : (T, c) ∈ s.F) : T.vars ⊆ s.VF := by
  intro u hu
  unfold RState.VF
  generalize hf : s.F = F at *
  clear hf
  induction F with
  | nil => simp at h
  | cons a as ih =>
    simp only [List.mem_cons] at h
    simp only [List.map_cons, List.foldr_cons, Finset.mem_union]
    rcases h with he | hmem
    · subst a
      exact Or.inl hu
    · exact Or.inr (ih hmem)

theorem audit_mem_VF {n : ℕ} (Φ : GFormula (Fin n)) (x : Fin n → Bool)
    (s : RState Φ x) (u : Fin n) :
    u ∈ s.VF ↔ ∃ p ∈ s.F, u ∈ p.1.vars := by
  unfold RState.VF
  generalize hf : s.F = F
  clear hf
  induction F with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.foldr_cons, Finset.mem_union, List.mem_cons]
    rw [ih]
    aesop

def audit_covered {n : ℕ} (Φ : GFormula (Fin n)) (x : Fin n → Bool)
    (W : Finset (Fin n)) (s : RState Φ x) : Prop :=
  W ⊆ s.U ∧ s.VF ⊆ s.U ∧ matchedVars Φ s.J s.M ⊆ s.U

/-- Successful steps preserve that all changed variables remain inside U. -/
theorem audit_step_preserves_covered {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s s' : RState Φ x) (c : Fin Φ.length)
    (hstep : RStep k Φ I0 x s c (some s'))
    (hcover : audit_covered Φ x W s) : audit_covered Φ x W s' := by
  obtain ⟨_, htree | hmatch⟩ := hstep
  · obtain ⟨T, _, _, _, heq⟩ := htree
    cases heq
    constructor
    · exact hcover.1.trans Finset.subset_union_left
    constructor
    · intro u hu
      obtain ⟨p, hp, hup⟩ := (audit_mem_VF Φ x _ u).mp hu
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · apply Finset.mem_union_left
        apply hcover.2.1
        exact (audit_mem_VF Φ x s u).mpr ⟨p, hp, hup⟩
      · exact Finset.mem_union_right _ hup
    · exact hcover.2.2.trans Finset.subset_union_left
  · obtain ⟨_, hsuccess | hfail⟩ := hmatch
    · obtain ⟨M', _, _, heq⟩ := hsuccess
      cases heq
      constructor
      · exact hcover.1.trans Finset.subset_union_left
      constructor
      · intro u hu
        obtain ⟨p, hp, hup⟩ := (audit_mem_VF Φ x _ u).mp hu
        have hp' : p ∈ s.F := (List.mem_filter.mp hp).1
        apply Finset.mem_union_left
        apply hcover.2.1
        exact (audit_mem_VF Φ x s u).mpr ⟨p, hp', hup⟩
      · exact Finset.subset_union_right
    · obtain ⟨_, heq⟩ := hfail
      contradiction

/-- Any successful Repair output contains W and agrees with x off its repair set. -/
theorem audit_success_support {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (r : Option (Finset (Fin n) × (Fin n → Bool))) (i : ℕ)
    (hrun : RepairRun k Φ I0 x s r i) :
    audit_covered Φ x W s →
    ∀ U y, r = some (U, y) → W ⊆ U ∧ ∀ u, u ∉ U → y u = x u := by
  induction hrun with
  | done s hdone =>
      intro hcover U y heq
      cases heq
      exact ⟨hcover.1, audit_output_agrees_off_U Φ x s hcover.2.1 hcover.2.2⟩
  | fail s c hfail =>
      intro _ U y heq
      contradiction
  | step s s' c r i hstep hrun ih =>
      intro hcover U y heq
      exact ih (audit_step_preserves_covered k Φ I0 x W s s' c hstep hcover) U y heq

theorem audit_initial_covered {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (W : Finset (Fin n)) :
    audit_covered Φ x W (RState.init Φ x W) := by
  simp [audit_covered, RState.init, RState.VF, matchedVars]

/-- To prove terminal output satisfies the whole formula, it remains only to
check the assigned clauses; all other clauses retain a true literal outside U. -/
theorem audit_terminal_satisfies_if_assigned {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (W : Finset (Fin n)) (s : RState Φ x)
    (hcover : audit_covered Φ x W s) (hdone : ∀ c, ¬ s.Pending c)
    (hassigned : ∀ c, s.Assigned c → ClauseSat s.output (Φ.get c)) :
    s.output ∈ sols Φ := by
  simp only [sols, Finset.mem_filter, Finset.mem_univ, true_and]
  intro C hC
  obtain ⟨c, hc⟩ := List.mem_iff_get.mp hC
  subst C
  by_cases ha : s.Assigned c
  · exact hassigned c ha
  · obtain ⟨u, hu, htrue⟩ := audit_unassigned_has_true_outside Φ x s hdone c ha
    refine ⟨u, ?_⟩
    have ho := audit_output_agrees_off_U Φ x s hcover.2.1 hcover.2.2 u hu
    simpa [ho] using htrue

end KSATSingleFlip.Connect


open scoped Classical BigOperators

/- Generic bipartite matching exchange, adapted from the accepted Apache-2.0
platform proof `OAI.SeymourSecondNeighborhood.Bipartite.exists_matching_saturating_left_of_card_lt`.
It is copied under a fresh namespace so this file can be checked standalone. -/
namespace AuditMatching

variable {L R : Type*} {E : L → R → Prop}

def IsMatching (E : L → R → Prop) (M : Finset (L × R)) : Prop :=
  (∀ e ∈ M, E e.1 e.2) ∧
    Set.InjOn Prod.fst (M : Set (L × R)) ∧
    Set.InjOn Prod.snd (M : Set (L × R))

private theorem exchange_matching_subset {M N : Finset (L × R)}
    (hM : IsMatching E M) (hNM : N ⊆ M) : IsMatching E N := by
  exact ⟨fun e he => hM.1 e (hNM he),
    fun _ he _ hf h => hM.2.1 (hNM he) (hNM hf) h,
    fun _ he _ hf h => hM.2.2 (hNM he) (hNM hf) h⟩

private theorem exchange_matching_insert [DecidableEq L] [DecidableEq R]
    {M : Finset (L × R)} (hM : IsMatching E M) {a : L} {b : R}
    (hab : E a b) (ha : ∀ e ∈ M, e.1 ≠ a) (hb : ∀ e ∈ M, e.2 ≠ b) :
    IsMatching E (insert (a, b) M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact hab
    · exact hM.1 e he
  · intro e he f hf hef
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · rfl
      · exact False.elim (ha f hf hef.symm)
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact False.elim (ha e he hef)
      · exact hM.2.1 he hf hef
  · intro e he f hf hef
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · rfl
      · exact False.elim (hb f hf hef.symm)
    · rcases Finset.mem_insert.mp hf with rfl | hf
      · exact False.elim (hb e he hef)
      · exact hM.2.2 he hf hef

theorem exists_matching_saturating_left_of_card_lt [Fintype L] [Fintype R]
    [DecidableEq L] [DecidableEq R]
    {M N : Finset (L × R)} (hM : IsMatching E M) (hN : IsMatching E N)
    (hcard : M.card < N.card) :
    ∃ Q : Finset (L × R), IsMatching E Q ∧ Q.card = N.card ∧
      M.image Prod.fst ⊆ Q.image Prod.fst := by
  classical
  let family : Finset (Finset (L × R)) :=
    Finset.univ.filter (fun Q => IsMatching E Q ∧ Q.card = N.card)
  have hNfamily : N ∈ family := by simp [family, hN]
  obtain ⟨Q, hQfamily, hQmax⟩ :=
    family.exists_max_image (fun Q => (Q ∩ M).card) ⟨N, hNfamily⟩
  have hQ : IsMatching E Q ∧ Q.card = N.card :=
    (Finset.mem_filter.mp hQfamily).2
  refine ⟨Q, hQ.1, hQ.2, ?_⟩
  intro a ha
  by_contra haQ
  obtain ⟨m, hmM, rfl⟩ := Finset.mem_image.mp ha
  have hfree : ∀ e ∈ Q, e.1 ≠ m.1 := by
    intro e he heq
    exact haQ (Finset.mem_image.mpr ⟨e, he, heq⟩)
  have hmQ : m ∉ Q := fun hm => hfree m hm rfl
  have hexternal : ∃ e ∈ Q, e ∉ M := by
    by_contra h
    have hQM : Q ⊆ M := by
      intro e he
      by_contra heM
      exact h ⟨e, he, heM⟩
    have := Finset.card_le_card hQM
    omega
  have hremove : ∃ e ∈ Q, e ∉ M ∧ ∀ f ∈ Q, f.2 = m.2 → f = e := by
    by_cases hright : ∃ e ∈ Q, e.2 = m.2
    · obtain ⟨e, heQ, he⟩ := hright
      have heM : e ∉ M := by
        intro heM
        have hem : e = m := hM.2.2 heM hmM he
        exact hmQ (hem ▸ heQ)
      exact ⟨e, heQ, heM, fun f hf hfm => hQ.1.2.2 hf heQ (hfm.trans he.symm)⟩
    · obtain ⟨e, heQ, heM⟩ := hexternal
      exact ⟨e, heQ, heM, fun f hf hfm => False.elim (hright ⟨f, hf, hfm⟩)⟩
  obtain ⟨e, heQ, heM, he_unique⟩ := hremove
  let Q' := insert m (Q.erase e)
  have hQ'match : IsMatching E Q' := by
    apply exchange_matching_insert
      (exchange_matching_subset hQ.1 (Finset.erase_subset e Q)) (hM.1 m hmM)
    · intro f hf
      exact hfree f (Finset.mem_of_mem_erase hf)
    · intro f hf hfm
      exact (Finset.mem_erase.mp hf).1 (he_unique f (Finset.mem_of_mem_erase hf) hfm)
  have hmQerase : m ∉ Q.erase e := fun hm => hmQ (Finset.mem_of_mem_erase hm)
  have hQ'card : Q'.card = N.card := by
    dsimp [Q']
    rw [Finset.card_insert_of_notMem hmQerase, Finset.card_erase_of_mem heQ]
    have : 0 < Q.card := Finset.card_pos.mpr ⟨e, heQ⟩
    omega
  have hQ'family : Q' ∈ family := by simp [family, hQ'match, hQ'card]
  have hinter : Q' ∩ M = insert m (Q ∩ M) := by
    ext f
    simp only [Q', Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨rfl | ⟨hne, hfQ⟩, hfM⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hfQ, hfM⟩
    · rintro (rfl | ⟨hfQ, hfM⟩)
      · exact ⟨Or.inl rfl, hmM⟩
      · exact ⟨Or.inr ⟨fun hfe => heM (hfe ▸ hfM), hfQ⟩, hfM⟩
  have hmInter : m ∉ Q ∩ M := fun hm => hmQ (Finset.mem_inter.mp hm).1
  have hstrict : (Q ∩ M).card < (Q' ∩ M).card := by
    rw [hinter, Finset.card_insert_of_notMem hmInter]
    omega
  exact (not_lt_of_ge (hQmax Q' hQ'family)) hstrict


end AuditMatching

namespace KSATSingleFlip.Connect

private noncomputable def pairPick {V C : Type} [Fintype V] [DecidableEq V]
    (J : Finset C) (M : C → Finset V) (hcard : ∀ c ∈ J, (M c).card = 2)
    (c : ↥J) : Fin 2 → V := fun i =>
  ((Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hcard c.1 c.2]) :
    ↥(M c.1) ≃ Fin 2).symm i).1

private theorem pairPick_mem {V C : Type} [Fintype V] [DecidableEq V]
    (J : Finset C) (M : C → Finset V) (hcard : ∀ c ∈ J, (M c).card = 2)
    (c : ↥J) (i : Fin 2) : pairPick J M hcard c i ∈ M c.1 := by
  exact (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hcard c.1 c.2]) :
    ↥(M c.1) ≃ Fin 2).symm i |>.2

private theorem pairPick_injective {V C : Type} [Fintype V] [DecidableEq V]
    (J : Finset C) (M : C → Finset V) (hcard : ∀ c ∈ J, (M c).card = 2)
    (c : ↥J) : Function.Injective (pairPick J M hcard c) := by
  intro a b h
  apply (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hcard c.1 c.2]) :
    ↥(M c.1) ≃ Fin 2).symm.injective
  exact Subtype.ext h

private theorem pairPick_surjective {V C : Type} [Fintype V] [DecidableEq V]
    (J : Finset C) (M : C → Finset V) (hcard : ∀ c ∈ J, (M c).card = 2)
    (c : ↥J) (v : V) (hv : v ∈ M c.1) : ∃ i, pairPick J M hcard c i = v := by
  let e : ↥(M c.1) ≃ Fin 2 := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hcard c.1 c.2])
  refine ⟨e ⟨v, hv⟩, ?_⟩
  change (e.symm (e ⟨v, hv⟩)).1 = v
  simp

private noncomputable def pairEdges {V C : Type} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C] (J : Finset C) (M : C → Finset V)
    (hcard : ∀ c ∈ J, (M c).card = 2) : Finset (V × (C × Fin 2)) :=
  Finset.univ.image (fun z : ↥J × Fin 2 => (pairPick J M hcard z.1 z.2, (z.1.1, z.2)))

private theorem pairEdges_card {V C : Type} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C] (J : Finset C) (M : C → Finset V)
    (hcard : ∀ c ∈ J, (M c).card = 2) :
    (pairEdges J M hcard).card = 2 * J.card := by
  unfold pairEdges
  rw [Finset.card_image_of_injective]
  · simp [Fintype.card_prod, Fintype.card_coe, Nat.mul_comm]
  · intro a b hab
    have hright : (a.1.1, a.2) = (b.1.1, b.2) := congrArg Prod.snd hab
    rcases a with ⟨⟨ac, ha⟩, ai⟩
    rcases b with ⟨⟨bc, hb⟩, bi⟩
    simp only [Prod.mk.injEq] at hright
    obtain ⟨rfl, rfl⟩ := hright
    rfl

private theorem pairEdges_left {V C : Type} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C] (J : Finset C) (M : C → Finset V)
    (hcard : ∀ c ∈ J, (M c).card = 2) :
    (pairEdges J M hcard).image Prod.fst = J.biUnion M := by
  ext v
  constructor
  · intro hv
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_biUnion.mpr ⟨z.1.1, z.1.2, pairPick_mem J M hcard z.1 z.2⟩
  · intro hv
    obtain ⟨c, hc, hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨i, hi⟩ := pairPick_surjective J M hcard ⟨c, hc⟩ v hv
    apply Finset.mem_image.mpr
    refine ⟨(v, (c, i)), ?_, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(⟨c, hc⟩, i), Finset.mem_univ _, ?_⟩
    simp [hi]

private theorem pairEdges_matching {n : ℕ} (Φ : GFormula (Fin n))
    (J K : Finset (Fin Φ.length)) (M : Fin Φ.length → Finset (Fin n))
    (hM : IsPairMatching Φ J M) (hJK : J ⊆ K) :
    AuditMatching.IsMatching (fun (v : Fin n) (slot : Fin Φ.length × Fin 2) =>
      slot.1 ∈ K ∧ v ∈ vbl (Φ.get slot.1))
      (pairEdges J M (fun c hc => (hM.1 c hc).2)) := by
  let hcard : ∀ c ∈ J, (M c).card = 2 := fun c hc => (hM.1 c hc).2
  change AuditMatching.IsMatching _ (pairEdges J M hcard)
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp he
    refine ⟨hJK z.1.2, ?_⟩
    exact (hM.1 z.1.1 z.1.2).1 (pairPick_mem J M hcard z.1 z.2)
  · intro e he f hf hef
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hf
    have hval : z.1.1 = w.1.1 := by
      by_contra hne
      have hd := hM.2 z.1.1 z.1.2 w.1.1 w.1.2 hne
      have hvw : pairPick J M hcard z.1 z.2 ∈ M w.1.1 := by
        change pairPick J M hcard z.1 z.2 = pairPick J M hcard w.1 w.2 at hef
        rw [hef]
        exact pairPick_mem J M hcard w.1 w.2
      exact Finset.disjoint_left.mp hd (pairPick_mem J M hcard z.1 z.2) hvw
    have hz : z.1 = w.1 := Subtype.ext hval
    have hi : z.2 = w.2 := by
      apply pairPick_injective J M hcard z.1
      simpa [hz] using hef
    cases z with
    | mk zc zi =>
      cases w with
      | mk wc wi =>
        simp only at hz hi
        subst wc
        subst wi
        rfl
  · intro e he f hf hef
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hf
    have hslots : (z.1.1, z.2) = (w.1.1, w.2) := hef
    have hval : z.1.1 = w.1.1 := (Prod.mk.inj hslots).1
    have hi : z.2 = w.2 := (Prod.mk.inj hslots).2
    have hz : z.1 = w.1 := Subtype.ext hval
    simp [hz, hi]


/-- Pair-matching augmentation preserves the variables already matched. -/
theorem audit_pair_matching_augmentation {n : ℕ} (Φ : GFormula (Fin n))
    (J : Finset (Fin Φ.length)) (M : Fin Φ.length → Finset (Fin n))
    (c : Fin Φ.length) (hm : IsPairMatching Φ J M) (hc : c ∉ J)
    (hex : ∃ M', IsPairMatching Φ (insert c J) M') :
    ∃ M', IsPairMatching Φ (insert c J) M' ∧
      matchedVars Φ J M ⊆ matchedVars Φ (insert c J) M' := by
  classical
  let K := insert c J
  obtain ⟨N, hn⟩ := hex
  have hmcard : ∀ j ∈ J, (M j).card = 2 := fun j hj => (hm.1 j hj).2
  have hncard : ∀ j ∈ K, (N j).card = 2 := fun j hj => (hn.1 j hj).2
  let old := pairEdges J M hmcard
  let new := pairEdges K N hncard
  let rel := fun (v : Fin n) (slot : Fin Φ.length × Fin 2) =>
    slot.1 ∈ K ∧ v ∈ vbl (Φ.get slot.1)
  have hold : AuditMatching.IsMatching rel old :=
    pairEdges_matching Φ J K M hm (Finset.subset_insert _ _)
  have hnew : AuditMatching.IsMatching rel new := pairEdges_matching Φ K K N hn (by rfl)
  have holdcard : old.card = 2 * J.card := pairEdges_card J M hmcard
  have hnewcard : new.card = 2 * K.card := pairEdges_card K N hncard
  have hlt : old.card < new.card := by
    rw [holdcard, hnewcard]
    simp [K, Finset.card_insert_of_notMem hc]
  obtain ⟨Q, hQ, hQcard, hleft⟩ :=
    AuditMatching.exists_matching_saturating_left_of_card_lt hold hnew hlt
  let slots : Finset (Fin Φ.length × Fin 2) := K.product Finset.univ
  have hslotSub : Q.image Prod.snd ⊆ slots := by
    intro p hp
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
    have hr := hQ.1 e he
    exact Finset.mem_product.mpr ⟨hr.1, Finset.mem_univ _⟩
  have hrightcard : (Q.image Prod.snd).card = Q.card :=
    Finset.card_image_iff.mpr hQ.2.2
  have hslotsCard : slots.card = 2 * K.card := by simp [slots, Finset.card_product, Nat.mul_comm]
  have hslots : Q.image Prod.snd = slots := by
    apply Finset.eq_of_subset_of_card_le hslotSub
    rw [hrightcard, hQcard, hnewcard, hslotsCard]
  have hslotexists : ∀ j ∈ K, ∀ i : Fin 2, ∃ v : Fin n, (v, (j, i)) ∈ Q := by
    intro j hj i
    have hmemb : (j, i) ∈ Q.image Prod.snd := by
      rw [hslots]
      exact Finset.mem_product.mpr ⟨hj, Finset.mem_univ _⟩
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hmemb
    exact ⟨e.1, by cases e; simp_all⟩
  let chooseV : ↥K → Fin 2 → Fin n := fun j i => Classical.choose (hslotexists j.1 j.2 i)
  have hchoose : ∀ (j : ↥K) (i : Fin 2), (chooseV j i, (j.1, i)) ∈ Q := by
    intro j i
    exact Classical.choose_spec (hslotexists j.1 j.2 i)
  have hinj : ∀ j : ↥K, Function.Injective (chooseV j) := by
    intro j i i' heq
    have he := hQ.2.1 (hchoose j i) (hchoose j i') heq
    exact (Prod.mk.inj (congrArg Prod.snd he)).2
  let R : Fin Φ.length → Finset (Fin n) := fun j =>
    if hj : j ∈ K then Finset.univ.image (chooseV ⟨j, hj⟩) else ∅
  refine ⟨R, ?_, ?_⟩
  · constructor
    · intro j hj
      change j ∈ K at hj
      have hR : R j = Finset.univ.image (chooseV ⟨j, hj⟩) := by simp [R, hj]
      rw [hR]
      constructor
      · intro v hv
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
        exact (hQ.1 _ (hchoose ⟨j, hj⟩ i)).2
      · rw [Finset.card_image_of_injective _ (hinj ⟨j, hj⟩)]
        simp
    · intro j hj j' hj' hne
      change j ∈ K at hj
      change j' ∈ K at hj'
      apply Finset.disjoint_left.mpr
      intro v hv hv'
      have hR : R j = Finset.univ.image (chooseV ⟨j, hj⟩) := by simp [R, hj]
      have hR' : R j' = Finset.univ.image (chooseV ⟨j', hj'⟩) := by simp [R, hj']
      rw [hR] at hv
      rw [hR'] at hv'
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
      obtain ⟨i', _, hi'⟩ := Finset.mem_image.mp hv'
      have heq := hQ.2.1 (hchoose ⟨j, hj⟩ i) (hchoose ⟨j', hj'⟩ i') (hi.trans hi'.symm)
      have hs : (j, i) = (j', i') := congrArg Prod.snd heq
      exact hne (Prod.mk.inj hs).1
  · intro v hv
    have hvold : v ∈ old.image Prod.fst := by
      rw [pairEdges_left]
      exact hv
    have hvQ := hleft hvold
    obtain ⟨e, he, heq⟩ := Finset.mem_image.mp hvQ
    have hj : e.2.1 ∈ K := (hQ.1 e he).1
    have hchosen := hchoose ⟨e.2.1, hj⟩ e.2.2
    have he' : (chooseV ⟨e.2.1, hj⟩ e.2.2, (e.2.1, e.2.2)) = e := by
      apply hQ.2.2 hchosen he
      cases e with | mk v p => cases p; rfl
    have hvEq : chooseV ⟨e.2.1, hj⟩ e.2.2 = v := (congrArg Prod.fst he').trans heq
    apply Finset.mem_biUnion.mpr
    refine ⟨e.2.1, hj, ?_⟩
    simp only [R, dif_pos hj]
    exact Finset.mem_image.mpr ⟨e.2.2, Finset.mem_univ _, hvEq⟩

/-- Every initial Repair run admits a completed resolution. -/
theorem audit_repair_terminates {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n)) :
    ∃ r i, RepairRun k Φ I0 x (RState.init Φ x W) r i := by
  exact audit_repair_terminates_of_augmentation k Φ I0 x W
    (audit_pair_matching_augmentation Φ)

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect

/-- The nondeterministic Repair algorithm has a completed run. -/
theorem solution {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n)) :
    ∃ r i, RepairRun k Φ I0 x (RState.init Φ x W) r i :=
  audit_repair_terminates k Φ I0 x W
