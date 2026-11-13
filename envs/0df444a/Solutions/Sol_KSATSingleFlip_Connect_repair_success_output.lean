-- Prove2me | solution 1 for KSATSingleFlip.Connect.repair_success_output
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:23:18.617786+00:00
-- url     : https://prove2.me/submissions/ee7fdef5-2e6b-4188-b32b-e5a3ba5b13db

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

namespace KSATSingleFlip.Connect

/-- Every matching-assigned clause is satisfied by the output when the matching
and retained-tree variables are disjoint. -/
theorem audit_matched_clause_satisfied {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x) (hm : IsPairMatching Φ s.J s.M)
    (hdisj : Disjoint s.VF (matchedVars Φ s.J s.M))
    (j : Fin Φ.length) (hj : j ∈ s.J) : ClauseSat s.output (Φ.get j) := by
  have hcard : (s.M j).card = 2 := (hm.1 j hj).2
  have hn : (s.M j).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hn
  have hvm : v ∈ matchedVars Φ s.J s.M := Finset.mem_biUnion.mpr ⟨j, hj, hv⟩
  have hvF : v ∉ s.VF := fun h => Finset.disjoint_left.mp hdisj h hvm
  have hvchoice : ∃ c ∈ s.J, v ∈ s.M c := ⟨j, hj, hv⟩
  have hchosen : Classical.choose hvchoice = j := by
    have hs := Classical.choose_spec hvchoice
    by_contra hne
    exact Finset.disjoint_left.mp (hm.2 _ hs.1 j hj hne) hs.2 hv
  have hvscope : v ∈ vbl (Φ.get j) := (hm.1 j hj).1 hv
  cases hval : (Φ.get j) v with
  | none =>
    have hsome : ((Φ.get j) v).isSome := (Finset.mem_filter.mp hvscope).2
    rw [hval] at hsome
    contradiction
  | some b =>
    have hout : s.output v = b := by
      unfold RState.output
      simp only [hvF, ↓reduceIte, dif_pos hvchoice, hchosen, hval, Option.getD_some]
    exact ⟨v, by rw [hout]; exact hval⟩

/-- Repair maintains disjointness of retained trees and matched variables. -/
theorem audit_step_preserves_tree_matching_disjoint {n : ℕ} (k : ℕ)
    (Φ : GFormula (Fin n)) (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool)
    (W : Finset (Fin n)) (s s' : RState Φ x) (c : Fin Φ.length)
    (hstep : RStep k Φ I0 x s c (some s')) (hcover : audit_covered Φ x W s)
    (hdisj : Disjoint s.VF (matchedVars Φ s.J s.M)) :
    Disjoint s'.VF (matchedVars Φ s'.J s'.M) := by
  obtain ⟨_, htree | hmatch⟩ := hstep
  · obtain ⟨T, _, _, hT, heq⟩ := htree
    cases heq
    apply Finset.disjoint_left.mpr
    intro v hvF hvM
    obtain ⟨p, hp, hvp⟩ := (audit_mem_VF Φ x _ v).mp hvF
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact Finset.disjoint_left.mp hdisj ((audit_mem_VF Φ x s v).mpr ⟨p, hp, hvp⟩) hvM
    · exact Finset.disjoint_left.mp hT hvp (hcover.2.2 hvM)
  · obtain ⟨_, hsuccess | hfail⟩ := hmatch
    · obtain ⟨M', _, _, heq⟩ := hsuccess
      cases heq
      apply Finset.disjoint_left.mpr
      intro v hvF hvM
      obtain ⟨p, hp, hvp⟩ := (audit_mem_VF Φ x _ v).mp hvF
      have hp' : Disjoint p.1.vars (matchedVars Φ (insert c s.J) M') :=
        of_decide_eq_true (List.mem_filter.mp hp).2
      exact Finset.disjoint_left.mp hp' hvp hvM
    · obtain ⟨_, heq⟩ := hfail
      contradiction

/-- Matching validity, coverage, and tree/matching disjointness persist along
any partial Repair execution. -/
theorem audit_reach_core_invariants {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s t : RState Φ x) (j : ℕ) (h : RepairReach k Φ I0 x s t j) :
    IsPairMatching Φ s.J s.M → audit_covered Φ x W s →
    Disjoint s.VF (matchedVars Φ s.J s.M) →
      IsPairMatching Φ t.J t.M ∧ audit_covered Φ x W t ∧
        Disjoint t.VF (matchedVars Φ t.J t.M) := by
  induction h with
  | refl s =>
    intro hm hc hd
    exact ⟨hm, hc, hd⟩
  | step s s' t c j hstep hreach ih =>
    intro hm hc hd
    exact ih (audit_step_preserves_matching k Φ I0 x s s' c hstep hm)
      (audit_step_preserves_covered k Φ I0 x W s s' c hstep hc)
      (audit_step_preserves_tree_matching_disjoint k Φ I0 x W s s' c hstep hc hd)

/-- At any reached terminal state, all matching-assigned clauses are satisfied. -/
theorem audit_reached_matching_satisfied {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ)
    (h : RepairReach k Φ I0 x (RState.init Φ x W) s j) :
    ∀ c ∈ s.J, ClauseSat s.output (Φ.get c) := by
  have hm : IsPairMatching Φ (RState.init Φ x W).J (RState.init Φ x W).M := by
    simp [IsPairMatching, RState.init]
  have hc := audit_initial_covered Φ x W
  have hd : Disjoint (RState.init Φ x W).VF
      (matchedVars Φ (RState.init Φ x W).J (RState.init Φ x W).M) := by
    simp [RState.init, RState.VF, matchedVars]
  obtain ⟨hm', _, hd'⟩ := audit_reach_core_invariants k Φ I0 x W _ _ _ h hm hc hd
  exact audit_matched_clause_satisfied Φ x s hm' hd'

/-- A present literal that is not true under x becomes true when its variable flips. -/
theorem audit_false_literal {n : ℕ} (x : Fin n → Bool) (C : GClause (Fin n))
    (v : Fin n) (hv : v ∈ vbl C) (hfalse : v ∉ satSet x C) : C v = some (!x v) := by
  have hsome : (C v).isSome := (Finset.mem_filter.mp hv).2
  have hne : C v ≠ some (x v) := by
    intro heq
    exact hfalse (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩)
  cases hcv : C v with
  | none => rw [hcv] at hsome; contradiction
  | some b =>
    cases hxb : x v <;> cases hb : b <;> simp_all

/-- A retained forcing-tree clause is satisfied by its flipped child. -/
theorem audit_retained_tree_clause_satisfied {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x) (T : ForcingTree Φ x)
    (assoc c : Fin Φ.length) (hT : (T, assoc) ∈ s.F) (hc : c ∈ T.cls) :
    ClauseSat s.output (Φ.get c) := by
  let v := T.child c
  have hvT : v ∈ T.vars := T.child_mem c hc
  have hvF : v ∈ s.VF := audit_tree_vars_in_VF Φ x s T assoc hT hvT
  have hvneq : v ≠ T.parent c := by
    intro heq
    have hd := T.depth_child c hc
    change T.depth v = T.depth (T.parent c) + 1 at hd
    rw [heq] at hd
    omega
  have hfalse : v ∉ satSet x (Φ.get c) := by
    rw [T.forces c hc]
    simp [hvneq]
  have hlit := audit_false_literal x (Φ.get c) v (T.child_vbl c hc) hfalse
  have hout : s.output v = !x v := by simp [RState.output, hvF]
  exact ⟨v, by rw [hout]; exact hlit⟩

private def audit_associations_false {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x) : Prop :=
  ∀ T c, (T, c) ∈ s.F → (Φ.get c) T.root = some (!x T.root)

/-- Retained trees keep the invariant that their root falsifies their associated
clause before it is flipped. -/
theorem audit_step_preserves_associations {n : ℕ} (k : ℕ)
    (Φ : GFormula (Fin n)) (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool)
    (s s' : RState Φ x) (c : Fin Φ.length)
    (hstep : RStep k Φ I0 x s c (some s'))
    (hassoc : audit_associations_false Φ x s) : audit_associations_false Φ x s' := by
  obtain ⟨hpend, htree | hmatch⟩ := hstep
  · obtain ⟨T, _, hroot, hdisj, heq⟩ := htree
    cases heq
    intro U d hU
    simp only [List.mem_append, List.mem_singleton] at hU
    rcases hU with hU | hU
    · exact hassoc U d hU
    · have heq : (U, d) = (T, c) := hU
      cases heq
      have hnotU : T.root ∉ s.U := Finset.disjoint_left.mp hdisj T.root_mem
      have hfalse : T.root ∉ satSet x (Φ.get c) := fun h => hnotU (hpend.2 h)
      exact audit_false_literal x (Φ.get c) T.root hroot hfalse
  · obtain ⟨_, hsuccess | hfail⟩ := hmatch
    · obtain ⟨M', _, _, heq⟩ := hsuccess
      cases heq
      intro T d hT
      exact hassoc T d (List.mem_filter.mp hT).1
    · obtain ⟨_, heq⟩ := hfail
      contradiction

theorem audit_reach_associations {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ)
    (h : RepairReach k Φ I0 x (RState.init Φ x W) s j) :
    audit_associations_false Φ x s := by
  have hgen : ∀ s t : RState Φ x, ∀ j, RepairReach k Φ I0 x s t j →
      audit_associations_false Φ x s → audit_associations_false Φ x t := by
    intro s t j hreach
    induction hreach with
    | refl s => intro hs; exact hs
    | step s s' t c j hstep hreach ih =>
      intro hs
      exact ih (audit_step_preserves_associations k Φ I0 x s s' c hstep hs)
  apply hgen _ _ _ h
  simp [audit_associations_false, RState.init]

/-- The associated clause of a retained tree is satisfied by its flipped root. -/
theorem audit_retained_associated_satisfied {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x) (T : ForcingTree Φ x)
    (c : Fin Φ.length) (hT : (T, c) ∈ s.F)
    (hassoc : audit_associations_false Φ x s) : ClauseSat s.output (Φ.get c) := by
  have hrF : T.root ∈ s.VF := audit_tree_vars_in_VF Φ x s T c hT T.root_mem
  have hout : s.output T.root = !x T.root := by simp [RState.output, hrF]
  exact ⟨T.root, by rw [hout]; exact hassoc T c hT⟩

private theorem audit_mem_A {n : ℕ} (Φ : GFormula (Fin n)) (x : Fin n → Bool)
    (s : RState Φ x) (c : Fin Φ.length) :
    c ∈ s.A ↔ ∃ p ∈ s.F, c = p.2 ∨ c ∈ p.1.cls := by
  unfold RState.A
  generalize hf : s.F = F
  clear hf
  induction F with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.foldr_cons, Finset.mem_union, Finset.mem_insert,
      List.mem_cons]
    rw [ih]
    aesop

/-- At every reached state, each assigned clause is satisfied by the final
assignment represented by that state. -/
theorem audit_reached_assigned_satisfied {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ)
    (h : RepairReach k Φ I0 x (RState.init Φ x W) s j) :
    ∀ c, s.Assigned c → ClauseSat s.output (Φ.get c) := by
  have hmatch := audit_reached_matching_satisfied k Φ I0 x W s j h
  have hassoc := audit_reach_associations k Φ I0 x W s j h
  intro c hc
  rcases hc with htree | hJ
  · obtain ⟨p, hp, heq | hin⟩ := (audit_mem_A Φ x s c).mp htree
    · cases p with
      | mk T d =>
        simp only at heq hp
        subst c
        exact audit_retained_associated_satisfied Φ x s T d hp hassoc
    · cases p with
      | mk T d =>
        exact audit_retained_tree_clause_satisfied Φ x s T d c hp hin
  · exact hmatch c hJ

/-- If a reached state has no pending clause, its output satisfies the whole formula. -/
theorem audit_reached_terminal_satisfies {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ)
    (h : RepairReach k Φ I0 x (RState.init Φ x W) s j)
    (hdone : ∀ c, ¬ s.Pending c) : s.output ∈ sols Φ := by
  have hm : IsPairMatching Φ (RState.init Φ x W).J (RState.init Φ x W).M := by
    simp [IsPairMatching, RState.init]
  have hc := audit_initial_covered Φ x W
  have hd : Disjoint (RState.init Φ x W).VF
      (matchedVars Φ (RState.init Φ x W).J (RState.init Φ x W).M) := by
    simp [RState.init, RState.VF, matchedVars]
  obtain ⟨_, hc', _⟩ := audit_reach_core_invariants k Φ I0 x W _ _ _ h hm hc hd
  exact audit_terminal_satisfies_if_assigned Φ x W s hc' hdone
    (audit_reached_assigned_satisfied k Φ I0 x W s j h)

/-- A successful run ends at an explicitly reachable terminal state. -/
theorem audit_success_terminal_state {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool)
    (s : RState Φ x) (r : Option (Finset (Fin n) × (Fin n → Bool))) (i : ℕ)
    (hrun : RepairRun k Φ I0 x s r i) :
    ∀ U y, r = some (U, y) →
      ∃ t j, RepairReach k Φ I0 x s t j ∧ t.U = U ∧ t.output = y ∧
        (∀ c, ¬ t.Pending c) := by
  induction hrun with
  | done s hdone =>
    intro U y heq
    cases heq
    exact ⟨s, 0, RepairReach.refl s, rfl, rfl, hdone⟩
  | fail s c hfail =>
    intro U y heq
    contradiction
  | step s s' c r i hstep hrun ih =>
    intro U y heq
    obtain ⟨t, j, hreach, hU, hy, hdone⟩ := ih U y heq
    exact ⟨t, j + 1, RepairReach.step s s' t c j hstep hreach, hU, hy, hdone⟩

/-- Every successful run returns a satisfying assignment with the required
support; only the repair's shortest-path clause remains to establish. -/
theorem audit_success_satisfies_and_support {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (r : Option (Finset (Fin n) × (Fin n → Bool))) (i : ℕ)
    (hrun : RepairRun k Φ I0 x (RState.init Φ x W) r i) :
    ∀ U y, r = some (U, y) →
      W ⊆ U ∧ y ∈ sols Φ ∧ ∀ u, u ∉ U → y u = x u := by
  intro U y heq
  obtain ⟨t, j, hreach, hU, hy, hdone⟩ :=
    audit_success_terminal_state k Φ I0 x _ r i hrun U y heq
  have hs := audit_reached_terminal_satisfies k Φ I0 x W t j hreach hdone
  rw [hy] at hs
  have hsupport := audit_success_support k Φ I0 x W _ r i hrun
    (audit_initial_covered Φ x W) U y heq
  exact ⟨hsupport.1, hs, hsupport.2⟩

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect

/-- A successful completed Repair run returns a satisfying assignment with the required support. -/
theorem solution {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (r : Option (Finset (Fin n) × (Fin n → Bool))) (i : ℕ)
    (hrun : RepairRun k Φ I0 x (RState.init Φ x W) r i) :
    ∀ U y, r = some (U, y) →
      W ⊆ U ∧ y ∈ sols Φ ∧ ∀ u, u ∉ U → y u = x u :=
  audit_success_satisfies_and_support k Φ I0 x W r i hrun
