-- Prove2me | solution 1 for KSATSingleFlip.Connect.repair_outside_tree_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T04:58:35.538366+00:00
-- url     : https://prove2.me/submissions/42329f41-2052-41ef-9a00-7ea9db6e1254

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

/-- The size estimate in Lemma 7.5: assignments that agree away from U differ
on at most |U| variables. -/
theorem audit_hamming_le_card {n : ℕ} (U : Finset (Fin n))
    (x y : Fin n → Bool) (h : ∀ u, u ∉ U → x u = y u) :
    hamming x y ≤ U.card := by
  apply Finset.card_le_card
  intro u hu
  by_contra hnot
  have hxy := h u hnot
  have hne : x u ≠ y u := (Finset.mem_filter.mp hu).2
  exact hne hxy

/-- Two inputs and the repair target, all agreeing with the reference off U,
contribute at most twice the repair set's cardinality. -/
theorem audit_findPath_distance_bound {n : ℕ} (U : Finset (Fin n))
    (x y y' t : Fin n → Bool)
    (hy : ∀ u, u ∉ U → y u = x u)
    (hy' : ∀ u, u ∉ U → y' u = x u)
    (ht : ∀ u, u ∉ U → t u = x u) :
    hamming y t + hamming y' t ≤ 2 * U.card := by
  have h₁ : hamming y t ≤ U.card := audit_hamming_le_card U y t (by
    intro u hu
    rw [hy u hu, ht u hu])
  have h₂ : hamming y' t ≤ U.card := audit_hamming_le_card U y' t (by
    intro u hu
    rw [hy' u hu, ht u hu])
  omega

/-- Hamming distance satisfies the triangle inequality. -/
theorem audit_hamming_triangle {n : ℕ} (x y z : Fin n → Bool) :
    hamming x z ≤ hamming x y + hamming y z := by
  unfold hamming
  calc
    (disagree x z).card ≤ (disagree x y ∪ disagree y z).card := by
      apply Finset.card_le_card
      intro u hu
      simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_union] at *
      by_cases hxy : x u = y u
      · right
        intro hyz
        exact hu (hxy.trans hyz)
      · exact Or.inl hxy
    _ ≤ (disagree x y).card + (disagree y z).card := Finset.card_union_le _ _

/-- A returned path with at most 2n flips obeys the declared cost model. -/
theorem audit_findPath_cost_bound {n q : ℕ} (p : List (Fin n → Bool))
    (hn : 0 < n) (hp : p ≠ []) (hlen : pathLength p ≤ 2 * n) :
    (findPathCost n q p : ℝ) ≤ 8 * n * (n + q) := by
  have plen : p.length = pathLength p + 1 := by
    unfold pathLength
    have : 0 < p.length := List.length_pos_iff.mpr hp
    omega
  unfold findPathCost
  push_cast
  have hlenR : (pathLength p : ℝ) ≤ 2 * n := by exact_mod_cast hlen
  have plenR : (p.length : ℝ) = pathLength p + 1 := by exact_mod_cast plen
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [plenR]
  have hmul : (0 : ℝ) ≤ (2 * n - (pathLength p : ℝ)) * (2 * n + q) :=
    mul_nonneg (by linarith) (by positivity)
  have hm2 : (0 : ℝ) ≤ ((n : ℝ) - 1) * (n + q) :=
    mul_nonneg (by linarith) (by positivity)
  nlinarith

/-- A flip toward the target removes exactly one disagreement. -/
theorem audit_disagree_flip {n : ℕ} (z t : Fin n → Bool) (u : Fin n)
    (hu : z u ≠ t u) :
    disagree (flip z u) t = (disagree z t).erase u := by
  ext v
  by_cases hv : v = u
  · subst v
    simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, ne_eq, not_true_eq_false, false_and, iff_false]
    simp only [flip, Function.update_self]
    cases hz : z u <;> cases ht : t u <;> simp_all
  · simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    rw [show flip z u v = z v from Function.update_of_ne hv _ _]
    simp [hv]

/-- Any single-flip walk has at least Hamming distance many steps. -/
theorem audit_chain_lower_bound {n : ℕ} (a b : Fin n → Bool)
    (l : List (Fin n → Bool))
    (hchain : (a :: l).IsChain (fun x y => hamming x y = 1))
    (hlast : (a :: l).getLast? = some b) :
    hamming a b ≤ l.length := by
  induction l generalizing a with
  | nil =>
      simp only [List.getLast?_cons, List.getLast?_nil] at hlast
      have hab : a = b := by simpa using hlast
      subst b
      simp [hamming, disagree]
  | cons c cs ih =>
      have hc := List.isChain_cons_cons.mp hchain
      have hlast' : (c :: cs).getLast? = some b := by simpa using hlast
      have htail := ih c hc.2 hlast'
      have htri := audit_hamming_triangle a c b
      simp only [List.length_cons]
      omega

/-- Hamming distance one is exactly a single Boolean flip. -/
theorem audit_distance_one_is_flip {n : ℕ} (a c : Fin n → Bool)
    (h : hamming a c = 1) : ∃ u, c = flip a u := by
  have hc : (disagree a c).card = 1 := h
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hc
  refine ⟨u, ?_⟩
  funext v
  by_cases hv : v = u
  · subst v
    have hne : a u ≠ c u := by
      have : u ∈ disagree a c := by rw [hu]; simp
      simpa [disagree] using this
    simp only [flip, Function.update_self]
    cases ha : a u <;> cases ht : c u <;> simp_all
  · have hn : v ∉ disagree a c := by rw [hu]; simp [hv]
    have he : a v = c v := by simpa [disagree] using hn
    rw [show flip a u v = a v from Function.update_of_ne hv _ _]
    exact he.symm

/-- A flip away from the target adds one disagreement. -/
theorem audit_disagree_flip_away {n : ℕ} (z t : Fin n → Bool) (u : Fin n)
    (hu : z u = t u) :
    disagree (flip z u) t = insert u (disagree z t) := by
  ext v
  by_cases hv : v = u
  · subst v
    simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, or_true, iff_true]
    simp only [flip, Function.update_self]
    rw [← hu]
    cases h : z u <;> simp [h]
  · simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    rw [show flip z u v = z v from Function.update_of_ne hv _ _]
    simp [hv]

theorem audit_hamming_flip_away {n : ℕ} (z t : Fin n → Bool) (u : Fin n)
    (hu : z u = t u) : hamming (flip z u) t = hamming z t + 1 := by
  unfold hamming
  rw [audit_disagree_flip_away z t u hu, Finset.card_insert_of_notMem]
  simp [disagree, hu]

/-- The first move of a Hamming-shortest satisfying path is a legal flip toward t. -/
theorem audit_shortest_path_has_move {n : ℕ} (Φ : GFormula (Fin n))
    (z t : Fin n → Bool) (p : List (Fin n → Bool))
    (hp : IsSatPath Φ p z t) (hlen : pathLength p = hamming z t)
    (hne : z ≠ t) : ∃ u, z u ≠ t u ∧ FSat (flip z u) Φ := by
  rcases p with _ | ⟨a, p⟩
  · simp [IsSatPath, IsPathIn] at hp
  · have ha : a = z := by simpa [IsSatPath, IsPathIn] using hp.1
    subst a
    rcases p with _ | ⟨c, cs⟩
    · have : z = t := by simpa [IsSatPath, IsPathIn] using hp.2.1
      exact (hne this).elim
    · have hc : hamming z c = 1 := (List.isChain_cons_cons.mp hp.2.2.2).1
      have htail : hamming c t ≤ cs.length := by
        apply audit_chain_lower_bound c t cs
        · exact (List.isChain_cons_cons.mp hp.2.2.2).2
        · simpa using hp.2.1
      have hlen' : cs.length + 1 = hamming z t := by simpa [pathLength] using hlen
      obtain ⟨u, rfl⟩ := audit_distance_one_is_flip z c hc
      have hmove : z u ≠ t u := by
        intro he
        have haway := audit_hamming_flip_away z t u he
        omega
      refine ⟨u, hmove, ?_⟩
      have hs := hp.2.2.1 (flip z u) (by simp)
      simpa [sols] using hs

theorem audit_hamming_flip_toward {n : ℕ} (z t : Fin n → Bool) (u : Fin n)
    (hu : z u ≠ t u) : hamming (flip z u) t + 1 = hamming z t := by
  unfold hamming
  rw [audit_disagree_flip z t u hu]
  have hm : u ∈ disagree z t := by simpa [disagree] using hu
  exact Finset.card_erase_add_one hm

theorem audit_hamming_single_flip {n : ℕ} (z : Fin n → Bool) (u : Fin n) :
    hamming z (flip z u) = 1 := by
  have hs : disagree z (flip z u) = {u} := by
    ext v
    by_cases hv : v = u
    · subst v
      have : z u ≠ flip z u u := by
        simp only [flip, Function.update_self]
        cases h : z u <;> simp
      simpa [disagree] using this
    · simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      rw [show flip z u v = z v from Function.update_of_ne hv _ _]
      simp [hv]
  simp [hamming, hs]

/-- Greedy routing succeeds whenever every satisfying intermediate assignment has a
shortest satisfying continuation to t, and its flips are confined to U. -/
theorem audit_greedy_success {n : ℕ} (Φ : GFormula (Fin n))
    (x t : Fin n → Bool) (U : Finset (Fin n))
    (ht : ∀ u, u ∉ U → t u = x u)
    (H : ∀ z, z ∈ sols Φ → (∀ u, u ∉ U → z u = x u) →
      ∃ p, IsSatPath Φ p z t ∧ pathLength p = hamming z t) :
    ∀ fuel z, z ∈ sols Φ → (∀ u, u ∉ U → z u = x u) →
      hamming z t ≤ fuel →
      ∃ p, greedyWalk Φ t fuel z = some p ∧ IsSatPath Φ p z t ∧
        pathLength p = hamming z t := by
  intro fuel
  induction fuel with
  | zero =>
      intro z hz hoff hdist
      have he : z = t := by
        funext u
        by_contra hne
        have hm : u ∈ disagree z t := by simpa [disagree] using hne
        have : 0 < hamming z t := Finset.card_pos.mpr ⟨u, hm⟩
        omega
      subst z
      refine ⟨[t], ?_, ?_, ?_⟩
      · simp [greedyWalk]
      · simp [IsSatPath, IsPathIn, hz]
      · simp [pathLength, hamming, disagree]
  | succ fuel ih =>
      intro z hz hoff hdist
      by_cases he : z = t
      · subst z
        refine ⟨[t], ?_, ?_, ?_⟩
        · simp [greedyWalk]
        · simp [IsSatPath, IsPathIn, hz]
        · simp [pathLength, hamming, disagree]
      · obtain ⟨p, hp, hplen⟩ := H z hz hoff
        obtain ⟨u, hune, husat⟩ := audit_shortest_path_has_move Φ z t p hp hplen he
        let cand := Finset.univ.filter fun u => z u ≠ t u ∧ FSat (flip z u) Φ
        have hnon : cand.Nonempty := ⟨u, by simp [cand, hune, husat]⟩
        let v := cand.min' hnon
        have hvmem : v ∈ cand := Finset.min'_mem cand hnon
        have hv : z v ≠ t v ∧ FSat (flip z v) Φ := by simpa [cand] using hvmem
        have hvU : v ∈ U := by
          by_contra hn
          exact hv.1 ((hoff v hn).trans (ht v hn).symm)
        have hnext : flip z v ∈ sols Φ := by simpa [sols] using hv.2
        have hoffnext : ∀ u, u ∉ U → flip z v u = x u := by
          intro u hu
          have huv : u ≠ v := by intro h; subst u; exact hu hvU
          rw [show flip z v u = z u from Function.update_of_ne huv _ _]
          exact hoff u hu
        have hstep := audit_hamming_flip_toward z t v hv.1
        have hdnext : hamming (flip z v) t ≤ fuel := by omega
        obtain ⟨q, hq, hqpath, hqlen⟩ := ih (flip z v) hnext hoffnext hdnext
        have qne : q ≠ [] := by
          intro hnil
          subst q
          simp [IsSatPath, IsPathIn] at hqpath
        have hqhead : q.head? = some (flip z v) := hqpath.1
        refine ⟨z :: q, ?_, ?_, ?_⟩
        · simp only [greedyWalk, if_neg he]
          change (if h : cand.Nonempty then
            (greedyWalk Φ t fuel (flip z (cand.min' h))).map (z :: ·) else none) = _
          rw [dif_pos hnon]
          change Option.map (z :: ·) (greedyWalk Φ t fuel (flip z v)) = some (z :: q)
          simp [hq]
        · rcases q with _ | ⟨a, qs⟩
          · exact (qne rfl).elim
          · have ha : a = flip z v := by simpa using hqhead
            subst a
            refine ⟨rfl, ?_, ?_, ?_⟩
            · simpa using hqpath.2.1
            · intro w hw
              simp only [List.mem_cons] at hw
              rcases hw with rfl | hw
              · exact hz
              · exact hqpath.2.2.1 w (by simpa using hw)
            · exact List.isChain_cons_cons.mpr ⟨audit_hamming_single_flip z v, hqpath.2.2.2⟩
        · have hqpos : 0 < q.length := List.length_pos_iff.mpr qne
          simp only [pathLength, List.length_cons] at hqlen ⊢
          omega

theorem audit_hamming_symm {n : ℕ} (x y : Fin n → Bool) : hamming x y = hamming y x := by
  simp [hamming, disagree, ne_comm]

/-- The two paths overlap at the target, listed only once. -/
theorem audit_join_paths {n : ℕ} (Φ : GFormula (Fin n))
    (y y' t : Fin n → Bool) (p q : List (Fin n → Bool))
    (hp : IsSatPath Φ p y t) (hq : IsSatPath Φ q y' t) :
    IsSatPath Φ (p ++ q.reverse.tail) y y' ∧
      pathLength (p ++ q.reverse.tail) = pathLength p + pathLength q := by
  obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.mp hp.2.1
  have hqrev : q.reverse.head? = some t := by simpa using hq.2.1
  obtain ⟨r, hr⟩ := List.head?_eq_some_iff.mp hqrev
  have hrevchain : q.reverse.IsChain (fun a b => hamming a b = 1) := by
    apply List.isChain_reverse.mpr
    exact hq.2.2.2.imp (by intro a b h; simpa [audit_hamming_symm] using h)
  have hchain : (l ++ [t] ++ r).IsChain (fun a b => hamming a b = 1) := by
    apply List.IsChain.append_overlap (l₂ := [t])
    · simpa [hl] using hp.2.2.2
    · simpa [hr] using hrevchain
    · simp
  have htail : q.reverse.tail = r := by rw [hr]; rfl
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · have hpne : p ≠ [] := by intro hh; simp [hh, IsSatPath, IsPathIn] at hp
      simpa [List.head?_append, hpne] using hp.1
    · rw [htail, hl]
      have hlast : (t :: r).getLast? = some y' := by
        rw [← hr]
        simpa using hq.1
      simpa [List.getLast?_append] using hlast
    · intro z hz
      simp only [List.mem_append] at hz
      rcases hz with hz | hz
      · exact hp.2.2.1 z hz
      · apply hq.2.2.1 z
        have : z ∈ q.reverse.tail := by simpa [htail] using hz
        exact List.mem_reverse.mp (List.mem_of_mem_tail this)
    · simpa [hl, htail] using hchain
  · have hpne : 0 < p.length := by
      apply List.length_pos_iff.mpr
      intro hh
      simp [hh, IsSatPath, IsPathIn] at hp
    have hqne : 0 < q.length := by
      apply List.length_pos_iff.mpr
      intro hh
      simp [hh, IsSatPath, IsPathIn] at hq
    simp only [pathLength, List.length_append, List.length_tail, List.length_reverse]
    omega

theorem audit_hamming_le_n {n : ℕ} (x y : Fin n → Bool) : hamming x y ≤ n := by
  simpa [hamming] using Finset.card_le_univ (disagree x y)

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

/-- A legal target-directed flip at every compatible nonterminal assignment
implies the shortest-path clause of a repair. -/
theorem audit_path_of_progress {n : ℕ} (Φ : GFormula (Fin n))
    (x y : Fin n → Bool) (U : Finset (Fin n))
    (hy : ∀ u, u ∉ U → y u = x u)
    (hprogress : ∀ z, z ∈ sols Φ → (∀ u, u ∉ U → z u = x u) → z ≠ y →
      ∃ u, z u ≠ y u ∧ FSat (flip z u) Φ) :
    ∀ z, z ∈ sols Φ → (∀ u, u ∉ U → z u = x u) →
      ∃ p, IsSatPath Φ p z y ∧ pathLength p = hamming z y := by
  have hpath : ∀ fuel z, z ∈ sols Φ → (∀ u, u ∉ U → z u = x u) →
      hamming z y ≤ fuel → ∃ p, IsSatPath Φ p z y ∧ pathLength p = hamming z y := by
    intro fuel
    induction fuel with
    | zero =>
      intro z hz hoff hdist
      have he : z = y := by
        funext u
        by_contra hne
        have hm : u ∈ disagree z y := by simpa [disagree] using hne
        have : 0 < hamming z y := Finset.card_pos.mpr ⟨u, hm⟩
        omega
      subst z
      exact ⟨[y], by simp [IsSatPath, IsPathIn, hz], by simp [pathLength, hamming, disagree]⟩
    | succ fuel ih =>
      intro z hz hoff hdist
      by_cases he : z = y
      · subst z
        exact ⟨[y], by simp [IsSatPath, IsPathIn, hz], by simp [pathLength, hamming, disagree]⟩
      · obtain ⟨v, hv, hsat⟩ := hprogress z hz hoff he
        have hvU : v ∈ U := by
          by_contra hn
          exact hv ((hoff v hn).trans (hy v hn).symm)
        have hnext : flip z v ∈ sols Φ := by simpa [sols] using hsat
        have hoffnext : ∀ u, u ∉ U → flip z v u = x u := by
          intro u hu
          have huv : u ≠ v := by intro h; subst u; exact hu hvU
          rw [show flip z v u = z u from Function.update_of_ne huv _ _]
          exact hoff u hu
        have hstep := audit_hamming_flip_toward z y v hv
        have hdnext : hamming (flip z v) y ≤ fuel := by omega
        obtain ⟨q, hqpath, hqlen⟩ := ih (flip z v) hnext hoffnext hdnext
        have hqne : q ≠ [] := by
          intro hnil
          subst q
          simp [IsSatPath, IsPathIn] at hqpath
        have hqhead : q.head? = some (flip z v) := hqpath.1
        refine ⟨z :: q, ?_, ?_⟩
        · rcases q with _ | ⟨a, qs⟩
          · exact (hqne rfl).elim
          · have ha : a = flip z v := by simpa using hqhead
            subst a
            refine ⟨rfl, ?_, ?_, ?_⟩
            · simpa using hqpath.2.1
            · intro w hw
              simp only [List.mem_cons] at hw
              rcases hw with rfl | hw
              · exact hz
              · exact hqpath.2.2.1 w (by simpa using hw)
            · exact List.isChain_cons_cons.mpr ⟨audit_hamming_single_flip z v, hqpath.2.2.2⟩
        · have hqpos : 0 < q.length := List.length_pos_iff.mpr hqne
          simp only [pathLength, List.length_cons] at hqlen ⊢
          omega
  intro z hz hoff
  exact hpath n z hz hoff (audit_hamming_le_n z y)

/-- A successful run is an (x,W)-repair once the one-step flip property is
proved for each subformula. -/
theorem audit_success_isRepair_of_progress {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (r : Option (Finset (Fin n) × (Fin n → Bool))) (i : ℕ)
    (hrun : RepairRun k Φ I0 x (RState.init Φ x W) r i)
    (U : Finset (Fin n)) (y : Fin n → Bool) (heq : r = some (U, y))
    (hprogress : ∀ (I : Finset (Fin Φ.length)) z,
      z ∈ sols (subF Φ I) → (∀ u, u ∉ U → z u = x u) → z ≠ y →
        ∃ u, z u ≠ y u ∧ FSat (flip z u) (subF Φ I)) :
    IsRepair Φ x W U y := by
  obtain ⟨hW, hy, hoff⟩ := audit_success_satisfies_and_support k Φ I0 x W r i hrun U y heq
  refine ⟨hW, hy, hoff, ?_⟩
  intro I z hz hzoff
  exact audit_path_of_progress (subF Φ I) x y U hoff (hprogress I) z hz hzoff

private def audit_tree_disjoint {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x) : Prop :=
  ∀ p ∈ s.F, ∀ q ∈ s.F, p ≠ q → Disjoint p.1.vars q.1.vars

/-- Retained trees have pairwise disjoint variable sets. -/
theorem audit_step_preserves_tree_disjoint {n : ℕ} (k : ℕ)
    (Φ : GFormula (Fin n)) (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool)
    (W : Finset (Fin n)) (s s' : RState Φ x) (c : Fin Φ.length)
    (hstep : RStep k Φ I0 x s c (some s')) (hcover : audit_covered Φ x W s)
    (hdisj : audit_tree_disjoint Φ x s) : audit_tree_disjoint Φ x s' := by
  obtain ⟨_, htree | hmatch⟩ := hstep
  · obtain ⟨T, _, _, hT, heq⟩ := htree
    cases heq
    intro p hp q hq hpq
    simp only [List.mem_append, List.mem_singleton] at hp hq
    rcases hp with hp | rfl <;> rcases hq with hq | rfl
    · exact hdisj p hp q hq hpq
    · apply Finset.disjoint_left.mpr
      intro v hvp hvT
      have hvF : v ∈ s.VF := (audit_mem_VF Φ x s v).mpr ⟨p, hp, hvp⟩
      exact Finset.disjoint_left.mp hT hvT (hcover.2.1 hvF)
    · apply Finset.disjoint_left.mpr
      intro v hvT hvq
      have hvF : v ∈ s.VF := (audit_mem_VF Φ x s v).mpr ⟨q, hq, hvq⟩
      exact Finset.disjoint_left.mp hT hvT (hcover.2.1 hvF)
    · exact (hpq rfl).elim
  · obtain ⟨_, hsuccess | hfail⟩ := hmatch
    · obtain ⟨M', _, _, heq⟩ := hsuccess
      cases heq
      intro p hp q hq hpq
      exact hdisj p (List.mem_filter.mp hp).1 q (List.mem_filter.mp hq).1 hpq
    · obtain ⟨_, heq⟩ := hfail
      contradiction

private def audit_tree_assigned_covered {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x) : Prop :=
  ∀ c ∈ s.A, satSet x (Φ.get c) ⊆ s.U

/-- All x-true literals of clauses assigned to trees lie in the repair set. -/
theorem audit_step_preserves_tree_assigned_covered {n : ℕ} (k : ℕ)
    (Φ : GFormula (Fin n)) (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool)
    (s s' : RState Φ x) (c : Fin Φ.length)
    (hstep : RStep k Φ I0 x s c (some s'))
    (hcover : audit_tree_assigned_covered Φ x s) :
    audit_tree_assigned_covered Φ x s' := by
  obtain ⟨hpend, htree | hmatch⟩ := hstep
  · obtain ⟨T, _, _, _, heq⟩ := htree
    cases heq
    intro d hd v hv
    obtain ⟨p, hp, hpclause⟩ := (audit_mem_A Φ x _ d).mp hd
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · apply Finset.mem_union_left
      exact hcover d ((audit_mem_A Φ x s d).mpr ⟨p, hp, hpclause⟩) hv
    · rcases hpclause with rfl | hdT
      · exact Finset.mem_union_left _ (hpend.2 hv)
      · have heq := T.forces d hdT
        rw [heq] at hv
        have hvp : v = T.parent d := Finset.mem_singleton.mp hv
        subst v
        exact Finset.mem_union_right _ (T.parent_mem d hdT)
  · obtain ⟨_, hsuccess | hfail⟩ := hmatch
    · obtain ⟨M', _, _, heq⟩ := hsuccess
      cases heq
      intro d hd v hv
      obtain ⟨p, hp, hpclause⟩ := (audit_mem_A Φ x _ d).mp hd
      have hp' := (List.mem_filter.mp hp).1
      exact Finset.mem_union_left _ (hcover d ((audit_mem_A Φ x s d).mpr ⟨p, hp', hpclause⟩) hv)
    · obtain ⟨_, heq⟩ := hfail
      contradiction

private def audit_matching_assigned_covered {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x) : Prop :=
  ∀ c ∈ s.J, satSet x (Φ.get c) ⊆ s.U

/-- All x-true literals of matching-assigned clauses lie in U. -/
theorem audit_step_preserves_matching_assigned_covered {n : ℕ} (k : ℕ)
    (Φ : GFormula (Fin n)) (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool)
    (s s' : RState Φ x) (c : Fin Φ.length)
    (hstep : RStep k Φ I0 x s c (some s'))
    (hcover : audit_matching_assigned_covered Φ x s) :
    audit_matching_assigned_covered Φ x s' := by
  obtain ⟨hpend, htree | hmatch⟩ := hstep
  · obtain ⟨T, _, _, _, heq⟩ := htree
    cases heq
    intro d hd v hv
    exact Finset.mem_union_left _ (hcover d hd hv)
  · obtain ⟨_, hsuccess | hfail⟩ := hmatch
    · obtain ⟨M', _, _, heq⟩ := hsuccess
      cases heq
      intro d hd v hv
      rcases Finset.mem_insert.mp hd with rfl | hd
      · exact Finset.mem_union_left _ (hpend.2 hv)
      · exact Finset.mem_union_left _ (hcover d hd hv)
    · obtain ⟨_, heq⟩ := hfail
      contradiction

/-- Disjoint nonempty witness sets occupy strictly more points than there are
witnesses whenever D contains a point outside T and singleton witnesses lie in T.
This is the counting step behind the first phase of the source's path proof. -/
theorem audit_disjoint_witness_count {α β : Type} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (D T : Finset β) (U : α → Finset β)
    (hnon : ∀ a ∈ F, (U a).Nonempty)
    (hsub : ∀ a ∈ F, U a ⊆ D)
    (hdisj : (↑F : Set α).PairwiseDisjoint U)
    (hone : ∀ a ∈ F, (U a).card = 1 → U a ⊆ T)
    (hout : ∃ v ∈ D, v ∉ T) : F.card < D.card := by
  classical
  let all := F.biUnion U
  have hallsub : all ⊆ D := by
    intro v hv
    obtain ⟨a, ha, hv⟩ := Finset.mem_biUnion.mp hv
    exact hsub a ha hv
  have hsum : all.card = ∑ a ∈ F, (U a).card := Finset.card_biUnion hdisj
  have hFle : F.card ≤ all.card := by
    rw [hsum]
    have h := Finset.sum_le_sum (s := F) (f := fun _ => (1 : ℕ))
      (g := fun a => (U a).card) (fun a ha => Finset.card_pos.mpr (hnon a ha))
    simpa using h
  by_cases heq : all = D
  · obtain ⟨v, hvD, hvT⟩ := hout
    have hvall : v ∈ all := heq ▸ hvD
    obtain ⟨a, ha, hva⟩ := Finset.mem_biUnion.mp hvall
    have ha2 : 1 < (U a).card := by
      have hpos := Finset.card_pos.mpr (hnon a ha)
      by_contra hnot
      have hcard : (U a).card = 1 := by omega
      exact hvT (hone a ha hcard hva)
    have hstrict := Finset.sum_lt_sum (s := F) (f := fun _ => (1 : ℕ))
      (g := fun a => (U a).card)
      (fun a ha => Finset.card_pos.mpr (hnon a ha)) ⟨a, ha, ha2⟩
    rw [← hsum, heq] at hstrict
    simpa using hstrict
  · have hlt : all.card < D.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hallsub, heq⟩)
    omega

/-- Flipping a variable that no clause forces preserves satisfaction. -/
theorem audit_unforced_flip_satisfies {n : ℕ} (Φ : GFormula (Fin n))
    (z : Fin n → Bool) (v : Fin n) (hz : FSat z Φ)
    (hunforced : ∀ c : Fin Φ.length, ¬ Forces z (Φ.get c) v) :
    FSat (flip z v) Φ := by
  intro C hC
  obtain ⟨c, hc⟩ := List.mem_iff_get.mp hC
  subst C
  obtain ⟨u, hu⟩ := hz _ (List.get_mem Φ c)
  by_cases huv : u = v
  · subst u
    have hex : ∃ w, w ≠ v ∧ (Φ.get c) w = some (z w) := by
      by_contra hn
      have hforce : Forces z (Φ.get c) v := by
        unfold Forces
        ext w
        simp only [satSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hw
          by_contra hne
          exact hn ⟨w, hne, hw⟩
        · intro heq
          subst w
          exact hu
      exact hunforced c hforce
    obtain ⟨w, hwne, hw⟩ := hex
    refine ⟨w, ?_⟩
    rw [show flip z v w = z w from Function.update_of_ne hwne _ _]
    exact hw
  · refine ⟨u, ?_⟩
    rw [show flip z v u = z u from Function.update_of_ne huv _ _]
    exact hu

/-- If fewer clauses force variables of D than there are variables in D,
then some variable of D can be flipped while preserving satisfaction. -/
theorem audit_fewer_forcing_clauses_give_flip {n : ℕ} (Φ : GFormula (Fin n))
    (z : Fin n → Bool) (D : Finset (Fin n)) (hz : FSat z Φ)
    (hcount : ((Finset.univ.filter fun c : Fin Φ.length =>
      ∃ v ∈ D, Forces z (Φ.get c) v).card) < D.card) :
    ∃ v ∈ D, FSat (flip z v) Φ := by
  classical
  let F : Finset (Fin Φ.length) := Finset.univ.filter fun c =>
    ∃ v ∈ D, Forces z (Φ.get c) v
  have hlen : F.card < D.card := hcount
  by_contra hno
  push Not at hno
  have hforce : ∀ v ∈ D, ∃ c : Fin Φ.length, Forces z (Φ.get c) v := by
    intro v hv
    by_contra hn
    have hu : ∀ c : Fin Φ.length, ¬ Forces z (Φ.get c) v := by simpa using hn
    exact hno v hv (audit_unforced_flip_satisfies Φ z v hz hu)
  have hcover : D ⊆ F.biUnion (fun c => satSet z (Φ.get c)) := by
    intro v hv
    obtain ⟨c, hc⟩ := hforce v hv
    have hcF : c ∈ F := by
      change c ∈ Finset.univ.filter _
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, v, hv, hc⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨c, hcF, ?_⟩
    rw [hc]
    simp
  have hunion : (F.biUnion (fun c => satSet z (Φ.get c))).card ≤ F.card := by
    calc
      _ ≤ ∑ c ∈ F, (satSet z (Φ.get c)).card := Finset.card_biUnion_le
      _ = F.card := by
        calc
          _ = ∑ _c ∈ F, (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro c hc
            have hc' : ∃ v ∈ D, Forces z (Φ.get c) v := (Finset.mem_filter.mp hc).2
            obtain ⟨v, _, hv⟩ := hc'
            rw [hv]
            simp
          _ = F.card := by simp
  have hc := Finset.card_le_card hcover
  omega

/-- First-phase progress from the disjoint clause-witness invariant used in
Lemma 7.4: if disagreement extends beyond the trees, a target-directed flip exists. -/
theorem audit_first_phase_progress {n : ℕ} (Φ : GFormula (Fin n))
    (z y : Fin n → Bool) (treeVars : Finset (Fin n)) (hz : FSat z Φ)
    (hout : ∃ v ∈ disagree z y, v ∉ treeVars)
    (U : Fin Φ.length → Finset (Fin n))
    (hnon : ∀ c ∈ (Finset.univ.filter fun c : Fin Φ.length =>
      ∃ v ∈ disagree z y, Forces z (Φ.get c) v), (U c).Nonempty)
    (hsub : ∀ c ∈ (Finset.univ.filter fun c : Fin Φ.length =>
      ∃ v ∈ disagree z y, Forces z (Φ.get c) v), U c ⊆ disagree z y)
    (hdisj : (↑(Finset.univ.filter fun c : Fin Φ.length =>
      ∃ v ∈ disagree z y, Forces z (Φ.get c) v) : Set (Fin Φ.length)).PairwiseDisjoint U)
    (hone : ∀ c ∈ (Finset.univ.filter fun c : Fin Φ.length =>
      ∃ v ∈ disagree z y, Forces z (Φ.get c) v), (U c).card = 1 → U c ⊆ treeVars) :
    ∃ v, z v ≠ y v ∧ FSat (flip z v) Φ := by
  classical
  have hcount := audit_disjoint_witness_count
    (Finset.univ.filter fun c : Fin Φ.length => ∃ v ∈ disagree z y, Forces z (Φ.get c) v)
    (disagree z y) treeVars U hnon hsub hdisj hone hout
  obtain ⟨v, hv, hflip⟩ := audit_fewer_forcing_clauses_give_flip Φ z (disagree z y) hz hcount
  exact ⟨v, by simpa [disagree] using hv, hflip⟩

private def audit_owned {n : ℕ} {Φ : GFormula (Fin n)} {x : Fin n → Bool}
    (p : ForcingTree Φ x × Fin Φ.length) : Finset (Fin Φ.length) :=
  insert p.2 p.1.cls

private def audit_owned_disjoint {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x) : Prop :=
  (∀ p ∈ s.F, p.2 ∉ p.1.cls) ∧
  (∀ p ∈ s.F, Disjoint (audit_owned p) s.J) ∧
  (∀ p ∈ s.F, ∀ q ∈ s.F, p ≠ q → Disjoint (audit_owned p) (audit_owned q))

private theorem audit_owned_mem_A {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x) (p : ForcingTree Φ x × Fin Φ.length)
    (hp : p ∈ s.F) {c : Fin Φ.length} (hc : c ∈ audit_owned p) : c ∈ s.A := by
  apply (audit_mem_A Φ x s c).mpr
  refine ⟨p, hp, ?_⟩
  simpa [audit_owned] using hc

private theorem audit_new_tree_clause_uncovered {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (T : ForcingTree Φ x) (U : Finset (Fin n))
    (hdisj : Disjoint T.vars U) (c : Fin Φ.length) (hc : c ∈ T.cls) :
    ¬ satSet x (Φ.get c) ⊆ U := by
  intro hsub
  have hp : T.parent c ∈ T.vars := T.parent_mem c hc
  have hp' : T.parent c ∈ satSet x (Φ.get c) := by rw [T.forces c hc]; simp
  exact Finset.disjoint_left.mp hdisj hp (hsub hp')

/-- The clause sets owned by different retained trees and the matching are disjoint. -/
theorem audit_step_preserves_owned_disjoint {n : ℕ} (k : ℕ)
    (Φ : GFormula (Fin n)) (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool)
    (s s' : RState Φ x) (c : Fin Φ.length)
    (hstep : RStep k Φ I0 x s c (some s'))
    (hA : audit_tree_assigned_covered Φ x s)
    (hJ : audit_matching_assigned_covered Φ x s)
    (hown : audit_owned_disjoint Φ x s) : audit_owned_disjoint Φ x s' := by
  obtain ⟨hpend, htree | hmatch⟩ := hstep
  · obtain ⟨T, _, _, hT, heq⟩ := htree
    cases heq
    have hnew : ∀ d ∈ T.cls, ¬ satSet x (Φ.get d) ⊆ s.U :=
      fun d hd => audit_new_tree_clause_uncovered Φ x T s.U hT d hd
    have hcnotT : c ∉ T.cls := fun hc => hnew c hc hpend.2
    have hcnotA : c ∉ s.A := fun hc => hpend.1 (Or.inl hc)
    have hcnotJ : c ∉ s.J := fun hc => hpend.1 (Or.inr hc)
    have hTA : Disjoint T.cls s.A := by
      apply Finset.disjoint_left.mpr
      intro d hd hdA
      exact hnew d hd (hA d hdA)
    have hTJ : Disjoint T.cls s.J := by
      apply Finset.disjoint_left.mpr
      intro d hd hdJ
      exact hnew d hd (hJ d hdJ)
    have hnewA : Disjoint (audit_owned (T, c)) s.A := by
      simp only [audit_owned, Finset.disjoint_insert_left]
      exact ⟨hcnotA, hTA⟩
    have hnewJ : Disjoint (audit_owned (T, c)) s.J := by
      simp only [audit_owned, Finset.disjoint_insert_left]
      exact ⟨hcnotJ, hTJ⟩
    constructor
    · intro p hp
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact hown.1 p hp
      · exact hcnotT
    constructor
    · intro p hp
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact hown.2.1 p hp
      · exact hnewJ
    · intro p hp q hq hpq
      simp only [List.mem_append, List.mem_singleton] at hp hq
      rcases hp with hp | rfl <;> rcases hq with hq | rfl
      · exact hown.2.2 p hp q hq hpq
      · apply Finset.disjoint_left.mpr
        intro d hdp hdnew
        exact Finset.disjoint_left.mp hnewA hdnew (audit_owned_mem_A Φ x s p hp hdp)
      · apply Finset.disjoint_left.mpr
        intro d hdnew hdq
        exact Finset.disjoint_left.mp hnewA hdnew (audit_owned_mem_A Φ x s q hq hdq)
      · exact (hpq rfl).elim
  · obtain ⟨_, hsuccess | hfail⟩ := hmatch
    · obtain ⟨M', _, _, heq⟩ := hsuccess
      cases heq
      constructor
      · intro p hp
        exact hown.1 p (List.mem_filter.mp hp).1
      constructor
      · intro p hp
        have hp' := (List.mem_filter.mp hp).1
        apply Finset.disjoint_left.mpr
        intro d hd hJ'
        rcases Finset.mem_insert.mp hJ' with rfl | hJ'
        · exact hpend.1 (Or.inl (audit_owned_mem_A Φ x s p hp' hd))
        · exact Finset.disjoint_left.mp (hown.2.1 p hp') hd hJ'
      · intro p hp q hq hpq
        exact hown.2.2 p (List.mem_filter.mp hp).1 q (List.mem_filter.mp hq).1 hpq
    · obtain ⟨_, heq⟩ := hfail
      contradiction

/-- The structural invariants needed for the Repair path argument hold at every
reachable state. -/
theorem audit_reach_path_invariants {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ)
    (h : RepairReach k Φ I0 x (RState.init Φ x W) s j) :
    audit_covered Φ x W s ∧ audit_tree_disjoint Φ x s ∧
    audit_tree_assigned_covered Φ x s ∧ audit_matching_assigned_covered Φ x s ∧
    audit_owned_disjoint Φ x s := by
  have hgen : ∀ s t : RState Φ x, ∀ j, RepairReach k Φ I0 x s t j →
      audit_covered Φ x W s ∧ audit_tree_disjoint Φ x s ∧
      audit_tree_assigned_covered Φ x s ∧ audit_matching_assigned_covered Φ x s ∧
      audit_owned_disjoint Φ x s →
      audit_covered Φ x W t ∧ audit_tree_disjoint Φ x t ∧
      audit_tree_assigned_covered Φ x t ∧ audit_matching_assigned_covered Φ x t ∧
      audit_owned_disjoint Φ x t := by
    intro s t j hreach
    induction hreach with
    | refl s => intro hs; exact hs
    | step s s' t c j hstep hreach ih =>
      intro hs
      have hc := audit_step_preserves_covered k Φ I0 x W s s' c hstep hs.1
      have ht := audit_step_preserves_tree_disjoint k Φ I0 x W s s' c hstep hs.1 hs.2.1
      have ha := audit_step_preserves_tree_assigned_covered k Φ I0 x s s' c hstep hs.2.2.1
      have hj := audit_step_preserves_matching_assigned_covered k Φ I0 x s s' c hstep hs.2.2.2.1
      have ho := audit_step_preserves_owned_disjoint k Φ I0 x s s' c hstep
        hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
      exact ih ⟨hc, ht, ha, hj, ho⟩
  apply hgen _ _ _ h
  refine ⟨audit_initial_covered Φ x W, ?_, ?_, ?_, ?_⟩
  · simp [audit_tree_disjoint, RState.init]
  · simp [audit_tree_assigned_covered, RState.init, RState.A]
  · simp [audit_matching_assigned_covered, RState.init]
  · simp [audit_owned_disjoint, RState.init]

/-- Any clause witness whose output-value literal is true lies in the current
disagreement set when the clause forces a disagreeing variable. -/
theorem audit_force_witness_in_disagreement {n : ℕ} (C : GClause (Fin n))
    (z y : Fin n → Bool) (U : Finset (Fin n))
    (htruth : ∀ v ∈ U, C v = some (y v))
    (v : Fin n) (hv : v ∈ disagree z y) (hforce : Forces z C v) :
    U ⊆ disagree z y := by
  intro u hu
  by_contra hnot
  have hzu : z u = y u := by
    by_contra hne
    exact hnot (by simpa [disagree] using hne)
  have htrue : u ∈ satSet z C := by
    unfold satSet
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [hzu]; exact htruth u hu⟩
  rw [hforce] at htrue
  have huv : u = v := Finset.mem_singleton.mp htrue
  subst u
  exact hnot hv

private noncomputable def audit_clause_witness {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x) (c : Fin Φ.length) : Finset (Fin n) :=
  if c ∈ s.J then s.M c
  else if h : ∃ p ∈ s.F, c ∈ audit_owned p then
    let p := Classical.choose h
    if c = p.2 then {p.1.root} else {p.1.child c}
  else ∅

/-- Every assigned clause has a nonempty witness contained in the tree or
matching variables; a singleton witness belongs to a retained tree. -/
theorem audit_assigned_witness_basic {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x) (hm : IsPairMatching Φ s.J s.M)
    (c : Fin Φ.length) (hc : s.Assigned c) :
    (audit_clause_witness Φ x s c).Nonempty ∧
      ((audit_clause_witness Φ x s c).card = 1 → audit_clause_witness Φ x s c ⊆ s.VF) := by
  by_cases hJ : c ∈ s.J
  · have hw : audit_clause_witness Φ x s c = s.M c := by simp [audit_clause_witness, hJ]
    rw [hw]
    have hcard := (hm.1 c hJ).2
    constructor
    · apply Finset.card_pos.mp
      omega
    · intro h
      omega
  · have hex : ∃ p ∈ s.F, c ∈ audit_owned p := by
      have hA : c ∈ s.A := hc.resolve_right hJ
      obtain ⟨p, hp, hcp⟩ := (audit_mem_A Φ x s c).mp hA
      exact ⟨p, hp, by simpa [audit_owned] using hcp⟩
    let p := Classical.choose hex
    have hp : p ∈ s.F ∧ c ∈ audit_owned p := Classical.choose_spec hex
    by_cases heq : c = p.2
    · have hw : audit_clause_witness Φ x s c = {p.1.root} := by
        unfold audit_clause_witness
        rw [if_neg hJ, dif_pos hex]
        change (if c = p.2 then {p.1.root} else {p.1.child c}) = _
        rw [if_pos heq]
      rw [hw]
      constructor
      · simp
      · intro _ v hv
        have hv' : v = p.1.root := Finset.mem_singleton.mp hv
        subst v
        exact (audit_mem_VF Φ x s p.1.root).mpr ⟨p, hp.1, p.1.root_mem⟩
    · have hcl : c ∈ p.1.cls := by
        have := Finset.mem_insert.mp hp.2
        exact this.resolve_left heq
      have hw : audit_clause_witness Φ x s c = {p.1.child c} := by
        unfold audit_clause_witness
        rw [if_neg hJ, dif_pos hex]
        change (if c = p.2 then {p.1.root} else {p.1.child c}) = _
        rw [if_neg heq]
      rw [hw]
      constructor
      · simp
      · intro _ v hv
        have hv' : v = p.1.child c := Finset.mem_singleton.mp hv
        subst v
        exact (audit_mem_VF Φ x s (p.1.child c)).mpr ⟨p, hp.1, p.1.child_mem c hcl⟩

/-- Every variable in a clause's witness satisfies its literal at the output. -/
theorem audit_assigned_witness_true {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x) (hm : IsPairMatching Φ s.J s.M)
    (hdisj : Disjoint s.VF (matchedVars Φ s.J s.M))
    (hassoc : audit_associations_false Φ x s)
    (c : Fin Φ.length) (hc : s.Assigned c) :
    ∀ v ∈ audit_clause_witness Φ x s c, (Φ.get c) v = some (s.output v) := by
  intro v hv
  by_cases hJ : c ∈ s.J
  · have hw : audit_clause_witness Φ x s c = s.M c := by simp [audit_clause_witness, hJ]
    rw [hw] at hv
    have hvm : v ∈ matchedVars Φ s.J s.M := Finset.mem_biUnion.mpr ⟨c, hJ, hv⟩
    have hvF : v ∉ s.VF := fun h => Finset.disjoint_left.mp hdisj h hvm
    have hvchoice : ∃ d ∈ s.J, v ∈ s.M d := ⟨c, hJ, hv⟩
    have hchosen : Classical.choose hvchoice = c := by
      have hs := Classical.choose_spec hvchoice
      by_contra hne
      exact Finset.disjoint_left.mp (hm.2 _ hs.1 c hJ hne) hs.2 hv
    have hvscope : v ∈ vbl (Φ.get c) := (hm.1 c hJ).1 hv
    cases hval : (Φ.get c) v with
    | none =>
      have hsome : ((Φ.get c) v).isSome := (Finset.mem_filter.mp hvscope).2
      rw [hval] at hsome
      contradiction
    | some b =>
      have hout : s.output v = b := by
        unfold RState.output
        simp only [hvF, ↓reduceIte, dif_pos hvchoice, hchosen, hval, Option.getD_some]
      rw [hout]
  · have hex : ∃ p ∈ s.F, c ∈ audit_owned p := by
      have hA : c ∈ s.A := hc.resolve_right hJ
      obtain ⟨p, hp, hcp⟩ := (audit_mem_A Φ x s c).mp hA
      exact ⟨p, hp, by simpa [audit_owned] using hcp⟩
    let p := Classical.choose hex
    have hp : p ∈ s.F ∧ c ∈ audit_owned p := Classical.choose_spec hex
    by_cases heq : c = p.2
    · have hw : audit_clause_witness Φ x s c = {p.1.root} := by
        unfold audit_clause_witness
        rw [if_neg hJ, dif_pos hex]
        change (if c = p.2 then {p.1.root} else {p.1.child c}) = _
        rw [if_pos heq]
      rw [hw] at hv
      have hv' : v = p.1.root := Finset.mem_singleton.mp hv
      subst v
      have hrF : p.1.root ∈ s.VF := (audit_mem_VF Φ x s _).mpr ⟨p, hp.1, p.1.root_mem⟩
      have hout : s.output p.1.root = !x p.1.root := by simp [RState.output, hrF]
      rw [hout, heq]
      exact hassoc p.1 p.2 hp.1
    · have hcl : c ∈ p.1.cls := by
        have := Finset.mem_insert.mp hp.2
        exact this.resolve_left heq
      have hw : audit_clause_witness Φ x s c = {p.1.child c} := by
        unfold audit_clause_witness
        rw [if_neg hJ, dif_pos hex]
        change (if c = p.2 then {p.1.root} else {p.1.child c}) = _
        rw [if_neg heq]
      rw [hw] at hv
      have hv' : v = p.1.child c := Finset.mem_singleton.mp hv
      subst v
      have hvF : p.1.child c ∈ s.VF := (audit_mem_VF Φ x s _).mpr
        ⟨p, hp.1, p.1.child_mem c hcl⟩
      have hvneq : p.1.child c ≠ p.1.parent c := by
        intro h
        have hd := p.1.depth_child c hcl
        rw [h] at hd
        omega
      have hfalse : p.1.child c ∉ satSet x (Φ.get c) := by
        rw [p.1.forces c hcl]
        simp [hvneq]
      have hlit := audit_false_literal x (Φ.get c) (p.1.child c) (p.1.child_vbl c hcl) hfalse
      have hout : s.output (p.1.child c) = !x (p.1.child c) := by simp [RState.output, hvF]
      rw [hout]
      exact hlit

private noncomputable def audit_tree_witness {n : ℕ} {Φ : GFormula (Fin n)}
    {x : Fin n → Bool} (p : ForcingTree Φ x × Fin Φ.length) (c : Fin Φ.length) : Fin n :=
  if c = p.2 then p.1.root else p.1.child c

private theorem audit_tree_witness_mem {n : ℕ} {Φ : GFormula (Fin n)}
    {x : Fin n → Bool} (p : ForcingTree Φ x × Fin Φ.length) (c : Fin Φ.length)
    (hc : c ∈ audit_owned p) : audit_tree_witness p c ∈ p.1.vars := by
  by_cases heq : c = p.2
  · simp [audit_tree_witness, heq, p.1.root_mem]
  · have hcl : c ∈ p.1.cls := (Finset.mem_insert.mp hc).resolve_left heq
    simp [audit_tree_witness, heq, p.1.child_mem c hcl]

private theorem audit_child_ne_root {n : ℕ} {Φ : GFormula (Fin n)}
    {x : Fin n → Bool} (T : ForcingTree Φ x) (c : Fin Φ.length) (hc : c ∈ T.cls) :
    T.child c ≠ T.root := by
  intro heq
  have hd := T.depth_child c hc
  rw [heq, T.depth_root] at hd
  omega

private theorem audit_tree_witness_inj {n : ℕ} {Φ : GFormula (Fin n)}
    {x : Fin n → Bool} (p : ForcingTree Φ x × Fin Φ.length)
    (howner : p.2 ∉ p.1.cls) (c d : Fin Φ.length)
    (hc : c ∈ audit_owned p) (hd : d ∈ audit_owned p)
    (heq : audit_tree_witness p c = audit_tree_witness p d) : c = d := by
  by_cases hcroot : c = p.2 <;> by_cases hdroot : d = p.2
  · exact hcroot.trans hdroot.symm
  · have hdcl : d ∈ p.1.cls := (Finset.mem_insert.mp hd).resolve_left hdroot
    have he : p.1.root = p.1.child d := by simpa [audit_tree_witness, hcroot, hdroot] using heq
    exact (audit_child_ne_root p.1 d hdcl he.symm).elim
  · have hccl : c ∈ p.1.cls := (Finset.mem_insert.mp hc).resolve_left hcroot
    have he : p.1.child c = p.1.root := by simpa [audit_tree_witness, hcroot, hdroot] using heq
    exact (audit_child_ne_root p.1 c hccl he).elim
  · have hccl : c ∈ p.1.cls := (Finset.mem_insert.mp hc).resolve_left hcroot
    have hdcl : d ∈ p.1.cls := (Finset.mem_insert.mp hd).resolve_left hdroot
    have hchild : p.1.child c = p.1.child d := by simpa [audit_tree_witness, hcroot, hdroot] using heq
    have hu := p.1.unique_parent (p.1.child c) (p.1.child_mem c hccl) (audit_child_ne_root p.1 c hccl)
    exact hu.unique ⟨hccl, rfl⟩ ⟨hdcl, hchild.symm⟩

private theorem audit_witness_tree_decomp {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x) (c : Fin Φ.length)
    (hc : s.Assigned c) (hJ : c ∉ s.J) :
    ∃ p ∈ s.F, c ∈ audit_owned p ∧ audit_clause_witness Φ x s c = {audit_tree_witness p c} := by
  have hA : c ∈ s.A := hc.resolve_right hJ
  obtain ⟨q, hq, hqc⟩ := (audit_mem_A Φ x s c).mp hA
  have hex : ∃ p ∈ s.F, c ∈ audit_owned p := ⟨q, hq, by simpa [audit_owned] using hqc⟩
  let p := Classical.choose hex
  have hp : p ∈ s.F ∧ c ∈ audit_owned p := Classical.choose_spec hex
  refine ⟨p, hp.1, hp.2, ?_⟩
  unfold audit_clause_witness
  rw [if_neg hJ, dif_pos hex]
  change (if c = p.2 then {p.1.root} else {p.1.child c}) = {audit_tree_witness p c}
  by_cases h : c = p.2 <;> simp [audit_tree_witness, h]

/-- Assigned clauses have pairwise disjoint output-satisfying witness sets. -/
theorem audit_assigned_witness_disjoint {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x) (hm : IsPairMatching Φ s.J s.M)
    (hTM : Disjoint s.VF (matchedVars Φ s.J s.M))
    (hTT : audit_tree_disjoint Φ x s) (hown : audit_owned_disjoint Φ x s)
    (c d : Fin Φ.length) (hc : s.Assigned c) (hd : s.Assigned d) (hne : c ≠ d) :
    Disjoint (audit_clause_witness Φ x s c) (audit_clause_witness Φ x s d) := by
  by_cases hcJ : c ∈ s.J <;> by_cases hdJ : d ∈ s.J
  · simpa [audit_clause_witness, hcJ, hdJ] using hm.2 c hcJ d hdJ hne
  · obtain ⟨p, hp, hdp, hwd⟩ := audit_witness_tree_decomp Φ x s d hd hdJ
    have hwc : audit_clause_witness Φ x s c = s.M c := by simp [audit_clause_witness, hcJ]
    rw [hwc, hwd]
    apply Finset.disjoint_left.mpr
    intro v hv hsingle
    have hvp : v ∈ p.1.vars := by
      have heq : v = audit_tree_witness p d := Finset.mem_singleton.mp hsingle
      subst v
      exact audit_tree_witness_mem p d hdp
    have hvF : v ∈ s.VF := (audit_mem_VF Φ x s v).mpr ⟨p, hp, hvp⟩
    have hvM : v ∈ matchedVars Φ s.J s.M := Finset.mem_biUnion.mpr ⟨c, hcJ, hv⟩
    exact Finset.disjoint_left.mp hTM hvF hvM
  · obtain ⟨p, hp, hcp, hwc⟩ := audit_witness_tree_decomp Φ x s c hc hcJ
    have hwd : audit_clause_witness Φ x s d = s.M d := by simp [audit_clause_witness, hdJ]
    rw [hwc, hwd]
    apply Finset.disjoint_left.mpr
    intro v hsingle hv
    have hvp : v ∈ p.1.vars := by
      have heq : v = audit_tree_witness p c := Finset.mem_singleton.mp hsingle
      subst v
      exact audit_tree_witness_mem p c hcp
    have hvF : v ∈ s.VF := (audit_mem_VF Φ x s v).mpr ⟨p, hp, hvp⟩
    have hvM : v ∈ matchedVars Φ s.J s.M := Finset.mem_biUnion.mpr ⟨d, hdJ, hv⟩
    exact Finset.disjoint_left.mp hTM hvF hvM
  · obtain ⟨p, hp, hcp, hwc⟩ := audit_witness_tree_decomp Φ x s c hc hcJ
    obtain ⟨q, hq, hdq, hwd⟩ := audit_witness_tree_decomp Φ x s d hd hdJ
    rw [hwc, hwd]
    apply Finset.disjoint_left.mpr
    intro v hv hw
    have hvc : v = audit_tree_witness p c := Finset.mem_singleton.mp hv
    have hvd : v = audit_tree_witness q d := Finset.mem_singleton.mp hw
    by_cases hpq : p = q
    · subst q
      have he : audit_tree_witness p c = audit_tree_witness p d := hvc.symm.trans hvd
      exact hne (audit_tree_witness_inj p (hown.1 p hp) c d hcp hdq he)
    · have hvp : v ∈ p.1.vars := by rw [hvc]; exact audit_tree_witness_mem p c hcp
      have hvq : v ∈ q.1.vars := by rw [hvd]; exact audit_tree_witness_mem q d hdq
      exact Finset.disjoint_left.mp (hTT p hp q hq hpq) hvp hvq

/-- A terminal unassigned clause cannot force a variable inside U when z agrees
with x outside U. -/
theorem audit_forcing_clause_assigned {n : ℕ} (Φ : GFormula (Fin n))
    (x z : Fin n → Bool) (s : RState Φ x)
    (hdone : ∀ c, ¬ s.Pending c) (hoff : ∀ u, u ∉ s.U → z u = x u)
    (c : Fin Φ.length) (v : Fin n) (hv : v ∈ s.U) (hf : Forces z (Φ.get c) v) :
    s.Assigned c := by
  by_contra hun
  obtain ⟨w, hwout, hwtrue⟩ := audit_unassigned_has_true_outside Φ x s hdone c hun
  have hwsat : w ∈ satSet z (Φ.get c) := by
    unfold satSet
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hoff w hwout]
    exact hwtrue
  rw [hf] at hwsat
  have heq : w = v := Finset.mem_singleton.mp hwsat
  subst w
  exact hwout hv

private theorem audit_subF_subset {n : ℕ} (Φ : GFormula (Fin n))
    (I : Finset (Fin Φ.length)) : ∀ C ∈ subF Φ I, C ∈ Φ := by
  intro C hC
  unfold subF at hC
  obtain ⟨c, _, heq⟩ := List.mem_filterMap.mp hC
  by_cases hc : c ∈ I
  · simp only [hc, ↓reduceIte, Option.some.injEq] at heq
    rw [← heq]
    exact List.get_mem Φ c
  · simp [hc] at heq

private theorem audit_unforced_flip_satisfies_subset {n : ℕ} (Φ Ψ : GFormula (Fin n))
    (hsub : ∀ C ∈ Ψ, C ∈ Φ) (z : Fin n → Bool) (v : Fin n) (hz : FSat z Ψ)
    (hunforced : ∀ c : Fin Φ.length, ¬ Forces z (Φ.get c) v) :
    FSat (flip z v) Ψ := by
  intro C hC
  obtain ⟨c, hc⟩ := List.mem_iff_get.mp (hsub C hC)
  subst C
  obtain ⟨u, hu⟩ := hz _ hC
  by_cases huv : u = v
  · subst u
    have hex : ∃ w, w ≠ v ∧ (Φ.get c) w = some (z w) := by
      by_contra hn
      have hforce : Forces z (Φ.get c) v := by
        unfold Forces
        ext w
        simp only [satSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hw
          by_contra hne
          exact hn ⟨w, hne, hw⟩
        · intro heq
          subst w
          exact hu
      exact hunforced c hforce
    obtain ⟨w, hwne, hw⟩ := hex
    refine ⟨w, ?_⟩
    rw [show flip z v w = z w from Function.update_of_ne hwne _ _]
    exact hw
  · refine ⟨u, ?_⟩
    rw [show flip z v u = z u from Function.update_of_ne huv _ _]
    exact hu

/-- The pigeonhole argument may count all original constraints even when the
current assignment only satisfies a subformula. -/
theorem audit_fewer_forcing_clauses_give_flip_subset {n : ℕ} (Φ Ψ : GFormula (Fin n))
    (hsub : ∀ C ∈ Ψ, C ∈ Φ) (z : Fin n → Bool) (D : Finset (Fin n)) (hz : FSat z Ψ)
    (hcount : ((Finset.univ.filter fun c : Fin Φ.length =>
      ∃ v ∈ D, Forces z (Φ.get c) v).card) < D.card) :
    ∃ v ∈ D, FSat (flip z v) Ψ := by
  classical
  let F : Finset (Fin Φ.length) := Finset.univ.filter fun c =>
    ∃ v ∈ D, Forces z (Φ.get c) v
  have hlen : F.card < D.card := hcount
  by_contra hno
  push Not at hno
  have hforce : ∀ v ∈ D, ∃ c : Fin Φ.length, Forces z (Φ.get c) v := by
    intro v hv
    by_contra hn
    have hu : ∀ c : Fin Φ.length, ¬ Forces z (Φ.get c) v := by simpa using hn
    exact hno v hv (audit_unforced_flip_satisfies_subset Φ Ψ hsub z v hz hu)
  have hcover : D ⊆ F.biUnion (fun c => satSet z (Φ.get c)) := by
    intro v hv
    obtain ⟨c, hc⟩ := hforce v hv
    have hcF : c ∈ F := by
      change c ∈ Finset.univ.filter _
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, v, hv, hc⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨c, hcF, ?_⟩
    rw [hc]
    simp
  have hunion : (F.biUnion (fun c => satSet z (Φ.get c))).card ≤ F.card := by
    calc
      _ ≤ ∑ c ∈ F, (satSet z (Φ.get c)).card := Finset.card_biUnion_le
      _ = F.card := by
        calc
          _ = ∑ _c ∈ F, (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro c hc
            have hc' : ∃ v ∈ D, Forces z (Φ.get c) v := (Finset.mem_filter.mp hc).2
            obtain ⟨v, _, hv⟩ := hc'
            rw [hv]
            simp
          _ = F.card := by simp
  have hc := Finset.card_le_card hcover
  omega

/-- First phase of the Repair path argument, directly for any reachable terminal
state and any subformula: if a disagreement lies outside the retained trees,
there is a legal flip toward the output. -/
theorem audit_repair_first_phase {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ)
    (hreach : RepairReach k Φ I0 x (RState.init Φ x W) s j)
    (hdone : ∀ c, ¬ s.Pending c) (I : Finset (Fin Φ.length))
    (z : Fin n → Bool) (hz : z ∈ sols (subF Φ I))
    (hoff : ∀ u, u ∉ s.U → z u = x u)
    (hout : ∃ v ∈ disagree z s.output, v ∉ s.VF) :
    ∃ v, z v ≠ s.output v ∧ FSat (flip z v) (subF Φ I) := by
  classical
  have hm0 : IsPairMatching Φ (RState.init Φ x W).J (RState.init Φ x W).M := by
    simp [IsPairMatching, RState.init]
  have hc0 := audit_initial_covered Φ x W
  have hd0 : Disjoint (RState.init Φ x W).VF
      (matchedVars Φ (RState.init Φ x W).J (RState.init Φ x W).M) := by
    simp [RState.init, RState.VF, matchedVars]
  obtain ⟨hm, hcover, hTM⟩ := audit_reach_core_invariants k Φ I0 x W _ _ _ hreach hm0 hc0 hd0
  obtain ⟨_, hTT, _, _, hown⟩ := audit_reach_path_invariants k Φ I0 x W s j hreach
  have hassoc := audit_reach_associations k Φ I0 x W s j hreach
  have houtU : ∀ u, u ∉ s.U → s.output u = x u :=
    audit_output_agrees_off_U Φ x s hcover.2.1 hcover.2.2
  have hDU : disagree z s.output ⊆ s.U := by
    intro v hv
    by_contra hnot
    have hne : z v ≠ s.output v := by simpa [disagree] using hv
    exact hne ((hoff v hnot).trans (houtU v hnot).symm)
  let F : Finset (Fin Φ.length) := Finset.univ.filter fun c =>
    ∃ v ∈ disagree z s.output, Forces z (Φ.get c) v
  have hassign : ∀ c ∈ F, s.Assigned c := by
    intro c hc
    have hex : ∃ v ∈ disagree z s.output, Forces z (Φ.get c) v := (Finset.mem_filter.mp hc).2
    obtain ⟨v, hv, hf⟩ := hex
    exact audit_forcing_clause_assigned Φ x z s hdone hoff c v (hDU hv) hf
  have hnon : ∀ c ∈ F, (audit_clause_witness Φ x s c).Nonempty := by
    intro c hc
    exact (audit_assigned_witness_basic Φ x s hm c (hassign c hc)).1
  have hsub : ∀ c ∈ F, audit_clause_witness Φ x s c ⊆ disagree z s.output := by
    intro c hc
    obtain ⟨v, hv, hf⟩ : ∃ v ∈ disagree z s.output, Forces z (Φ.get c) v :=
      (Finset.mem_filter.mp hc).2
    exact audit_force_witness_in_disagreement (Φ.get c) z s.output
      (audit_clause_witness Φ x s c)
      (audit_assigned_witness_true Φ x s hm hTM hassoc c (hassign c hc)) v hv hf
  have hpair : (↑F : Set (Fin Φ.length)).PairwiseDisjoint (audit_clause_witness Φ x s) := by
    intro c hc d hd hne
    exact audit_assigned_witness_disjoint Φ x s hm hTM hTT hown c d (hassign c hc) (hassign d hd) hne
  have hone : ∀ c ∈ F, (audit_clause_witness Φ x s c).card = 1 →
      audit_clause_witness Φ x s c ⊆ s.VF := by
    intro c hc
    exact (audit_assigned_witness_basic Φ x s hm c (hassign c hc)).2
  have hcount : F.card < (disagree z s.output).card :=
    audit_disjoint_witness_count F (disagree z s.output) s.VF
      (audit_clause_witness Φ x s) hnon hsub hpair hone hout
  have hsat : FSat z (subF Φ I) := by simpa [sols] using hz
  obtain ⟨v, hv, hflip⟩ := audit_fewer_forcing_clauses_give_flip_subset Φ (subF Φ I)
    (audit_subF_subset Φ I) z (disagree z s.output) hsat hcount
  exact ⟨v, by simpa [disagree] using hv, hflip⟩

private def audit_association_order {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x) : Prop :=
  s.F.Pairwise (fun p q => Disjoint (satSet x (Φ.get p.2)) q.1.vars) ∧
    ∀ p ∈ s.F, Disjoint (satSet x (Φ.get p.2)) p.1.vars

/-- Earlier associated clauses have no x-true literal in later trees, and a
tree's own associated clause has no x-true literal in that tree. -/
theorem audit_step_preserves_association_order {n : ℕ} (k : ℕ)
    (Φ : GFormula (Fin n)) (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool)
    (s s' : RState Φ x) (c : Fin Φ.length)
    (hstep : RStep k Φ I0 x s c (some s'))
    (hA : audit_tree_assigned_covered Φ x s)
    (hord : audit_association_order Φ x s) : audit_association_order Φ x s' := by
  obtain ⟨hpend, htree | hmatch⟩ := hstep
  · obtain ⟨T, _, _, hT, heq⟩ := htree
    cases heq
    constructor
    · apply List.pairwise_append.mpr
      refine ⟨hord.1, by simp, ?_⟩
      intro p hp q hq
      simp only [List.mem_singleton] at hq
      subst q
      apply Finset.disjoint_left.mpr
      intro v hvp hvT
      have hpA : p.2 ∈ s.A := audit_owned_mem_A Φ x s p hp (by simp [audit_owned])
      exact Finset.disjoint_left.mp hT hvT (hA p.2 hpA hvp)
    · intro p hp
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact hord.2 p hp
      · apply Finset.disjoint_left.mpr
        intro v hvc hvT
        exact Finset.disjoint_left.mp hT hvT (hpend.2 hvc)
  · obtain ⟨_, hsuccess | hfail⟩ := hmatch
    · obtain ⟨M', _, _, heq⟩ := hsuccess
      cases heq
      constructor
      · exact List.Pairwise.filter _ hord.1
      · intro p hp
        exact hord.2 p (List.mem_filter.mp hp).1
    · obtain ⟨_, heq⟩ := hfail
      contradiction

/-- The association-order invariant holds in every reachable Repair state. -/
theorem audit_reach_association_order {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ)
    (h : RepairReach k Φ I0 x (RState.init Φ x W) s j) :
    audit_association_order Φ x s := by
  have hgen : ∀ s t : RState Φ x, ∀ j, RepairReach k Φ I0 x s t j →
      audit_tree_assigned_covered Φ x s → audit_association_order Φ x s →
      audit_association_order Φ x t := by
    intro s t j hreach
    induction hreach with
    | refl s => intro _ ho; exact ho
    | step s s' t c j hstep hreach ih =>
      intro ha ho
      exact ih (audit_step_preserves_tree_assigned_covered k Φ I0 x s s' c hstep ha)
        (audit_step_preserves_association_order k Φ I0 x s s' c hstep ha ho)
  apply hgen _ _ _ h
  · simp [audit_tree_assigned_covered, RState.init, RState.A]
  · simp [audit_association_order, RState.init]

/-- Choose a deepest disagreement in the last retained tree containing one. -/
theorem audit_choose_last_deepest {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x) (D : Finset (Fin n))
    (hD : D.Nonempty) (hsub : D ⊆ s.VF) :
    ∃ (i : Fin s.F.length) (v : Fin n), v ∈ D ∧ v ∈ (s.F.get i).1.vars ∧
      (∀ j : Fin s.F.length, i < j → Disjoint D (s.F.get j).1.vars) ∧
      (∀ w ∈ D, w ∈ (s.F.get i).1.vars → (s.F.get i).1.depth w ≤ (s.F.get i).1.depth v) := by
  classical
  let I : Finset (Fin s.F.length) := Finset.univ.filter fun i =>
    ∃ v ∈ D, v ∈ (s.F.get i).1.vars
  have hInon : I.Nonempty := by
    obtain ⟨v, hv⟩ := hD
    have hvF := hsub hv
    obtain ⟨p, hp, hvp⟩ := (audit_mem_VF Φ x s v).mp hvF
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
    refine ⟨i, ?_⟩
    change i ∈ Finset.univ.filter _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, v, hv, by rw [hi]; exact hvp⟩
  obtain ⟨i, hiI, himax⟩ := I.exists_max_image (fun i => i.val) hInon
  have hex : ∃ v ∈ D, v ∈ (s.F.get i).1.vars := (Finset.mem_filter.mp hiI).2
  let P := D ∩ (s.F.get i).1.vars
  have hPnon : P.Nonempty := by
    obtain ⟨v, hvD, hvP⟩ := hex
    exact ⟨v, Finset.mem_inter.mpr ⟨hvD, hvP⟩⟩
  obtain ⟨v, hvP, hvmax⟩ := P.exists_max_image (s.F.get i).1.depth hPnon
  obtain ⟨hvD, hvTree⟩ := Finset.mem_inter.mp hvP
  refine ⟨i, v, hvD, hvTree, ?_, ?_⟩
  · intro j hij
    apply Finset.disjoint_left.mpr
    intro w hwD hwT
    have hjI : j ∈ I := by
      change j ∈ Finset.univ.filter _
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, w, hwD, hwT⟩
    have hle := himax j hjI
    exact (not_le_of_gt hij) hle
  · intro w hwD hwT
    exact hvmax w (Finset.mem_inter.mpr ⟨hwD, hwT⟩)

/-- In the all-tree phase, the deepest disagreement of the last affected tree
is unforced by every original constraint. -/
theorem audit_repair_second_phase_unforced {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ)
    (hreach : RepairReach k Φ I0 x (RState.init Φ x W) s j)
    (hdone : ∀ c, ¬ s.Pending c) (z : Fin n → Bool)
    (hoff : ∀ u, u ∉ s.U → z u = x u)
    (hsub : disagree z s.output ⊆ s.VF)
    (i : Fin s.F.length) (v : Fin n)
    (hvD : v ∈ disagree z s.output) (hvT : v ∈ (s.F.get i).1.vars)
    (hlater : ∀ j : Fin s.F.length, i < j → Disjoint (disagree z s.output) (s.F.get j).1.vars)
    (hdeep : ∀ w ∈ disagree z s.output, w ∈ (s.F.get i).1.vars →
      (s.F.get i).1.depth w ≤ (s.F.get i).1.depth v) :
    ∀ c : Fin Φ.length, ¬ Forces z (Φ.get c) v := by
  classical
  have hm0 : IsPairMatching Φ (RState.init Φ x W).J (RState.init Φ x W).M := by
    simp [IsPairMatching, RState.init]
  have hc0 := audit_initial_covered Φ x W
  have hd0 : Disjoint (RState.init Φ x W).VF
      (matchedVars Φ (RState.init Φ x W).J (RState.init Φ x W).M) := by
    simp [RState.init, RState.VF, matchedVars]
  obtain ⟨hm, hcover, hTM⟩ := audit_reach_core_invariants k Φ I0 x W _ _ _ hreach hm0 hc0 hd0
  obtain ⟨_, hTT, _, _, hown⟩ := audit_reach_path_invariants k Φ I0 x W s j hreach
  have hassoc := audit_reach_associations k Φ I0 x W s j hreach
  have horder := audit_reach_association_order k Φ I0 x W s j hreach
  have hoffy : ∀ u, u ∉ s.U → s.output u = x u :=
    audit_output_agrees_off_U Φ x s hcover.2.1 hcover.2.2
  have hDU : disagree z s.output ⊆ s.U := by
    intro u hu
    by_contra hout
    have hne : z u ≠ s.output u := by simpa [disagree] using hu
    exact hne ((hoff u hout).trans (hoffy u hout).symm)
  have hvF : v ∈ s.VF := hsub hvD
  have hyv : s.output v = !x v := by simp [RState.output, hvF]
  have hvneq : z v ≠ s.output v := by simpa [disagree] using hvD
  have hvx : z v = x v := by
    rw [hyv] at hvneq
    cases hz : z v <;> cases hx : x v <;> simp_all
  intro c hf
  have hc : s.Assigned c := audit_forcing_clause_assigned Φ x z s hdone hoff c v (hDU hvD) hf
  have hwitness := audit_assigned_witness_basic Φ x s hm c hc
  have htrue := audit_assigned_witness_true Φ x s hm hTM hassoc c hc
  have hwD : audit_clause_witness Φ x s c ⊆ disagree z s.output :=
    audit_force_witness_in_disagreement (Φ.get c) z s.output _ htrue v hvD hf
  have hvSatX : v ∈ satSet x (Φ.get c) := by
    have hvSatZ : v ∈ satSet z (Φ.get c) := by rw [hf]; simp
    unfold satSet at hvSatZ ⊢
    rw [Finset.mem_filter] at hvSatZ ⊢
    exact ⟨Finset.mem_univ _, by simpa [hvx] using hvSatZ.2⟩
  by_cases hcJ : c ∈ s.J
  · have hw : audit_clause_witness Φ x s c = s.M c := by simp [audit_clause_witness, hcJ]
    obtain ⟨u, hu⟩ := hwitness.1
    have huD := hwD hu
    have huF := hsub huD
    have huM : u ∈ matchedVars Φ s.J s.M := by
      apply Finset.mem_biUnion.mpr
      refine ⟨c, hcJ, ?_⟩
      simpa [hw] using hu
    exact Finset.disjoint_left.mp hTM huF huM
  · obtain ⟨q, hq, hcq, hw⟩ := audit_witness_tree_decomp Φ x s c hc hcJ
    obtain ⟨t, ht⟩ := List.mem_iff_get.mp hq
    subst q
    have hcOwned : c ∈ audit_owned (s.F.get t) := hcq
    have hW : audit_clause_witness Φ x s c = {audit_tree_witness (s.F.get t) c} := hw
    have huD : audit_tree_witness (s.F.get t) c ∈ disagree z s.output := by
      apply hwD
      rw [hW]
      simp
    have huT : audit_tree_witness (s.F.get t) c ∈ (s.F.get t).1.vars :=
      audit_tree_witness_mem (s.F.get t) c hcOwned
    by_cases hti : i < t
    · exact Finset.disjoint_left.mp (hlater t hti) huD huT
    · have hle : t ≤ i := le_of_not_gt hti
      by_cases hca : c = (s.F.get t).2
      · have hdis : Disjoint (satSet x (Φ.get c)) (s.F.get i).1.vars := by
          rcases lt_or_eq_of_le hle with hlt | heq
          · have hh := horder.1.rel_get_of_lt hlt
            simpa [hca] using hh
          · subst t
            have hh := horder.2 (s.F.get i) (List.get_mem s.F i)
            simpa [hca] using hh
        exact Finset.disjoint_left.mp hdis hvSatX hvT
      · have hcTree : c ∈ (s.F.get t).1.cls := (Finset.mem_insert.mp hcOwned).resolve_left hca
        have hparent : v = (s.F.get t).1.parent c := by
          rw [(s.F.get t).1.forces c hcTree] at hvSatX
          exact Finset.mem_singleton.mp hvSatX
        by_cases hsame : s.F.get t = s.F.get i
        · have hchildD : (s.F.get i).1.child c ∈ disagree z s.output := by
            have : audit_tree_witness (s.F.get t) c = (s.F.get t).1.child c := by
              unfold audit_tree_witness
              rw [if_neg hca]
            rw [this, hsame] at huD
            exact huD
          have hcTree' : c ∈ (s.F.get i).1.cls := by rw [← hsame]; exact hcTree
          have hchildT := (s.F.get i).1.child_mem c hcTree'
          have hdepth := (s.F.get i).1.depth_child c hcTree'
          have hparent' : v = (s.F.get i).1.parent c := by rw [← hsame]; exact hparent
          rw [← hparent'] at hdepth
          have hledepth := hdeep _ hchildD hchildT
          omega
        · have hvOther : v ∈ (s.F.get t).1.vars := by
            rw [hparent]
            exact (s.F.get t).1.parent_mem c hcTree
          have hd := hTT (s.F.get i) (List.get_mem s.F i)
            (s.F.get t) (List.get_mem s.F t) (Ne.symm hsame)
          exact Finset.disjoint_left.mp hd hvT hvOther

/-- At a reachable terminal state, every compatible non-target solution of a
subformula has a satisfying flip toward the output. -/
theorem audit_repair_terminal_progress {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ)
    (hreach : RepairReach k Φ I0 x (RState.init Φ x W) s j)
    (hdone : ∀ c, ¬ s.Pending c) (I : Finset (Fin Φ.length))
    (z : Fin n → Bool) (hz : z ∈ sols (subF Φ I))
    (hoff : ∀ u, u ∉ s.U → z u = x u) (hne : z ≠ s.output) :
    ∃ v, z v ≠ s.output v ∧ FSat (flip z v) (subF Φ I) := by
  classical
  by_cases hsub : disagree z s.output ⊆ s.VF
  · have hD : (disagree z s.output).Nonempty := by
      by_contra hnone
      apply hne
      funext v
      by_contra hv
      exact hnone ⟨v, by simpa [disagree] using hv⟩
    obtain ⟨i, v, hvD, hvT, hlater, hdeep⟩ := audit_choose_last_deepest Φ x s _ hD hsub
    have hunforced := audit_repair_second_phase_unforced k Φ I0 x W s j hreach hdone z hoff hsub
      i v hvD hvT hlater hdeep
    have hz' : FSat z (subF Φ I) := by simpa [sols] using hz
    have hflip := audit_unforced_flip_satisfies_subset Φ (subF Φ I)
      (audit_subF_subset Φ I) z v hz' hunforced
    exact ⟨v, by simpa [disagree] using hvD, hflip⟩
  · have hout : ∃ v ∈ disagree z s.output, v ∉ s.VF := Finset.not_subset.mp hsub
    exact audit_repair_first_phase k Φ I0 x W s j hreach hdone I z hz hoff hout

/-- Every reachable terminal state satisfies the full repair specification. -/
theorem audit_reached_terminal_isRepair {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ)
    (hreach : RepairReach k Φ I0 x (RState.init Φ x W) s j)
    (hdone : ∀ c, ¬ s.Pending c) : IsRepair Φ x W s.U s.output := by
  have hm0 : IsPairMatching Φ (RState.init Φ x W).J (RState.init Φ x W).M := by
    simp [IsPairMatching, RState.init]
  have hc0 := audit_initial_covered Φ x W
  have hd0 : Disjoint (RState.init Φ x W).VF
      (matchedVars Φ (RState.init Φ x W).J (RState.init Φ x W).M) := by
    simp [RState.init, RState.VF, matchedVars]
  obtain ⟨_, hcover, _⟩ := audit_reach_core_invariants k Φ I0 x W _ _ _ hreach hm0 hc0 hd0
  have hoff : ∀ u, u ∉ s.U → s.output u = x u :=
    audit_output_agrees_off_U Φ x s hcover.2.1 hcover.2.2
  refine ⟨hcover.1, audit_reached_terminal_satisfies k Φ I0 x W s j hreach hdone, hoff, ?_⟩
  intro I z hz hzoff
  exact audit_path_of_progress (subF Φ I) x s.output s.U hoff
    (audit_repair_terminal_progress k Φ I0 x W s j hreach hdone I) z hz hzoff

/-- A completed Repair run either fails or returns an (x,W)-repair. -/
theorem audit_repair_run_correct {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (r : Option (Finset (Fin n) × (Fin n → Bool))) (i : ℕ)
    (hrun : RepairRun k Φ I0 x (RState.init Φ x W) r i) :
    r = none ∨ ∃ U y, r = some (U, y) ∧ IsRepair Φ x W U y := by
  cases r with
  | none => exact Or.inl rfl
  | some p =>
    rcases p with ⟨U, y⟩
    right
    obtain ⟨t, j, hreach, hU, hy, hdone⟩ :=
      audit_success_terminal_state k Φ I0 x _ _ i hrun U y rfl
    refine ⟨U, y, rfl, ?_⟩
    have hrepair := audit_reached_terminal_isRepair k Φ I0 x W t j hreach hdone
    rw [hU, hy] at hrepair
    exact hrepair

end KSATSingleFlip.Connect



open scoped Classical BigOperators

namespace KSATSingleFlip.Connect

/-- A matching update that adds at most two variables can discard at most two
pairwise-disjoint trees, if all trees avoided the old matched set. -/
theorem audit_discarded_tree_count {α V : Type} [DecidableEq α] [DecidableEq V]
    (S : Finset α) (T : α → Finset V) (B X : Finset V)
    (hpair : (↑S : Set α).PairwiseDisjoint T)
    (hold : ∀ a ∈ S, Disjoint (T a) B) :
    (S.filter fun a => ¬ Disjoint (T a) X).card ≤ (X \ B).card := by
  classical
  let D := S.filter fun a => ¬ Disjoint (T a) X
  have hw : ∀ a : ↥D, ∃ v, v ∈ T a.1 ∧ v ∈ X \ B := by
    intro a
    have ha : a.1 ∈ S ∧ ¬ Disjoint (T a.1) X := Finset.mem_filter.mp a.2
    obtain ⟨v, hv⟩ := Finset.not_disjoint_iff_nonempty_inter.mp ha.2
    obtain ⟨hvT, hvX⟩ := Finset.mem_inter.mp hv
    exact ⟨v, hvT, Finset.mem_sdiff.mpr ⟨hvX, Finset.disjoint_left.mp (hold a.1 ha.1) hvT⟩⟩
  let f : ↥D → ↥(X \ B) := fun a => ⟨Classical.choose (hw a), (Classical.choose_spec (hw a)).2⟩
  have hinj : Function.Injective f := by
    intro a b heq
    apply Subtype.ext
    by_contra hne
    have ha : a.1 ∈ S := (Finset.mem_filter.mp a.2).1
    have hb : b.1 ∈ S := (Finset.mem_filter.mp b.2).1
    have hd := hpair ha hb hne
    have hva := (Classical.choose_spec (hw a)).1
    have hvb := (Classical.choose_spec (hw b)).1
    have he : Classical.choose (hw a) = Classical.choose (hw b) := congrArg Subtype.val heq
    rw [he] at hva
    exact Finset.disjoint_left.mp hd hva hvb
  have h := Fintype.card_le_of_injective f hinj
  simpa [D] using h

/-- The variables in discarded trees occupy at most the number of new matched
variables times the per-tree size bound. -/
theorem audit_discarded_tree_vars {α V : Type} [DecidableEq α] [DecidableEq V]
    (S : Finset α) (T : α → Finset V) (B X : Finset V) (L : ℕ)
    (hpair : (↑S : Set α).PairwiseDisjoint T)
    (hold : ∀ a ∈ S, Disjoint (T a) B)
    (hsize : ∀ a ∈ S, (T a).card ≤ L) :
    ((S.filter fun a => ¬ Disjoint (T a) X).biUnion T).card ≤ (X \ B).card * L := by
  classical
  let D := S.filter fun a => ¬ Disjoint (T a) X
  have hd : D.card ≤ (X \ B).card := audit_discarded_tree_count S T B X hpair hold
  calc
    (D.biUnion T).card ≤ ∑ a ∈ D, (T a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ D, L := Finset.sum_le_sum (fun a ha => hsize a (Finset.mem_filter.mp ha).1)
    _ = D.card * L := by simp
    _ ≤ (X \ B).card * L := Nat.mul_le_mul_right L hd

end KSATSingleFlip.Connect


open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- Every retained tree was introduced as a small tree. -/
theorem audit_reach_tree_small {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ)
    (h : RepairReach k Φ I0 x (RState.init Φ x W) s j) :
    ∀ p ∈ s.F, IsSmallTree k Φ I0 x p.1 := by
  have hg : ∀ s t : RState Φ x, ∀ j, RepairReach k Φ I0 x s t j →
      (∀ p ∈ s.F, IsSmallTree k Φ I0 x p.1) →
      (∀ p ∈ t.F, IsSmallTree k Φ I0 x p.1) := by
    intro s t j hr
    induction hr with
    | refl s => intro hs; exact hs
    | step s s' t c j hs hr ih =>
      intro old
      apply ih
      obtain ⟨_, ht | hm⟩ := hs
      · obtain ⟨T, hsmall, _, _, heq⟩ := ht
        cases heq
        intro p hp
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact old p hp
        · exact hsmall
      · obtain ⟨_, hm | hf⟩ := hm
        · obtain ⟨M', _, _, heq⟩ := hm
          cases heq
          intro p hp
          exact old p (List.mem_filter.mp hp).1
        · obtain ⟨_, heq⟩ := hf
          contradiction
  apply hg _ _ _ h
  simp [RState.init]

/-- A successful matching augmentation adds exactly two matched variables. -/
theorem audit_match_new_vars {n : ℕ} (Φ : GFormula (Fin n))
    (J : Finset (Fin Φ.length)) (M M' : Fin Φ.length → Finset (Fin n))
    (c : Fin Φ.length) (hc : c ∉ J) (hm : IsPairMatching Φ J M)
    (hm' : IsPairMatching Φ (insert c J) M')
    (hsub : matchedVars Φ J M ⊆ matchedVars Φ (insert c J) M') :
    (matchedVars Φ (insert c J) M' \ matchedVars Φ J M).card = 2 := by
  have h := Finset.card_sdiff_of_subset hsub
  rw [audit_pair_matching_card Φ (insert c J) M' hm', audit_pair_matching_card Φ J M hm,
    Finset.card_insert_of_notMem hc] at h
  omega

/-- Each matching augmentation discards tree variables in at most two small trees. -/
theorem audit_reach_discarded_tree_vars {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ)
    (h : RepairReach k Φ I0 x (RState.init Φ x W) s j)
    (c : Fin Φ.length) (M' : Fin Φ.length → Finset (Fin n))
    (hc : c ∉ s.J) (hm' : IsPairMatching Φ (insert c s.J) M')
    (hsub : matchedVars Φ s.J s.M ⊆ matchedVars Φ (insert c s.J) M') :
    ((s.F.toFinset.filter fun p => ¬ Disjoint p.1.vars (matchedVars Φ (insert c s.J) M')).biUnion
      (fun p => p.1.vars)).card ≤ 2 * ⌊Real.log k ^ 6⌋₊ := by
  have hm : IsPairMatching Φ (RState.init Φ x W).J (RState.init Φ x W).M := by
    simp [IsPairMatching, RState.init]
  have hd : Disjoint (RState.init Φ x W).VF
      (matchedVars Φ (RState.init Φ x W).J (RState.init Φ x W).M) := by
    simp [RState.init, RState.VF, matchedVars]
  obtain ⟨hm, _, hd⟩ := audit_reach_core_invariants k Φ I0 x W _ _ _ h hm
    (audit_initial_covered Φ x W) hd
  have hinv := audit_reach_path_invariants k Φ I0 x W s j h
  have hp : (↑s.F.toFinset : Set (ForcingTree Φ x × Fin Φ.length)).PairwiseDisjoint (fun p => p.1.vars) := by
    intro p hp q hq hpq
    exact hinv.2.1 p (List.mem_toFinset.mp hp) q (List.mem_toFinset.mp hq) hpq
  have hold : ∀ p ∈ s.F.toFinset, Disjoint p.1.vars (matchedVars Φ s.J s.M) := by
    intro p hp
    exact hd.mono_left (audit_tree_vars_in_VF Φ x s p.1 p.2 (List.mem_toFinset.mp hp))
  have hsize : ∀ p ∈ s.F.toFinset, p.1.vars.card ≤ ⌊Real.log k ^ 6⌋₊ := by
    intro p hp
    apply Nat.le_floor
    exact (audit_reach_tree_small k Φ I0 x W s j h p (List.mem_toFinset.mp hp)).2
  have hcount := audit_discarded_tree_vars s.F.toFinset (fun p => p.1.vars)
    (matchedVars Φ s.J s.M) (matchedVars Φ (insert c s.J) M') ⌊Real.log k ^ 6⌋₊ hp hold hsize
  rw [audit_match_new_vars Φ s.J s.M M' c hc hm hm' hsub] at hcount
  exact hcount

end KSATSingleFlip.Connect


open scoped Classical BigOperators
namespace KSATSingleFlip.Connect

/-- One matching update grows the part of U outside retained trees by at most
its two new matched variables and the variables of at most two removed trees. -/
theorem audit_match_outside_growth {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ)
    (h : RepairReach k Φ I0 x (RState.init Φ x W) s j)
    (c : Fin Φ.length) (M' : Fin Φ.length → Finset (Fin n))
    (hc : c ∉ s.J) (hm' : IsPairMatching Φ (insert c s.J) M')
    (hsub : matchedVars Φ s.J s.M ⊆ matchedVars Φ (insert c s.J) M') :
    let t : RState Φ x := ⟨s.U ∪ matchedVars Φ (insert c s.J) M',
      s.F.filter (fun p => Disjoint p.1.vars (matchedVars Φ (insert c s.J) M')),
      insert c s.J, M'⟩
    (t.U \ t.VF).card ≤ (s.U \ s.VF).card + 2 + 2 * ⌊Real.log k ^ 6⌋₊ := by
  let X := matchedVars Φ (insert c s.J) M'
  let B := matchedVars Φ s.J s.M
  let D := (s.F.toFinset.filter fun p => ¬ Disjoint p.1.vars X).biUnion (fun p => p.1.vars)
  let t : RState Φ x := ⟨s.U ∪ X, s.F.filter (fun p => Disjoint p.1.vars X), insert c s.J, M'⟩
  change (t.U \ t.VF).card ≤ (s.U \ s.VF).card + 2 + 2 * ⌊Real.log k ^ 6⌋₊
  have hm : IsPairMatching Φ (RState.init Φ x W).J (RState.init Φ x W).M := by
    simp [IsPairMatching, RState.init]
  have hd : Disjoint (RState.init Φ x W).VF
      (matchedVars Φ (RState.init Φ x W).J (RState.init Φ x W).M) := by
    simp [RState.init, RState.VF, matchedVars]
  obtain ⟨hm, hcvr, hd⟩ := audit_reach_core_invariants k Φ I0 x W _ _ _ h hm
    (audit_initial_covered Φ x W) hd
  have hXcard : (X \ B).card = 2 := audit_match_new_vars Φ s.J s.M M' c hc hm hm' hsub
  have hDcard : D.card ≤ 2 * ⌊Real.log k ^ 6⌋₊ :=
    audit_reach_discarded_tree_vars k Φ I0 x W s j h c M' hc hm' hsub
  have hsubset : t.U \ t.VF ⊆ (s.U \ s.VF) ∪ (X \ B) ∪ D := by
    intro v hv
    obtain ⟨hvU, hvnot⟩ := Finset.mem_sdiff.mp hv
    change v ∈ s.U ∪ X at hvU
    by_cases hvR : v ∈ s.U \ s.VF
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hvR)
    · by_cases hvX : v ∈ X \ B
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvX)
      · have hvUold : v ∈ s.U := by
          rcases Finset.mem_union.mp hvU with hvUold | hvX'
          · exact hvUold
          · have hvB : v ∈ B := by
              by_contra hnotB
              exact hvX (Finset.mem_sdiff.mpr ⟨hvX', hnotB⟩)
            exact hcvr.2.2 hvB
        have hvF : v ∈ s.VF := by
          by_contra hnotF
          exact hvR (Finset.mem_sdiff.mpr ⟨hvUold, hnotF⟩)
        obtain ⟨p, hp, hvp⟩ := (audit_mem_VF Φ x s v).mp hvF
        have hpD : ¬ Disjoint p.1.vars X := by
          intro hdisj
          apply hvnot
          apply (audit_mem_VF Φ x t v).mpr
          exact ⟨p, List.mem_filter.mpr ⟨hp, by simpa [t] using hdisj⟩, hvp⟩
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        exact ⟨p, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hp, hpD⟩, hvp⟩
  have hc1 := Finset.card_le_card hsubset
  have hc2 := Finset.card_union_le ((s.U \ s.VF) ∪ (X \ B)) D
  have hc3 := Finset.card_union_le (s.U \ s.VF) (X \ B)
  omega

/-- Tree insertion does not enlarge the variables outside retained trees. -/
theorem audit_tree_outside_growth {n : ℕ} (Φ : GFormula (Fin n))
    (x : Fin n → Bool) (s : RState Φ x) (T : ForcingTree Φ x) (c : Fin Φ.length) :
    let t : RState Φ x := ⟨s.U ∪ T.vars, s.F ++ [(T, c)], s.J, s.M⟩
    (t.U \ t.VF).card ≤ (s.U \ s.VF).card := by
  let t : RState Φ x := ⟨s.U ∪ T.vars, s.F ++ [(T, c)], s.J, s.M⟩
  change (t.U \ t.VF).card ≤ (s.U \ s.VF).card
  apply Finset.card_le_card
  intro v hv
  obtain ⟨hvU, hvnot⟩ := Finset.mem_sdiff.mp hv
  apply Finset.mem_sdiff.mpr
  constructor
  · change v ∈ s.U ∪ T.vars at hvU
    rcases Finset.mem_union.mp hvU with hvU | hvT
    · exact hvU
    · exfalso
      apply hvnot
      exact (audit_mem_VF Φ x t v).mpr ⟨(T, c), by simp [t], hvT⟩
  · intro hvF
    apply hvnot
    obtain ⟨p, hp, hvp⟩ := (audit_mem_VF Φ x s v).mp hvF
    exact (audit_mem_VF Φ x t v).mpr ⟨p, by simp [t, hp], hvp⟩

/-- Reachability is closed under appending a successful step. -/
theorem audit_reach_snoc {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (s t u : RState Φ x)
    (j : ℕ) (h : RepairReach k Φ I0 x s t j) (c : Fin Φ.length)
    (hs : RStep k Φ I0 x t c (some u)) :
    RepairReach k Φ I0 x s u (j + 1) := by
  induction h with
  | refl s => simpa using RepairReach.step s u u c 0 hs (RepairReach.refl u)
  | step s s' t d j hstep hreach ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      RepairReach.step s s' u d (j + 1) hstep (ih hs)

/-- At every reached state, variables outside retained trees are bounded by the
initial set plus the loss from the matching updates. -/
theorem audit_reach_outside_bound {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ)
    (h : RepairReach k Φ I0 x (RState.init Φ x W) s j) :
    (s.U \ s.VF).card ≤ W.card + (2 + 2 * ⌊Real.log k ^ 6⌋₊) * s.J.card := by
  let L := 2 + 2 * ⌊Real.log k ^ 6⌋₊
  have hg : ∀ s t : RState Φ x, ∀ i,
      RepairReach k Φ I0 x s t i →
      ∀ j, RepairReach k Φ I0 x (RState.init Φ x W) s j →
      (s.U \ s.VF).card ≤ W.card + L * s.J.card →
      (t.U \ t.VF).card ≤ W.card + L * t.J.card := by
    intro s t i hreach
    induction hreach with
    | refl s => intro j hp hb; exact hb
    | step s s' t c i hs hr ih =>
      intro j hp hb
      apply ih (j + 1) (audit_reach_snoc k Φ I0 x _ _ _ j hp c hs)
      obtain ⟨hpend, htree | hmatch⟩ := hs
      · obtain ⟨T, _, _, _, heq⟩ := htree
        cases heq
        have hbound := audit_tree_outside_growth Φ x s T c
        exact hbound.trans hb
      · obtain ⟨_, hsuccess | hfail⟩ := hmatch
        · obtain ⟨M', hm', hsub, heq⟩ := hsuccess
          have hc : c ∉ s.J := by intro hc; exact hpend.1 (Or.inr hc)
          have hbound := audit_match_outside_growth k Φ I0 x W s j hp c M' hc hm' hsub
          cases heq
          simp only [Finset.card_insert_of_notMem hc]
          dsimp only at hbound
          dsimp [L] at hb ⊢
          nlinarith
        · obtain ⟨_, heq⟩ := hfail
          contradiction
  apply hg _ _ _ h 0 (RepairReach.refl _)
  simp [RState.init, RState.VF, L]

/-- The source's bound on variables outside retained trees, for log(k) ≥ 1. -/
theorem audit_reach_outside_bound_real {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ) (hlog : 1 ≤ Real.log k)
    (h : RepairReach k Φ I0 x (RState.init Φ x W) s j) :
    ((s.U \ s.VF).card : ℝ) ≤ W.card + 4 * Real.log k ^ 6 * s.J.card := by
  have hpow : 1 ≤ Real.log k ^ 6 := one_le_pow₀ hlog
  have hfloor : (⌊Real.log k ^ 6⌋₊ : ℝ) ≤ Real.log k ^ 6 := Nat.floor_le (by positivity)
  have hnat := audit_reach_outside_bound k Φ I0 x W s j h
  have hreal : ((s.U \ s.VF).card : ℝ) ≤ W.card +
      (2 + 2 * (⌊Real.log k ^ 6⌋₊ : ℝ)) * s.J.card := by exact_mod_cast hnat
  have hJ : (0 : ℝ) ≤ s.J.card := Nat.cast_nonneg _
  nlinarith

end KSATSingleFlip.Connect

open KSATSingleFlip.Connect

/-- The variables outside retained trees are controlled by the initial set and matching clauses. -/
theorem solution {n : ℕ} (k : ℕ) (Φ : GFormula (Fin n))
    (I0 : Finset (Fin Φ.length)) (x : Fin n → Bool) (W : Finset (Fin n))
    (s : RState Φ x) (j : ℕ) (hlog : 1 ≤ Real.log k)
    (h : RepairReach k Φ I0 x (RState.init Φ x W) s j) :
    ((s.U \ s.VF).card : ℝ) ≤ W.card + 4 * Real.log k ^ 6 * s.J.card := by
  exact audit_reach_outside_bound_real k Φ I0 x W s j hlog h

#print axioms solution
