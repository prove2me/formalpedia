-- Prove2me | solution 1 for NonsmoothLojasiewicz.Continuous.subanalytic_compl
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T06:13:41.224241+00:00
-- url     : https://prove2.me/submissions/4aec0499-4315-4bee-826f-a8a55ce05297

import Mathlib
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic
import Theorems.Thm_NonsmoothLojasiewicz_Continuous_tarski_seidenberg_parametric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! SubanalyticLib L0a: the semianalytic sets of BDL Def 2.1(i) form a Boolean algebra.
Everything is phrased through `LocForm V A` (the normal form of `A` on one open `V`). -/

open Filter Topology
section TopOpen
open NonsmoothLojasiewicz.Continuous

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace SubanalyticLib

section LocForm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

/-- `A` has the semianalytic normal form on `V`. -/
def LocForm (V A : Set X) : Prop :=
  ∃ (p q : ℕ) (F G : Fin p → Fin q → X → ℝ),
    (∀ i j, AnalyticOnNhd ℝ (F i j) V ∧ AnalyticOnNhd ℝ (G i j) V) ∧
    A ∩ V = V ∩ ⋃ i : Fin p, ⋂ j : Fin q, {x | F i j x = 0 ∧ 0 < G i j x}

theorem LocForm.congr {V A A' : Set X} (h : LocForm V A) (hA : A ∩ V = A' ∩ V) :
    LocForm V A' := by
  obtain ⟨p, q, F, G, hFG, hEq⟩ := h
  exact ⟨p, q, F, G, hFG, hA ▸ hEq⟩

theorem LocForm.mono {V V' A : Set X} (h : LocForm V A) (hV : V' ⊆ V) : LocForm V' A := by
  obtain ⟨p, q, F, G, hFG, hEq⟩ := h
  refine ⟨p, q, F, G, fun i j => ⟨(hFG i j).1.mono hV, (hFG i j).2.mono hV⟩, ?_⟩
  have h1 : A ∩ V' = (A ∩ V) ∩ V' := by
    rw [Set.inter_assoc, Set.inter_eq_right.mpr hV]
  rw [h1, hEq]
  ext x
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨_, h⟩, hx⟩; exact ⟨hx, h⟩
  · rintro ⟨hx, h⟩; exact ⟨⟨hV hx, h⟩, hx⟩

/-- Raise the number of conjuncts by padding with the trivial condition `0 = 0 ∧ 0 < 1`. -/
theorem LocForm.pad {V A : Set X} {p q : ℕ} {F G : Fin p → Fin q → X → ℝ}
    (hFG : ∀ i j, AnalyticOnNhd ℝ (F i j) V ∧ AnalyticOnNhd ℝ (G i j) V)
    (hEq : A ∩ V = V ∩ ⋃ i : Fin p, ⋂ j : Fin q, {x | F i j x = 0 ∧ 0 < G i j x})
    (q' : ℕ) (hq : q ≤ q') :
    ∃ F' G' : Fin p → Fin q' → X → ℝ,
      (∀ i j, AnalyticOnNhd ℝ (F' i j) V ∧ AnalyticOnNhd ℝ (G' i j) V) ∧
      A ∩ V = V ∩ ⋃ i : Fin p, ⋂ j : Fin q', {x | F' i j x = 0 ∧ 0 < G' i j x} := by
  refine ⟨fun i j x => if h : (j : ℕ) < q then F i ⟨j, h⟩ x else 0,
    fun i j x => if h : (j : ℕ) < q then G i ⟨j, h⟩ x else 1, ?_, ?_⟩
  · intro i j
    by_cases h : (j : ℕ) < q
    · simp only [h, dite_true]
      exact hFG i ⟨j, h⟩
    · simp only [h, dite_false]
      exact ⟨analyticOnNhd_const, analyticOnNhd_const⟩
  · rw [hEq]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, i, hi⟩
      refine ⟨hx, i, fun j => ?_⟩
      by_cases h : (j : ℕ) < q
      · simp only [h, dite_true]; exact hi ⟨j, h⟩
      · simp only [h, dite_false]; norm_num
    · rintro ⟨hx, i, hi⟩
      refine ⟨hx, i, fun j => ?_⟩
      have := hi ⟨j, lt_of_lt_of_le j.2 hq⟩
      simpa only [j.2, dite_true] using this

theorem locForm_empty (V : Set X) : LocForm V (∅ : Set X) :=
  ⟨0, 0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩

theorem locForm_univ (V : Set X) : LocForm V (Set.univ : Set X) :=
  ⟨1, 0, fun _ j => j.elim0, fun _ j => j.elim0, fun _ j => j.elim0, by
    rw [Set.univ_inter]; ext x
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter]
    exact ⟨fun h => ⟨h, 0, fun j => j.elim0⟩, fun h => h.1⟩⟩

theorem locForm_basic {V : Set X} {F G : X → ℝ} (hF : AnalyticOnNhd ℝ F V)
    (hG : AnalyticOnNhd ℝ G V) : LocForm V {x | F x = 0 ∧ 0 < G x} := by
  refine ⟨1, 1, fun _ _ => F, fun _ _ => G, fun _ _ => ⟨hF, hG⟩, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, hx⟩; exact ⟨hx, 0, fun _ => h⟩
  · rintro ⟨hx, _, h⟩; exact ⟨h 0, hx⟩

theorem locForm_zero {V : Set X} {F : X → ℝ} (hF : AnalyticOnNhd ℝ F V) :
    LocForm V {x | F x = 0} :=
  (locForm_basic hF (analyticOnNhd_const (v := (1 : ℝ)))).congr (by ext x; simp)

theorem locForm_pos {V : Set X} {G : X → ℝ} (hG : AnalyticOnNhd ℝ G V) :
    LocForm V {x | 0 < G x} :=
  (locForm_basic (analyticOnNhd_const (v := (0 : ℝ))) hG).congr (by ext x; simp)

theorem LocForm.union {V A B : Set X} (hA : LocForm V A) (hB : LocForm V B) :
    LocForm V (A ∪ B) := by
  obtain ⟨p, q, F, G, hFG, hEq⟩ := hA
  obtain ⟨p', q', F', G', hFG', hEq'⟩ := hB
  obtain ⟨F1, G1, hFG1, hEq1⟩ := LocForm.pad hFG hEq (max q q') (le_max_left _ _)
  obtain ⟨F2, G2, hFG2, hEq2⟩ := LocForm.pad hFG' hEq' (max q q') (le_max_right _ _)
  refine ⟨p + p', max q q',
    fun i => Fin.addCases (motive := fun _ => Fin (max q q') → X → ℝ) F1 F2 i,
    fun i => Fin.addCases (motive := fun _ => Fin (max q q') → X → ℝ) G1 G2 i, ?_, ?_⟩
  · intro i j
    induction i using Fin.addCases with
    | left i => simpa only [Fin.addCases_left] using hFG1 i j
    | right i => simpa only [Fin.addCases_right] using hFG2 i j
  · rw [Set.union_inter_distrib_right, hEq1, hEq2]
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_setOf_eq]
    constructor
    · rintro (⟨hx, i, hi⟩ | ⟨hx, i, hi⟩)
      · exact ⟨hx, Fin.castAdd p' i, by simpa only [Fin.addCases_left] using hi⟩
      · exact ⟨hx, Fin.natAdd p i, by simpa only [Fin.addCases_right] using hi⟩
    · rintro ⟨hx, i, hi⟩
      induction i using Fin.addCases with
      | left i => exact Or.inl ⟨hx, i, by simpa only [Fin.addCases_left] using hi⟩
      | right i => exact Or.inr ⟨hx, i, by simpa only [Fin.addCases_right] using hi⟩

theorem LocForm.inter {V A B : Set X} (hA : LocForm V A) (hB : LocForm V B) :
    LocForm V (A ∩ B) := by
  obtain ⟨p, q, F, G, hFG, hEq⟩ := hA
  obtain ⟨p', q', F', G', hFG', hEq'⟩ := hB
  let F'' : Fin (p * p') → Fin (q + q') → X → ℝ := fun i j =>
    Fin.addCases (motive := fun _ => X → ℝ) (fun j => F (finProdFinEquiv.symm i).1 j)
      (fun j => F' (finProdFinEquiv.symm i).2 j) j
  let G'' : Fin (p * p') → Fin (q + q') → X → ℝ := fun i j =>
    Fin.addCases (motive := fun _ => X → ℝ) (fun j => G (finProdFinEquiv.symm i).1 j)
      (fun j => G' (finProdFinEquiv.symm i).2 j) j
  have key : ∀ x, (∃ i, ∀ j, F'' i j x = 0 ∧ 0 < G'' i j x) ↔
      (∃ i, ∀ j, F i j x = 0 ∧ 0 < G i j x) ∧ (∃ i, ∀ j, F' i j x = 0 ∧ 0 < G' i j x) := by
    intro x
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨⟨(finProdFinEquiv.symm i).1, fun j => ?_⟩, ⟨(finProdFinEquiv.symm i).2, fun j => ?_⟩⟩
      · have := hi (Fin.castAdd q' j)
        simpa only [F'', G'', Fin.addCases_left] using this
      · have := hi (Fin.natAdd q j)
        simpa only [F'', G'', Fin.addCases_right] using this
    · rintro ⟨⟨i, hi⟩, ⟨i', hi'⟩⟩
      refine ⟨finProdFinEquiv (i, i'), fun j => ?_⟩
      induction j using Fin.addCases with
      | left j =>
        simp only [F'', G'', Fin.addCases_left, Equiv.symm_apply_apply]
        exact hi j
      | right j =>
        simp only [F'', G'', Fin.addCases_right, Equiv.symm_apply_apply]
        exact hi' j
  refine ⟨p * p', q + q', F'', G'', ?_, ?_⟩
  · intro i j
    induction j using Fin.addCases with
    | left j =>
      simp only [F'', G'', Fin.addCases_left]
      exact hFG _ _
    | right j =>
      simp only [F'', G'', Fin.addCases_right]
      exact hFG' _ _
  · ext x
    have h := Set.ext_iff.mp hEq x
    have h' := Set.ext_iff.mp hEq' x
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq] at h h' ⊢
    rw [key x]
    exact ⟨fun ⟨⟨ha, hb⟩, hv⟩ => ⟨hv, (h.1 ⟨ha, hv⟩).2, (h'.1 ⟨hb, hv⟩).2⟩,
      fun ⟨hv, r1, r2⟩ => ⟨⟨(h.2 ⟨hv, r1⟩).1, (h'.2 ⟨hv, r2⟩).1⟩, hv⟩⟩

theorem LocForm.iUnion {V : Set X} : ∀ {k : ℕ} {S : Fin k → Set X},
    (∀ j, LocForm V (S j)) → LocForm V (⋃ j, S j)
  | 0, S, _ => (locForm_empty V).congr (by simp)
  | k + 1, S, h => by
    have e : (⋃ j, S j) = S 0 ∪ ⋃ j : Fin k, S j.succ := by
      ext x; simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨j, hj⟩
        induction j using Fin.cases with
        | zero => exact Or.inl hj
        | succ j => exact Or.inr ⟨j, hj⟩
      · rintro (hj | ⟨j, hj⟩)
        · exact ⟨0, hj⟩
        · exact ⟨j.succ, hj⟩
    rw [e]
    exact (h 0).union (LocForm.iUnion fun j => h j.succ)

theorem LocForm.iInter {V : Set X} : ∀ {k : ℕ} {S : Fin k → Set X},
    (∀ j, LocForm V (S j)) → LocForm V (⋂ j, S j)
  | 0, S, _ => (locForm_univ V).congr (by simp)
  | k + 1, S, h => by
    have e : (⋂ j, S j) = S 0 ∩ ⋂ j : Fin k, S j.succ := by
      ext x; simp only [Set.mem_iInter, Set.mem_inter_iff]
      constructor
      · intro hj; exact ⟨hj 0, fun j => hj j.succ⟩
      · rintro ⟨h0, hj⟩ j
        induction j using Fin.cases with
        | zero => exact h0
        | succ j => exact hj j
    rw [e]
    exact (h 0).inter (LocForm.iInter fun j => h j.succ)

/-- The complement of a basic set is a union of four basic sets. -/
theorem locForm_basic_compl {V : Set X} {F G : X → ℝ} (hF : AnalyticOnNhd ℝ F V)
    (hG : AnalyticOnNhd ℝ G V) : LocForm V {x | F x = 0 ∧ 0 < G x}ᶜ := by
  have hnF : AnalyticOnNhd ℝ (fun x => -F x) V := hF.neg
  have hnG : AnalyticOnNhd ℝ (fun x => -G x) V := hG.neg
  have h := (((locForm_pos hF).union (locForm_pos hnF)).union (locForm_zero hG)).union
    (locForm_pos hnG)
  refine h.congr ?_
  ext x
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, Set.mem_compl_iff, not_and,
    not_lt]
  constructor
  · rintro ⟨hx, hV⟩
    refine ⟨fun hF0 => ?_, hV⟩
    rcases hx with ((h1 | h1) | h1) | h1
    · linarith
    · linarith
    · linarith
    · linarith
  · rintro ⟨hx, hV⟩
    refine ⟨?_, hV⟩
    by_cases hF0 : F x = 0
    · have := hx hF0
      rcases this.lt_or_eq with h1 | h1
      · exact Or.inr (by linarith)
      · exact Or.inl (Or.inr h1)
    · rcases lt_or_gt_of_ne hF0 with h1 | h1
      · exact Or.inl (Or.inl (Or.inr (by linarith)))
      · exact Or.inl (Or.inl (Or.inl h1))

theorem LocForm.compl {V A : Set X} (hA : LocForm V A) : LocForm V Aᶜ := by
  obtain ⟨p, q, F, G, hFG, hEq⟩ := hA
  have h : LocForm V (⋂ i : Fin p, ⋃ j : Fin q, {x | F i j x = 0 ∧ 0 < G i j x}ᶜ) :=
    LocForm.iInter fun i => LocForm.iUnion fun j =>
      locForm_basic_compl (hFG i j).1 (hFG i j).2
  refine h.congr ?_
  have e : Aᶜ ∩ V = V \ (A ∩ V) := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff]; exact ⟨fun ⟨hna, hv⟩ => ⟨hv, fun hav => hna hav.1⟩, fun ⟨hv, hn⟩ => ⟨fun ha => hn ⟨ha, hv⟩, hv⟩⟩
  rw [e, hEq]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_iUnion, Set.mem_compl_iff,
    Set.mem_diff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hall, hx⟩
    refine ⟨hx, fun ⟨_, i, hi⟩ => ?_⟩
    obtain ⟨j, hj⟩ := hall i
    exact hj (hi j)
  · rintro ⟨hx, hn⟩
    refine ⟨fun i => ?_, hx⟩
    by_contra hc
    exact hn ⟨hx, i, fun j => by_contra fun hj => hc ⟨j, hj⟩⟩

end LocForm

section Semi

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

theorem semi_empty : IsSemianalytic (∅ : Set X) :=
  fun _ => ⟨Set.univ, isOpen_univ, trivial, locForm_empty _⟩

theorem semi_univ : IsSemianalytic (Set.univ : Set X) :=
  fun _ => ⟨Set.univ, isOpen_univ, trivial, locForm_univ _⟩

theorem semi_union {A B : Set X} (hA : IsSemianalytic A) (hB : IsSemianalytic B) :
    IsSemianalytic (A ∪ B) := by
  intro x₀
  obtain ⟨V, hV, hx, (h : LocForm V A)⟩ := hA x₀
  obtain ⟨V', hV', hx', (h' : LocForm V' B)⟩ := hB x₀
  exact ⟨V ∩ V', hV.inter hV', ⟨hx, hx'⟩,
    (h.mono Set.inter_subset_left).union (h'.mono Set.inter_subset_right)⟩

theorem semi_inter {A B : Set X} (hA : IsSemianalytic A) (hB : IsSemianalytic B) :
    IsSemianalytic (A ∩ B) := by
  intro x₀
  obtain ⟨V, hV, hx, (h : LocForm V A)⟩ := hA x₀
  obtain ⟨V', hV', hx', (h' : LocForm V' B)⟩ := hB x₀
  exact ⟨V ∩ V', hV.inter hV', ⟨hx, hx'⟩,
    (h.mono Set.inter_subset_left).inter (h'.mono Set.inter_subset_right)⟩

theorem semi_compl {A : Set X} (hA : IsSemianalytic A) : IsSemianalytic Aᶜ := by
  intro x₀
  obtain ⟨V, hV, hx, (h : LocForm V A)⟩ := hA x₀
  exact ⟨V, hV, hx, h.compl⟩

theorem semi_iUnion : ∀ {k : ℕ} {S : Fin k → Set X},
    (∀ j, IsSemianalytic (S j)) → IsSemianalytic (⋃ j, S j)
  | 0, S, _ => by simpa using (semi_empty : IsSemianalytic (∅ : Set X))
  | k + 1, S, h => by
    have e : (⋃ j, S j) = S 0 ∪ ⋃ j : Fin k, S j.succ := by
      ext x; simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨j, hj⟩
        induction j using Fin.cases with
        | zero => exact Or.inl hj
        | succ j => exact Or.inr ⟨j, hj⟩
      · rintro (hj | ⟨j, hj⟩)
        · exact ⟨0, hj⟩
        · exact ⟨j.succ, hj⟩
    rw [e]
    exact semi_union (h 0) (semi_iUnion fun j => h j.succ)

theorem semi_iInter {k : ℕ} {S : Fin k → Set X} (h : ∀ j, IsSemianalytic (S j)) :
    IsSemianalytic (⋂ j, S j) := by
  have := semi_compl (semi_iUnion (fun j => semi_compl (h j)))
  simpa [Set.compl_iUnion] using this

/-- Sets cut out on all of `X` by one analytic equation or inequality. -/
theorem semi_zero {F : X → ℝ} (hF : AnalyticOnNhd ℝ F Set.univ) :
    IsSemianalytic {x | F x = 0} :=
  fun _ => ⟨Set.univ, isOpen_univ, trivial, locForm_zero hF⟩

theorem semi_pos {G : X → ℝ} (hG : AnalyticOnNhd ℝ G Set.univ) :
    IsSemianalytic {x | 0 < G x} :=
  fun _ => ⟨Set.univ, isOpen_univ, trivial, locForm_pos hG⟩

theorem semi_nonneg {G : X → ℝ} (hG : AnalyticOnNhd ℝ G Set.univ) :
    IsSemianalytic {x | 0 ≤ G x} := by
  have h := semi_compl (semi_pos (G := fun x => -G x) hG.neg)
  refine (congrArg IsSemianalytic ?_).mp h
  ext x; simp

theorem semi_lt {F G : X → ℝ} (hF : AnalyticOnNhd ℝ F Set.univ)
    (hG : AnalyticOnNhd ℝ G Set.univ) : IsSemianalytic {x | F x < G x} := by
  have h := semi_pos (G := fun x => G x - F x) (hG.sub hF)
  refine (congrArg IsSemianalytic ?_).mp h
  ext x; simp

theorem semi_le {F G : X → ℝ} (hF : AnalyticOnNhd ℝ F Set.univ)
    (hG : AnalyticOnNhd ℝ G Set.univ) : IsSemianalytic {x | F x ≤ G x} := by
  have h := semi_nonneg (G := fun x => G x - F x) (hG.sub hF)
  refine (congrArg IsSemianalytic ?_).mp h
  ext x; simp

theorem semi_eq {F G : X → ℝ} (hF : AnalyticOnNhd ℝ F Set.univ)
    (hG : AnalyticOnNhd ℝ G Set.univ) : IsSemianalytic {x | F x = G x} := by
  have h := semi_zero (F := fun x => F x - G x) (hF.sub hG)
  refine (congrArg IsSemianalytic ?_).mp h
  ext x; simp [sub_eq_zero]

end Semi


section General

theorem analytic_normsq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) :
    AnalyticAt ℝ (fun x : E => ‖x‖ ^ 2) x := by
  have hd : AnalyticAt ℝ (fun y : E => (y, y)) x := analyticAt_id.prod analyticAt_id
  have hb : AnalyticAt ℝ (fun q : E × E => (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) q.1 q.2)
      ((fun y : E => (y, y)) x) := ContinuousLinearMap.analyticAt_bilinear _ _
  have := AnalyticAt.comp (f := fun y : E => (y, y)) hb hd
  convert this using 1
  funext y
  simp

theorem semi_preimage {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {Φ : X → Y} (hΦ : ∀ x, AnalyticAt ℝ Φ x) {B : Set Y} (hB : IsSemianalytic B) :
    IsSemianalytic (Φ ⁻¹' B) := by
  intro x₀
  obtain ⟨V, hVo, hxV, p, q, F, G, hFG, hEq⟩ := hB (Φ x₀)
  have hc : Continuous Φ := continuous_iff_continuousAt.2 fun x => (hΦ x).continuousAt
  refine ⟨Φ ⁻¹' V, hVo.preimage hc, hxV, p, q, fun i j y => F i j (Φ y),
    fun i j y => G i j (Φ y), ?_, ?_⟩
  · intro i j
    exact ⟨(hFG i j).1.comp (fun y _ => hΦ y) (fun y hy => hy),
      (hFG i j).2.comp (fun y _ => hΦ y) (fun y hy => hy)⟩
  · ext y
    have h := Set.ext_iff.mp hEq (Φ y)
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_setOf_eq] at h ⊢
    exact h

/-- Re-express a bounded semianalytic witness in `X × Y` (any finite-dimensional `Y`) as one in
`X × ℝ^m` with `m ≥ 1`, with the same projection. -/
theorem wit {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {B : Set (X × Y)} (hB : IsSemianalytic B) (hb : Bornology.IsBounded B) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ B' : Set (X × EuclideanSpace ℝ (Fin m)),
      IsSemianalytic B' ∧ Bornology.IsBounded B' ∧ Prod.fst '' B' = Prod.fst '' B := by
  let e : (Y × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (Y × ℝ))) := toEuclidean
  have hm : 1 ≤ Module.finrank ℝ (Y × ℝ) := by
    rw [Module.finrank_prod, Module.finrank_self]; omega
  let es : EuclideanSpace ℝ (Fin (Module.finrank ℝ (Y × ℝ))) →L[ℝ] Y × ℝ := e.symm
  let Φ : X × EuclideanSpace ℝ (Fin (Module.finrank ℝ (Y × ℝ))) → X × Y :=
    fun z => (z.1, (es z.2).1)
  let T : X × EuclideanSpace ℝ (Fin (Module.finrank ℝ (Y × ℝ))) → ℝ := fun z => (es z.2).2
  have hΦ : ∀ z, AnalyticAt ℝ Φ z := fun z =>
    analyticAt_fst.prod (((ContinuousLinearMap.fst ℝ Y ℝ).analyticAt _).comp
      ((es.analyticAt _).comp analyticAt_snd))
  have hT : AnalyticOnNhd ℝ T Set.univ := fun z _ =>
    ((ContinuousLinearMap.snd ℝ Y ℝ).analyticAt _).comp ((es.analyticAt _).comp analyticAt_snd)
  refine ⟨_, hm, Φ ⁻¹' B ∩ {z | T z = 0}, semi_inter (semi_preimage hΦ hB) (semi_zero hT),
    ?_, ?_⟩
  · obtain ⟨R, hR⟩ := hb.exists_norm_le
    let eL : Y × ℝ →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ (Y × ℝ))) := e
    refine isBounded_iff_forall_norm_le.2 ⟨R + ‖eL‖ * R, fun z hz => ?_⟩
    obtain ⟨hzB, hzT⟩ := hz
    have h1 := hR _ hzB
    have hR0 : 0 ≤ R := (norm_nonneg _).trans h1
    have hz1 : ‖z.1‖ ≤ R := (norm_fst_le (Φ z)).trans h1
    have hz2 : ‖(es z.2).1‖ ≤ R := (norm_snd_le (Φ z)).trans h1
    have hT0 : (es z.2).2 = 0 := hzT
    have hz3 : ‖z.2‖ ≤ ‖eL‖ * R := by
      have hze : z.2 = eL (es z.2) := (e.apply_symm_apply _).symm
      rw [hze]
      refine (eL.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      refine norm_prod_le_iff.2 ⟨hz2, ?_⟩
      rw [hT0, norm_zero]; exact hR0
    have hm0 : 0 ≤ ‖eL‖ * R := mul_nonneg (norm_nonneg _) hR0
    exact norm_prod_le_iff.2 ⟨by linarith, by linarith⟩
  · ext x
    constructor
    · rintro ⟨z, ⟨hzB, -⟩, rfl⟩
      exact ⟨Φ z, hzB, rfl⟩
    · rintro ⟨⟨x, y⟩, hB', rfl⟩
      refine ⟨(x, e (y, 0)), ⟨?_, ?_⟩, rfl⟩
      · show (x, (e.symm (e (y, 0))).1) ∈ B
        simpa using hB'
      · show (e.symm (e (y, 0))).2 = 0
        simp

end General

section Sub

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

/-- Bounded open semianalytic neighbourhoods ("Euclidean balls" through `toEuclidean`). -/
def ebox (x₀ : X) (r : ℝ) : Set X := {x | ‖toEuclidean (x - x₀)‖ ^ 2 < r ^ 2}

theorem ebox_semi (x₀ : X) (r : ℝ) : IsSemianalytic (ebox x₀ r) := by
  let T : X →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ X)) :=
    (toEuclidean : X ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ X))).toContinuousLinearMap
  have h : AnalyticOnNhd ℝ (fun x : X => ‖T (x - x₀)‖ ^ 2) Set.univ := fun x _ =>
    (analytic_normsq _).comp ((T.analyticAt _).comp (analyticAt_id.sub analyticAt_const))
  exact semi_lt h analyticOnNhd_const

theorem ebox_open (x₀ : X) (r : ℝ) : IsOpen (ebox x₀ r) := by
  let T : X →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ X)) :=
    (toEuclidean : X ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ X))).toContinuousLinearMap
  have hc : Continuous fun x : X => ‖T (x - x₀)‖ ^ 2 :=
    ((T.continuous.comp (continuous_id.sub continuous_const)).norm).pow 2
  exact isOpen_lt hc continuous_const

theorem ebox_mem (x₀ : X) {r : ℝ} (hr : 0 < r) : x₀ ∈ ebox x₀ r := by
  show ‖toEuclidean (x₀ - x₀)‖ ^ 2 < r ^ 2
  simp only [sub_self, map_zero, norm_zero]
  nlinarith [mul_pos hr hr]

theorem ebox_nhds (x₀ : X) {r : ℝ} (hr : 0 < r) : ebox x₀ r ∈ 𝓝 x₀ :=
  (ebox_open x₀ r).mem_nhds (ebox_mem x₀ hr)

theorem ebox_bdd (x₀ : X) (r : ℝ) : Bornology.IsBounded (ebox x₀ r) := by
  let T : X →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ X)) :=
    (toEuclidean : X ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ X))).toContinuousLinearMap
  let S : EuclideanSpace ℝ (Fin (Module.finrank ℝ X)) →L[ℝ] X :=
    (toEuclidean : X ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ X))).symm.toContinuousLinearMap
  refine isBounded_iff_forall_norm_le.2 ⟨‖x₀‖ + ‖S‖ * |r|, fun x hx => ?_⟩
  have hx' : ‖T (x - x₀)‖ ^ 2 < r ^ 2 := hx
  have h1 : ‖T (x - x₀)‖ < |r| := by
    have := sq_lt_sq.1 hx'
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have h2 : x - x₀ = S (T (x - x₀)) := (toEuclidean.symm_apply_apply _).symm
  have h3 : ‖x - x₀‖ ≤ ‖S‖ * |r| := by
    rw [h2]
    exact (S.le_opNorm _).trans (mul_le_mul_of_nonneg_left h1.le (norm_nonneg _))
  have h4 : ‖x‖ ≤ ‖x₀‖ + ‖x - x₀‖ := by
    have := norm_add_le x₀ (x - x₀)
    simpa using this
  linarith

theorem ebox_sub (x₀ : X) {U : Set X} (hU : U ∈ 𝓝 x₀) : ∃ r > 0, ebox x₀ r ⊆ U := by
  let T : X →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ X)) :=
    (toEuclidean : X ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ X))).toContinuousLinearMap
  let S : EuclideanSpace ℝ (Fin (Module.finrank ℝ X)) →L[ℝ] X :=
    (toEuclidean : X ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ X))).symm.toContinuousLinearMap
  let g : EuclideanSpace ℝ (Fin (Module.finrank ℝ X)) → X := fun v => x₀ + S v
  have hg : Tendsto g (𝓝 0) (𝓝 x₀) := by
    have : Continuous g := continuous_const.add S.continuous
    simpa [g] using this.tendsto 0
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hg hU)
  refine ⟨ε, hε, fun x hx => ?_⟩
  have hx' : ‖T (x - x₀)‖ ^ 2 < ε ^ 2 := hx
  have h1 : ‖T (x - x₀)‖ < ε := by
    have := sq_lt_sq.1 hx'
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_pos hε] at this
  have h2 : g (T (x - x₀)) = x := by
    show x₀ + toEuclidean.symm (toEuclidean (x - x₀)) = x
    rw [ContinuousLinearEquiv.symm_apply_apply]; abel
  have h3 : T (x - x₀) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ X))) ε := by
    simpa using h1
  have := hball h3
  rwa [Set.mem_preimage, h2] at this

theorem restr {A V W S : Set X} (hEq : A ∩ V = S) (hW : W ⊆ V) : A ∩ W = S ∩ W := by
  rw [← hEq]
  ext x
  constructor
  · rintro ⟨ha, hw⟩; exact ⟨⟨ha, hW hw⟩, hw⟩
  · rintro ⟨⟨ha, _⟩, hw⟩; exact ⟨ha, hw⟩

theorem sub_of_semi {A : Set X} (hA : IsSemianalytic A) : IsSubanalytic A := by
  intro x₀
  let W := ebox x₀ 1
  let B : Set (X × ℝ) := Prod.fst ⁻¹' (A ∩ W) ∩ {z | z.2 = 0}
  have hBs : IsSemianalytic B :=
    semi_inter (semi_preimage (fun z => analyticAt_fst) (semi_inter hA (ebox_semi x₀ 1)))
      (semi_zero (fun z _ => analyticAt_snd))
  have hBb : Bornology.IsBounded B := by
    obtain ⟨R, hR⟩ := (ebox_bdd x₀ 1).exists_norm_le
    refine isBounded_iff_forall_norm_le.2 ⟨R, fun z hz => ?_⟩
    obtain ⟨⟨_, hzW⟩, hz2⟩ := hz
    have h1 := hR _ hzW
    have h2 : z.2 = 0 := hz2
    refine norm_prod_le_iff.2 ⟨h1, ?_⟩
    rw [h2, norm_zero]; exact (norm_nonneg _).trans h1
  obtain ⟨m, hm, B', h1, h2, h3⟩ := wit hBs hBb
  refine ⟨W, ebox_nhds x₀ one_pos, m, hm, B', h1, h2, ?_⟩
  rw [h3]
  ext x
  constructor
  · intro hx; exact ⟨(x, 0), ⟨hx, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨hz, -⟩, rfl⟩; exact hz

theorem sub_union {A A' : Set X} (hA : IsSubanalytic A) (hA' : IsSubanalytic A') :
    IsSubanalytic (A ∪ A') := by
  intro x₀
  obtain ⟨V, hV, m, -, B, hBs, hBb, hEq⟩ := hA x₀
  obtain ⟨V', hV', m', -, B', hBs', hBb', hEq'⟩ := hA' x₀
  obtain ⟨r, hr, hsub⟩ := ebox_sub x₀ (Filter.inter_mem hV hV')
  let W := ebox x₀ r
  have hW1 : W ⊆ V := fun x hx => (hsub hx).1
  have hW2 : W ⊆ V' := fun x hx => (hsub hx).2
  let P1 : X × (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m')) →
      X × EuclideanSpace ℝ (Fin m) := fun z => (z.1, z.2.1)
  let P2 : X × (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m')) →
      X × EuclideanSpace ℝ (Fin m') := fun z => (z.1, z.2.2)
  have hP1 : ∀ z, AnalyticAt ℝ P1 z := fun z => analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)
  have hP2 : ∀ z, AnalyticAt ℝ P2 z := fun z => analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)
  have hZ1 : IsSemianalytic {z : X × (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m')) |
      ‖z.2.2‖ ^ 2 = 0} :=
    semi_zero (fun z _ => (analytic_normsq _).comp (analyticAt_snd.comp analyticAt_snd))
  have hZ2 : IsSemianalytic {z : X × (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m')) |
      ‖z.2.1‖ ^ 2 = 0} :=
    semi_zero (fun z _ => (analytic_normsq _).comp (analyticAt_fst.comp analyticAt_snd))
  have hWs : IsSemianalytic (Prod.fst ⁻¹' W :
      Set (X × (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m')))) :=
    semi_preimage (fun z => analyticAt_fst) (ebox_semi x₀ r)
  let C := (P1 ⁻¹' B ∩ Prod.fst ⁻¹' W ∩ {z | ‖z.2.2‖ ^ 2 = 0}) ∪
    (P2 ⁻¹' B' ∩ Prod.fst ⁻¹' W ∩ {z | ‖z.2.1‖ ^ 2 = 0})
  have hCs : IsSemianalytic C :=
    semi_union (semi_inter (semi_inter (semi_preimage hP1 hBs) hWs) hZ1)
      (semi_inter (semi_inter (semi_preimage hP2 hBs') hWs) hZ2)
  have hCb : Bornology.IsBounded C := by
    obtain ⟨R, hR⟩ := hBb.exists_norm_le
    obtain ⟨R', hR'⟩ := hBb'.exists_norm_le
    refine isBounded_iff_forall_norm_le.2 ⟨|R| + |R'|, fun z hz => ?_⟩
    have hRa := le_abs_self R
    have hRb := le_abs_self R'
    have hRc := abs_nonneg R
    have hRd := abs_nonneg R'
    rcases hz with ⟨⟨hzB, -⟩, hz0⟩ | ⟨⟨hzB, -⟩, hz0⟩
    · have h1 := hR _ hzB
      have hz0' : ‖z.2.2‖ ^ 2 = 0 := hz0
      have hn := norm_nonneg z.2.2
      have h2 : ‖z.2.2‖ ≤ 0 := by nlinarith
      have ha : ‖z.1‖ ≤ R := (norm_fst_le (P1 z)).trans h1
      have hb : ‖z.2.1‖ ≤ R := (norm_snd_le (P1 z)).trans h1
      exact norm_prod_le_iff.2 ⟨by linarith, norm_prod_le_iff.2 ⟨by linarith, by linarith⟩⟩
    · have h1 := hR' _ hzB
      have hz0' : ‖z.2.1‖ ^ 2 = 0 := hz0
      have hn := norm_nonneg z.2.1
      have h2 : ‖z.2.1‖ ≤ 0 := by nlinarith
      have ha : ‖z.1‖ ≤ R' := (norm_fst_le (P2 z)).trans h1
      have hb : ‖z.2.2‖ ≤ R' := (norm_snd_le (P2 z)).trans h1
      exact norm_prod_le_iff.2 ⟨by linarith, norm_prod_le_iff.2 ⟨by linarith, by linarith⟩⟩
  obtain ⟨k, hk, C', h1, h2, h3⟩ := wit hCs hCb
  refine ⟨W, ebox_nhds x₀ hr, k, hk, C', h1, h2, ?_⟩
  rw [h3, Set.union_inter_distrib_right, restr hEq hW1, restr hEq' hW2]
  ext x
  constructor
  · rintro (⟨⟨⟨x', y⟩, hB, rfl⟩, hx⟩ | ⟨⟨⟨x', y⟩, hB, rfl⟩, hx⟩)
    · exact ⟨(x', (y, 0)), Or.inl ⟨⟨hB, hx⟩, by simp⟩, rfl⟩
    · exact ⟨(x', (0, y)), Or.inr ⟨⟨hB, hx⟩, by simp⟩, rfl⟩
  · rintro ⟨z, (⟨⟨hB, hx⟩, -⟩ | ⟨⟨hB, hx⟩, -⟩), rfl⟩
    · exact Or.inl ⟨⟨P1 z, hB, rfl⟩, hx⟩
    · exact Or.inr ⟨⟨P2 z, hB, rfl⟩, hx⟩

theorem sub_inter {A A' : Set X} (hA : IsSubanalytic A) (hA' : IsSubanalytic A') :
    IsSubanalytic (A ∩ A') := by
  intro x₀
  obtain ⟨V, hV, m, -, B, hBs, hBb, hEq⟩ := hA x₀
  obtain ⟨V', hV', m', -, B', hBs', hBb', hEq'⟩ := hA' x₀
  obtain ⟨r, hr, hsub⟩ := ebox_sub x₀ (Filter.inter_mem hV hV')
  let W := ebox x₀ r
  have hW1 : W ⊆ V := fun x hx => (hsub hx).1
  have hW2 : W ⊆ V' := fun x hx => (hsub hx).2
  let P1 : X × (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m')) →
      X × EuclideanSpace ℝ (Fin m) := fun z => (z.1, z.2.1)
  let P2 : X × (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m')) →
      X × EuclideanSpace ℝ (Fin m') := fun z => (z.1, z.2.2)
  have hP1 : ∀ z, AnalyticAt ℝ P1 z := fun z => analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)
  have hP2 : ∀ z, AnalyticAt ℝ P2 z := fun z => analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)
  have hWs : IsSemianalytic (Prod.fst ⁻¹' W :
      Set (X × (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m')))) :=
    semi_preimage (fun z => analyticAt_fst) (ebox_semi x₀ r)
  let C := P1 ⁻¹' B ∩ P2 ⁻¹' B' ∩ Prod.fst ⁻¹' W
  have hCs : IsSemianalytic C :=
    semi_inter (semi_inter (semi_preimage hP1 hBs) (semi_preimage hP2 hBs')) hWs
  have hCb : Bornology.IsBounded C := by
    obtain ⟨R, hR⟩ := hBb.exists_norm_le
    obtain ⟨R', hR'⟩ := hBb'.exists_norm_le
    refine isBounded_iff_forall_norm_le.2 ⟨R + R', fun z hz => ?_⟩
    obtain ⟨⟨hzB, hzB'⟩, -⟩ := hz
    have h1 := hR _ hzB
    have h1' := hR' _ hzB'
    have hR0 : 0 ≤ R := (norm_nonneg _).trans h1
    have hR0' : 0 ≤ R' := (norm_nonneg _).trans h1'
    have ha : ‖z.1‖ ≤ R := (norm_fst_le (P1 z)).trans h1
    have hb : ‖z.2.1‖ ≤ R := (norm_snd_le (P1 z)).trans h1
    have hc : ‖z.2.2‖ ≤ R' := (norm_snd_le (P2 z)).trans h1'
    exact norm_prod_le_iff.2 ⟨by linarith, norm_prod_le_iff.2 ⟨by linarith, by linarith⟩⟩
  obtain ⟨k, hk, C', h1, h2, h3⟩ := wit hCs hCb
  refine ⟨W, ebox_nhds x₀ hr, k, hk, C', h1, h2, ?_⟩
  have e1 : (A ∩ A') ∩ W = (A ∩ W) ∩ (A' ∩ W) := by
    ext x; simp only [Set.mem_inter_iff]; exact ⟨fun ⟨⟨a, b⟩, w⟩ => ⟨⟨a, w⟩, b, w⟩, fun ⟨⟨a, w⟩, b, _⟩ => ⟨⟨a, b⟩, w⟩⟩
  rw [h3, e1, restr hEq hW1, restr hEq' hW2]
  ext x
  constructor
  · rintro ⟨⟨⟨p, hB, hp⟩, hx⟩, ⟨p', hB', hp'⟩, -⟩
    refine ⟨(x, (p.2, p'.2)), ⟨⟨?_, ?_⟩, hx⟩, rfl⟩
    · show (x, p.2) ∈ B
      have : p = (x, p.2) := Prod.ext hp rfl
      rw [← this]; exact hB
    · show (x, p'.2) ∈ B'
      have : p' = (x, p'.2) := Prod.ext hp' rfl
      rw [← this]; exact hB'
  · rintro ⟨z, ⟨⟨hB, hB'⟩, hx⟩, rfl⟩
    exact ⟨⟨⟨P1 z, hB, rfl⟩, hx⟩, ⟨P2 z, hB', rfl⟩, hx⟩

end Sub


section Wit

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

/-- `A ∩ W` is the projection of a bounded semianalytic set of `X × ℝ^m` (any `m`). -/
def LocWit (A W : Set X) : Prop :=
  ∃ m : ℕ, ∃ B : Set (X × EuclideanSpace ℝ (Fin m)),
    IsSemianalytic B ∧ Bornology.IsBounded B ∧ A ∩ W = Prod.fst '' B

theorem locWit_of {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {A W : Set X} {B : Set (X × Y)} (hB : IsSemianalytic B) (hb : Bornology.IsBounded B)
    (hEq : A ∩ W = Prod.fst '' B) : LocWit A W := by
  obtain ⟨m, -, B', h1, h2, h3⟩ := wit hB hb
  exact ⟨m, B', h1, h2, hEq.trans h3.symm⟩

theorem sub_iff_locWit {A : Set X} : IsSubanalytic A ↔ ∀ x₀, ∃ W ∈ 𝓝 x₀, LocWit A W := by
  constructor
  · intro h x₀
    obtain ⟨V, hV, m, -, B, h1, h2, h3⟩ := h x₀
    exact ⟨V, hV, m, B, h1, h2, h3⟩
  · intro h x₀
    obtain ⟨W, hW, m, B, h1, h2, h3⟩ := h x₀
    obtain ⟨k, hk, B', h1', h2', h3'⟩ := wit h1 h2
    exact ⟨W, hW, k, hk, B', h1', h2', h3.trans h3'.symm⟩

theorem LocWit.congr {A A' W : Set X} (h : LocWit A W) (hA : A ∩ W = A' ∩ W) :
    LocWit A' W := by
  obtain ⟨m, B, h1, h2, h3⟩ := h
  exact ⟨m, B, h1, h2, hA ▸ h3⟩

theorem LocWit.mono {A W W' : Set X} (h : LocWit A W) (hW : W' ⊆ W)
    (hW' : IsSemianalytic W') : LocWit A W' := by
  obtain ⟨m, B, h1, h2, h3⟩ := h
  refine ⟨m, B ∩ Prod.fst ⁻¹' W', semi_inter h1 (semi_preimage (fun z => analyticAt_fst) hW'),
    h2.subset Set.inter_subset_left, ?_⟩
  rw [restr h3 hW]
  ext x
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, hx⟩; exact ⟨p, ⟨hp, hx⟩, rfl⟩
  · rintro ⟨p, ⟨hp, hx⟩, rfl⟩; exact ⟨⟨p, hp, rfl⟩, hx⟩

theorem locWit_empty (W : Set X) : LocWit (∅ : Set X) W :=
  ⟨1, ∅, semi_empty, Bornology.isBounded_empty, by simp⟩

theorem LocWit.union {A A' W : Set X} (h : LocWit A W) (h' : LocWit A' W) :
    LocWit (A ∪ A') W := by
  obtain ⟨m, B, hBs, hBb, hEq⟩ := h
  obtain ⟨m', B', hBs', hBb', hEq'⟩ := h'
  let P1 : X × (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m')) →
      X × EuclideanSpace ℝ (Fin m) := fun z => (z.1, z.2.1)
  let P2 : X × (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m')) →
      X × EuclideanSpace ℝ (Fin m') := fun z => (z.1, z.2.2)
  have hP1 : ∀ z, AnalyticAt ℝ P1 z := fun z =>
    analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)
  have hP2 : ∀ z, AnalyticAt ℝ P2 z := fun z =>
    analyticAt_fst.prod (analyticAt_snd.comp analyticAt_snd)
  have hZ1 : IsSemianalytic {z : X × (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m')) |
      ‖z.2.2‖ ^ 2 = 0} :=
    semi_zero (fun z _ => (analytic_normsq _).comp (analyticAt_snd.comp analyticAt_snd))
  have hZ2 : IsSemianalytic {z : X × (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m')) |
      ‖z.2.1‖ ^ 2 = 0} :=
    semi_zero (fun z _ => (analytic_normsq _).comp (analyticAt_fst.comp analyticAt_snd))
  let C := (P1 ⁻¹' B ∩ {z | ‖z.2.2‖ ^ 2 = 0}) ∪ (P2 ⁻¹' B' ∩ {z | ‖z.2.1‖ ^ 2 = 0})
  have hCs : IsSemianalytic C :=
    semi_union (semi_inter (semi_preimage hP1 hBs) hZ1) (semi_inter (semi_preimage hP2 hBs') hZ2)
  have hCb : Bornology.IsBounded C := by
    obtain ⟨R, hR⟩ := hBb.exists_norm_le
    obtain ⟨R', hR'⟩ := hBb'.exists_norm_le
    refine isBounded_iff_forall_norm_le.2 ⟨|R| + |R'|, fun z hz => ?_⟩
    have hRa := le_abs_self R
    have hRb := le_abs_self R'
    have hRc := abs_nonneg R
    have hRd := abs_nonneg R'
    rcases hz with ⟨hzB, hz0⟩ | ⟨hzB, hz0⟩
    · have h1 := hR _ hzB
      have hz0' : ‖z.2.2‖ ^ 2 = 0 := hz0
      have hn := norm_nonneg z.2.2
      have h2 : ‖z.2.2‖ ≤ 0 := by nlinarith
      have ha : ‖z.1‖ ≤ R := (norm_fst_le (P1 z)).trans h1
      have hb : ‖z.2.1‖ ≤ R := (norm_snd_le (P1 z)).trans h1
      exact norm_prod_le_iff.2 ⟨by linarith, norm_prod_le_iff.2 ⟨by linarith, by linarith⟩⟩
    · have h1 := hR' _ hzB
      have hz0' : ‖z.2.1‖ ^ 2 = 0 := hz0
      have hn := norm_nonneg z.2.1
      have h2 : ‖z.2.1‖ ≤ 0 := by nlinarith
      have ha : ‖z.1‖ ≤ R' := (norm_fst_le (P2 z)).trans h1
      have hb : ‖z.2.2‖ ≤ R' := (norm_snd_le (P2 z)).trans h1
      exact norm_prod_le_iff.2 ⟨by linarith, norm_prod_le_iff.2 ⟨by linarith, by linarith⟩⟩
  refine locWit_of hCs hCb ?_
  rw [Set.union_inter_distrib_right, hEq, hEq']
  ext x
  constructor
  · rintro (⟨⟨x', y⟩, hB, rfl⟩ | ⟨⟨x', y⟩, hB, rfl⟩)
    · exact ⟨(x', (y, 0)), Or.inl ⟨hB, by simp⟩, rfl⟩
    · exact ⟨(x', (0, y)), Or.inr ⟨hB, by simp⟩, rfl⟩
  · rintro ⟨z, (⟨hB, -⟩ | ⟨hB, -⟩), rfl⟩
    · exact Or.inl ⟨P1 z, hB, rfl⟩
    · exact Or.inr ⟨P2 z, hB, rfl⟩

theorem locWit_biUnion {ι : Type*} [DecidableEq ι] {W : Set X} {S : ι → Set X}
    (t : Finset ι) (h : ∀ i ∈ t, LocWit (S i) W) : LocWit (⋃ i ∈ t, S i) W := by
  revert h
  refine Finset.induction_on t (fun _ => by simpa using locWit_empty W) ?_
  intro a s _ ih h
  rw [Finset.set_biUnion_insert]
  exact (h a (Finset.mem_insert_self a s)).union
    (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem sub_preimage {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {Φ : X → Y} (hΦ : ∀ x, AnalyticAt ℝ Φ x) {A : Set Y} (hA : IsSubanalytic A) :
    IsSubanalytic (Φ ⁻¹' A) := by
  rw [sub_iff_locWit]
  intro x₀
  obtain ⟨V, hV, m, -, B, h1, h2, h3⟩ := hA (Φ x₀)
  have hc : Continuous Φ := continuous_iff_continuousAt.2 fun x => (hΦ x).continuousAt
  obtain ⟨r, hr, hsub⟩ := ebox_sub x₀ (hc.continuousAt.preimage_mem_nhds hV)
  let W := ebox x₀ r
  let Ψ : X × EuclideanSpace ℝ (Fin m) → Y × EuclideanSpace ℝ (Fin m) := fun q => (Φ q.1, q.2)
  have hΨ : ∀ q, AnalyticAt ℝ Ψ q := fun q => ((hΦ q.1).comp analyticAt_fst).prod analyticAt_snd
  refine ⟨W, ebox_nhds x₀ hr, locWit_of (B := Ψ ⁻¹' B ∩ Prod.fst ⁻¹' W)
    (semi_inter (semi_preimage hΨ h1) (semi_preimage (fun q => analyticAt_fst) (ebox_semi x₀ r)))
    ?_ ?_⟩
  · obtain ⟨R, hR⟩ := h2.exists_norm_le
    obtain ⟨R', hR'⟩ := (ebox_bdd x₀ r).exists_norm_le
    refine isBounded_iff_forall_norm_le.2 ⟨|R| + |R'|, fun q hq => ?_⟩
    obtain ⟨hqB, hqW⟩ := hq
    have a1 : ‖q.1‖ ≤ R' := hR' _ hqW
    have a2 : ‖q.2‖ ≤ R := (norm_snd_le (Ψ q)).trans (hR _ hqB)
    have := le_abs_self R
    have := le_abs_self R'
    have := abs_nonneg R
    have := abs_nonneg R'
    exact norm_prod_le_iff.2 ⟨by linarith, by linarith⟩
  · ext x
    constructor
    · rintro ⟨hxA, hxW⟩
      have : Φ x ∈ Prod.fst '' B := by rw [← h3]; exact ⟨hxA, hsub hxW⟩
      obtain ⟨⟨y, e⟩, hB, hy⟩ := this
      refine ⟨(x, e), ⟨?_, hxW⟩, rfl⟩
      show (Φ x, e) ∈ B
      simp only at hy
      rw [← hy]
      exact hB
    · rintro ⟨q, ⟨hq, hqW⟩, rfl⟩
      have : Φ q.1 ∈ Prod.fst '' B := ⟨Ψ q, hq, rfl⟩
      rw [← h3] at this
      exact ⟨this.1, hqW⟩

/-- Projection of a bounded subanalytic set is subanalytic (finite cover of the fibre ball). -/
theorem sub_proj {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {A : Set (X × Z)} (hA : IsSubanalytic A) (hb : Bornology.IsBounded A) :
    IsSubanalytic (Prod.fst '' A) := by
  classical
  rw [sub_iff_locWit]
  intro x₀
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  have hK : IsCompact (Metric.closedBall (0 : Z) R) := isCompact_closedBall 0 R
  have hboxs : ∀ (z : Z) (r₁ r₂ : ℝ), IsSemianalytic (ebox x₀ r₁ ×ˢ ebox z r₂) := fun z r₁ r₂ =>
    semi_inter (semi_preimage (fun p => analyticAt_fst) (ebox_semi x₀ r₁))
      (semi_preimage (fun p => analyticAt_snd) (ebox_semi z r₂))
  have hloc : ∀ z : Z, ∃ r₁ > 0, ∃ r₂ > 0, LocWit A (ebox x₀ r₁ ×ˢ ebox z r₂) := by
    intro z
    obtain ⟨V, hV, hW⟩ := (sub_iff_locWit.1 hA) (x₀, z)
    rw [nhds_prod_eq] at hV
    obtain ⟨U, hU, O, hO, hUO⟩ := Filter.mem_prod_iff.1 hV
    obtain ⟨r₁, hr₁, h1⟩ := ebox_sub x₀ hU
    obtain ⟨r₂, hr₂, h2⟩ := ebox_sub z hO
    exact ⟨r₁, hr₁, r₂, hr₂, hW.mono (fun p hp => hUO ⟨h1 hp.1, h2 hp.2⟩) (hboxs z r₁ r₂)⟩
  choose r₁ hr₁ r₂ hr₂ hW using hloc
  obtain ⟨t, htK⟩ := hK.elim_finite_subcover (fun z => ebox z (r₂ z)) (fun z => ebox_open z _)
    (fun y _ => Set.mem_iUnion.2 ⟨y, ebox_mem y (hr₂ y)⟩)
  have hU : (⋂ z ∈ t, ebox x₀ (r₁ z)) ∈ 𝓝 x₀ :=
    (Filter.biInter_finset_mem t).2 fun z _ => ebox_nhds x₀ (hr₁ z)
  obtain ⟨ρ, hρ, hρsub⟩ := ebox_sub x₀ hU
  have hpiece : ∀ z ∈ t, LocWit (Prod.fst '' (A ∩ (ebox x₀ ρ ×ˢ ebox z (r₂ z)))) (ebox x₀ ρ) := by
    intro z hz
    have hsubW : ebox x₀ ρ ×ˢ ebox z (r₂ z) ⊆ ebox x₀ (r₁ z) ×ˢ ebox z (r₂ z) :=
      Set.prod_mono (fun x hx => Set.mem_iInter₂.1 (hρsub hx) z hz) le_rfl
    obtain ⟨m, B, h1, h2, h3⟩ := (hW z).mono hsubW (hboxs z ρ (r₂ z))
    let Φ : X × (Z × EuclideanSpace ℝ (Fin m)) → (X × Z) × EuclideanSpace ℝ (Fin m) :=
      fun q => ((q.1, q.2.1), q.2.2)
    have hΦ : ∀ q, AnalyticAt ℝ Φ q := fun q =>
      (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)).prod
        (analyticAt_snd.comp analyticAt_snd)
    refine locWit_of (semi_preimage hΦ h1) ?_ ?_
    · obtain ⟨R', hR'⟩ := h2.exists_norm_le
      refine isBounded_iff_forall_norm_le.2 ⟨R', fun q hq => ?_⟩
      have hq' := hR' _ hq
      have a0 : ‖((q.1, q.2.1) : X × Z)‖ ≤ R' := (norm_fst_le (Φ q)).trans hq'
      have a1 : ‖q.1‖ ≤ R' := (norm_fst_le ((q.1, q.2.1) : X × Z)).trans a0
      have a2 : ‖q.2.1‖ ≤ R' := (norm_snd_le ((q.1, q.2.1) : X × Z)).trans a0
      have a3 : ‖q.2.2‖ ≤ R' := (norm_snd_le (Φ q)).trans hq'
      exact norm_prod_le_iff.2 ⟨a1, norm_prod_le_iff.2 ⟨a2, a3⟩⟩
    · have hsub' : Prod.fst '' (A ∩ (ebox x₀ ρ ×ˢ ebox z (r₂ z))) ⊆ ebox x₀ ρ := by
        rintro _ ⟨p, ⟨-, hp, -⟩, rfl⟩; exact hp
      rw [Set.inter_eq_left.2 hsub']
      ext x
      constructor
      · rintro ⟨p, hp, rfl⟩
        have : p ∈ Prod.fst '' B := by rw [← h3]; exact hp
        obtain ⟨⟨p', e⟩, hB, hpe⟩ := this
        refine ⟨(p.1, (p.2, e)), ?_, rfl⟩
        show ((p.1, p.2), e) ∈ B
        simp only at hpe
        subst hpe
        exact hB
      · rintro ⟨q, hq, rfl⟩
        have hm : (Φ q).1 ∈ A ∩ (ebox x₀ ρ ×ˢ ebox z (r₂ z)) := by
          rw [h3]; exact ⟨Φ q, hq, rfl⟩
        exact ⟨(Φ q).1, hm, rfl⟩
  have hcover : Prod.fst '' A ∩ ebox x₀ ρ =
      (⋃ z ∈ t, Prod.fst '' (A ∩ (ebox x₀ ρ ×ˢ ebox z (r₂ z)))) ∩ ebox x₀ ρ := by
    ext x
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hx⟩
      have hpK : p.2 ∈ Metric.closedBall (0 : Z) R := by
        rw [mem_closedBall_zero_iff]; exact (norm_snd_le p).trans (hR p hp)
      obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.1 (htK hpK)
      exact ⟨Set.mem_iUnion₂.2 ⟨z, hz, p, ⟨hp, hx, hpz⟩, rfl⟩, hx⟩
    · rintro ⟨hx, hxW⟩
      obtain ⟨z, hz, p, ⟨hp, -⟩, rfl⟩ := Set.mem_iUnion₂.1 hx
      exact ⟨⟨p, hp, rfl⟩, hxW⟩
  exact ⟨ebox x₀ ρ, ebox_nhds x₀ hρ, (locWit_biUnion t hpiece).congr hcover.symm⟩

end Wit


section More

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

theorem sub_univ : IsSubanalytic (Set.univ : Set X) := sub_of_semi semi_univ

theorem sub_image_equiv {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (e : X ≃L[ℝ] Y) {A : Set X} (hA : IsSubanalytic A) : IsSubanalytic (e '' A) := by
  rw [e.image_eq_preimage_symm]
  exact sub_preimage (fun y => (e.symm : Y →L[ℝ] X).analyticAt y) hA

/-- The graph of a globally analytic real function is semianalytic, hence subanalytic. -/
theorem sub_graph_analytic {F : X → ℝ} (hF : ∀ x, AnalyticAt ℝ F x) :
    IsSubanalytic {p : X × ℝ | F p.1 = p.2} :=
  sub_of_semi (semi_eq (fun p _ => (hF p.1).comp analyticAt_fst) (fun p _ => analyticAt_snd))

end More

end SubanalyticLib

section L6Fwrap

/-! SubanalyticLib L1a: weighted ℓ¹ norms of multivariable power series.
`Conv w f` : the series `f` converges absolutely on the closed polydisc of polyradius `w`
(`∑ |a_α| w^α < ∞`); `wn w f` is that weighted norm.  These are the Banach-algebra estimates
behind convergent Weierstrass division (plan L2). -/


set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace SubanalyticLib

section Conv

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- weight of the monomial `X^α` for the polyradius `w`. -/
noncomputable def mw (w : σ → ℝ) (α : σ →₀ ℕ) : ℝ := ∏ i, w i ^ α i

theorem mw_zero (w : σ → ℝ) : mw w 0 = 1 := by simp [mw]

theorem mw_add (w : σ → ℝ) (α β : σ →₀ ℕ) : mw w (α + β) = mw w α * mw w β := by
  simp [mw, pow_add, Finset.prod_mul_distrib]

theorem mw_nonneg {w : σ → ℝ} (hw : ∀ i, 0 ≤ w i) (α : σ →₀ ℕ) : 0 ≤ mw w α :=
  Finset.prod_nonneg fun i _ => pow_nonneg (hw i) _

theorem mw_pos {w : σ → ℝ} (hw : ∀ i, 0 < w i) (α : σ →₀ ℕ) : 0 < mw w α :=
  Finset.prod_pos fun i _ => pow_pos (hw i) _

theorem mw_single (w : σ → ℝ) (i : σ) (k : ℕ) : mw w (Finsupp.single i k) = w i ^ k := by
  unfold mw
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem mw_mono {w w' : σ → ℝ} (hw' : ∀ i, 0 ≤ w' i) (hle : ∀ i, w' i ≤ w i) (α : σ →₀ ℕ) :
    mw w' α ≤ mw w α :=
  Finset.prod_le_prod (fun i _ => pow_nonneg (hw' i) _)
    (fun i _ => pow_le_pow_left₀ (hw' i) (hle i) _)

/-- the weighted absolute coefficient family. -/
noncomputable def wt (w : σ → ℝ) (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) : ℝ :=
  |coeff α f| * mw w α

/-- `f` converges absolutely on the closed polydisc of polyradius `w`. -/
def Conv (w : σ → ℝ) (f : MvPowerSeries σ ℝ) : Prop := Summable (wt w f)

/-- the weighted ℓ¹ norm. -/
noncomputable def wn (w : σ → ℝ) (f : MvPowerSeries σ ℝ) : ℝ := ∑' α, wt w f α

variable {w : σ → ℝ}

theorem wt_nonneg (hw : ∀ i, 0 ≤ w i) (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) : 0 ≤ wt w f α :=
  mul_nonneg (abs_nonneg _) (mw_nonneg hw α)

theorem wn_nonneg (hw : ∀ i, 0 ≤ w i) (f : MvPowerSeries σ ℝ) : 0 ≤ wn w f :=
  tsum_nonneg (wt_nonneg hw f)

theorem wt_zero (α : σ →₀ ℕ) : wt w 0 α = 0 := by simp [wt]

theorem conv_zero : Conv w (0 : MvPowerSeries σ ℝ) := by
  have : wt w (0 : MvPowerSeries σ ℝ) = fun _ => 0 := funext wt_zero
  rw [Conv, this]; exact summable_zero

theorem wn_zero : wn w (0 : MvPowerSeries σ ℝ) = 0 := by
  have : wt w (0 : MvPowerSeries σ ℝ) = fun _ => 0 := funext wt_zero
  rw [wn, this, tsum_zero]

theorem wt_neg (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) : wt w (-f) α = wt w f α := by
  simp [wt]

theorem Conv.neg {f : MvPowerSeries σ ℝ} (hf : Conv w f) : Conv w (-f) := by
  have : wt w (-f) = wt w f := funext (wt_neg f)
  rw [Conv, this]; exact hf

theorem wn_neg (f : MvPowerSeries σ ℝ) : wn w (-f) = wn w f := by
  have : wt w (-f) = wt w f := funext (wt_neg f)
  rw [wn, wn, this]

theorem wt_smul (c : ℝ) (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) : wt w (c • f) α = |c| * wt w f α := by
  simp only [wt, map_smul, smul_eq_mul, abs_mul]; ring

theorem Conv.smul {f : MvPowerSeries σ ℝ} (hf : Conv w f) (c : ℝ) : Conv w (c • f) := by
  have : wt w (c • f) = fun α => |c| * wt w f α := funext (wt_smul c f)
  rw [Conv, this]; exact hf.mul_left _

theorem wt_add_le (hw : ∀ i, 0 ≤ w i) (f g : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) :
    wt w (f + g) α ≤ wt w f α + wt w g α := by
  unfold wt
  rw [map_add, ← add_mul]
  exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (mw_nonneg hw α)

theorem Conv.add (hw : ∀ i, 0 ≤ w i) {f g : MvPowerSeries σ ℝ} (hf : Conv w f) (hg : Conv w g) :
    Conv w (f + g) :=
  Summable.of_nonneg_of_le (wt_nonneg hw _) (wt_add_le hw f g) (Summable.add hf hg)

theorem wn_add_le (hw : ∀ i, 0 ≤ w i) {f g : MvPowerSeries σ ℝ} (hf : Conv w f) (hg : Conv w g) :
    wn w (f + g) ≤ wn w f + wn w g :=
  hasSum_le (wt_add_le hw f g) (Conv.add hw hf hg).hasSum (hf.hasSum.add hg.hasSum)

theorem Conv.sub (hw : ∀ i, 0 ≤ w i) {f g : MvPowerSeries σ ℝ} (hf : Conv w f) (hg : Conv w g) :
    Conv w (f - g) := by
  rw [sub_eq_add_neg]; exact Conv.add hw hf (Conv.neg hg)

theorem wt_mul_le (hw : ∀ i, 0 ≤ w i) (f g : MvPowerSeries σ ℝ) (γ : σ →₀ ℕ) :
    wt w (f * g) γ ≤ ∑ p ∈ Finset.HasAntidiagonal.antidiagonal γ, wt w f p.1 * wt w g p.2 := by
  unfold wt
  rw [coeff_mul]
  calc |∑ p ∈ Finset.HasAntidiagonal.antidiagonal γ, coeff p.1 f * coeff p.2 g| * mw w γ
      ≤ (∑ p ∈ Finset.HasAntidiagonal.antidiagonal γ, |coeff p.1 f * coeff p.2 g|) * mw w γ :=
        mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (mw_nonneg hw γ)
    _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal γ, |coeff p.1 f| * mw w p.1 * (|coeff p.2 g| * mw w p.2) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        rw [← hp, mw_add, abs_mul]; ring

theorem summable_wt_antidiag (hw : ∀ i, 0 ≤ w i) {f g : MvPowerSeries σ ℝ} (hf : Conv w f)
    (hg : Conv w g) :
    Summable fun x : (σ →₀ ℕ) × (σ →₀ ℕ) => wt w f x.1 * wt w g x.2 :=
  Summable.mul_of_nonneg hf hg (Pi.le_def.2 fun α => by simpa using wt_nonneg hw f α)
    (Pi.le_def.2 fun α => by simpa using wt_nonneg hw g α)

theorem Conv.mul (hw : ∀ i, 0 ≤ w i) {f g : MvPowerSeries σ ℝ} (hf : Conv w f) (hg : Conv w g) :
    Conv w (f * g) :=
  Summable.of_nonneg_of_le (wt_nonneg hw _) (wt_mul_le hw f g)
    (summable_sum_mul_antidiagonal_of_summable_mul (summable_wt_antidiag hw hf hg))

theorem wn_mul_le (hw : ∀ i, 0 ≤ w i) {f g : MvPowerSeries σ ℝ} (hf : Conv w f) (hg : Conv w g) :
    wn w (f * g) ≤ wn w f * wn w g := by
  have hS := summable_sum_mul_antidiagonal_of_summable_mul (summable_wt_antidiag hw hf hg)
  rw [wn, wn, wn, Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hf hg
    (summable_wt_antidiag hw hf hg)]
  exact hasSum_le (wt_mul_le hw f g) (Conv.mul hw hf hg).hasSum hS.hasSum

theorem Conv.pow (hw : ∀ i, 0 ≤ w i) {f : MvPowerSeries σ ℝ} (hf : Conv w f) (n : ℕ) :
    Conv w (f ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    have : wt w (1 : MvPowerSeries σ ℝ) = fun α => if α = 0 then 1 else 0 := by
      funext α; by_cases h : α = 0 <;> simp [wt, coeff_one, h, mw_zero]
    rw [Conv, this]
    exact summable_of_ne_finset_zero (s := {0}) (fun α hα => by simp at hα; simp [hα])
  | succ n ih => rw [pow_succ]; exact Conv.mul hw ih hf

/-! ### constants, variables -/

theorem hasSum_wt_C (a : ℝ) : HasSum (wt w (C a : MvPowerSeries σ ℝ)) |a| := by
  have : |a| = wt w (C a : MvPowerSeries σ ℝ) 0 := by simp [wt, mw_zero]
  rw [this]
  exact hasSum_single 0 (fun β hβ => by simp [wt, coeff_C, hβ])

theorem conv_C (a : ℝ) : Conv w (C a : MvPowerSeries σ ℝ) := (hasSum_wt_C a).summable

theorem wn_C (a : ℝ) : wn w (C a : MvPowerSeries σ ℝ) = |a| := (hasSum_wt_C a).tsum_eq

theorem conv_one : Conv w (1 : MvPowerSeries σ ℝ) := by
  simpa using conv_C (w := w) (σ := σ) 1

theorem wn_one : wn w (1 : MvPowerSeries σ ℝ) = 1 := by
  simpa using wn_C (w := w) (σ := σ) 1

theorem hasSum_wt_X (hw : ∀ i, 0 ≤ w i) (i : σ) : HasSum (wt w (X i : MvPowerSeries σ ℝ)) (w i) := by
  have : w i = wt w (X i : MvPowerSeries σ ℝ) (Finsupp.single i 1) := by
    simp [wt, coeff_X, mw_single]
  rw [this]
  exact hasSum_single _ (fun β hβ => by simp [wt, coeff_X, hβ])

theorem conv_X (hw : ∀ i, 0 ≤ w i) (i : σ) : Conv w (X i : MvPowerSeries σ ℝ) :=
  (hasSum_wt_X hw i).summable

theorem wt_mono {w' : σ → ℝ} (hw' : ∀ i, 0 ≤ w' i) (hle : ∀ i, w' i ≤ w i)
    (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) : wt w' f α ≤ wt w f α :=
  mul_le_mul_of_nonneg_left (mw_mono hw' hle α) (abs_nonneg _)

theorem Conv.mono {w' : σ → ℝ} (hw' : ∀ i, 0 ≤ w' i) (hle : ∀ i, w' i ≤ w i)
    {f : MvPowerSeries σ ℝ} (hf : Conv w f) : Conv w' f :=
  Summable.of_nonneg_of_le (wt_nonneg hw' f) (wt_mono hw' hle f) hf

theorem wn_mono {w' : σ → ℝ} (hw' : ∀ i, 0 ≤ w' i) (hle : ∀ i, w' i ≤ w i)
    {f : MvPowerSeries σ ℝ} (hf : Conv w f) : wn w' f ≤ wn w f :=
  hasSum_le (wt_mono hw' hle f) (Conv.mono hw' hle hf).hasSum hf.hasSum

/-- a finite family bound gives `Conv` (partial sums bounded). -/
theorem conv_of_sum_le (hw : ∀ i, 0 ≤ w i) {f : MvPowerSeries σ ℝ} {c : ℝ}
    (h : ∀ s : Finset (σ →₀ ℕ), ∑ α ∈ s, wt w f α ≤ c) : Conv w f :=
  summable_of_sum_le (Pi.le_def.2 fun α => by simpa using wt_nonneg hw f α) h

theorem wn_le_of_sum_le (hw : ∀ i, 0 ≤ w i) {f : MvPowerSeries σ ℝ} {c : ℝ}
    (h : ∀ s : Finset (σ →₀ ℕ), ∑ α ∈ s, wt w f α ≤ c) : wn w f ≤ c :=
  (conv_of_sum_le hw h).tsum_le_of_sum_le h

/-! ### approximation principle, finite sums, powers, inverses -/

/-- if `f` agrees coefficientwise with uniformly bounded convergent approximants, `f` converges. -/
theorem conv_of_approx (hw : ∀ i, 0 ≤ w i) {f : MvPowerSeries σ ℝ} (P : ℕ → MvPowerSeries σ ℝ)
    (D : (σ →₀ ℕ) → ℕ) {B : ℝ} (hP : ∀ N, Conv w (P N)) (hB : ∀ N, wn w (P N) ≤ B)
    (hc : ∀ α N, D α ≤ N → coeff α f = coeff α (P N)) : Conv w f ∧ wn w f ≤ B := by
  have key : ∀ s : Finset (σ →₀ ℕ), ∑ α ∈ s, wt w f α ≤ B := by
    intro s
    have h1 : ∑ α ∈ s, wt w f α = ∑ α ∈ s, wt w (P (s.sup D)) α := by
      refine Finset.sum_congr rfl fun α hα => ?_
      simp only [wt]; rw [hc α (s.sup D) (Finset.le_sup hα)]
    rw [h1]
    exact (sum_le_hasSum s (fun β _ => wt_nonneg hw _ β) (hP _).hasSum).trans (hB _)
  exact ⟨conv_of_sum_le hw key, wn_le_of_sum_le hw key⟩

theorem conv_finset_sum (hw : ∀ i, 0 ≤ w i) {ι : Type*} (s : Finset ι)
    (F : ι → MvPowerSeries σ ℝ) (hF : ∀ i ∈ s, Conv w (F i)) :
    Conv w (∑ i ∈ s, F i) ∧ wn w (∑ i ∈ s, F i) ≤ ∑ i ∈ s, wn w (F i) := by
  classical
  revert hF
  refine Finset.induction_on s ?_ ?_
  · intro _; simp [conv_zero, wn_zero]
  · intro a s ha ih hF
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    have haF := hF a (Finset.mem_insert_self a s)
    exact ⟨Conv.add hw haF hs.1, (wn_add_le hw haF hs.1).trans (by linarith [hs.2])⟩

theorem wn_pow_le (hw : ∀ i, 0 ≤ w i) {h : MvPowerSeries σ ℝ} (hh : Conv w h) (k : ℕ) :
    wn w (h ^ k) ≤ wn w h ^ k := by
  induction k with
  | zero => simp [wn_one]
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (wn_mul_le hw (Conv.pow hw hh k) hh).trans
      (mul_le_mul_of_nonneg_right ih (wn_nonneg hw h))

/-- **convergent inverse**: a series that is a small perturbation of its constant term is a unit
of the convergent algebra, with an explicit bound. -/
theorem conv_inv (hw : ∀ i, 0 ≤ w i) {u : MvPowerSeries σ ℝ} (hu : Conv w u) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hc : constantCoeff u ≠ 0)
    (hq : wn w (u - C (constantCoeff u)) ≤ q * |constantCoeff u|) :
    Conv w u⁻¹ ∧ wn w u⁻¹ ≤ |constantCoeff u|⁻¹ * (1 - q)⁻¹ := by
  set c := constantCoeff u with hcdef
  set h : MvPowerSeries σ ℝ := -(C c⁻¹ * (u - C c)) with hhdef
  have hcpos : 0 < |c| := abs_pos.2 hc
  have hd : Conv w (u - C c) := Conv.sub hw hu (conv_C c)
  have hh : Conv w h := Conv.neg (Conv.mul hw (conv_C _) hd)
  have hwh : wn w h ≤ q := by
    rw [hhdef, wn_neg]
    calc wn w (C c⁻¹ * (u - C c)) ≤ wn w (C c⁻¹ : MvPowerSeries σ ℝ) * wn w (u - C c) :=
          wn_mul_le hw (conv_C _) hd
      _ = |c|⁻¹ * wn w (u - C c) := by rw [wn_C, abs_inv]
      _ ≤ |c|⁻¹ * (q * |c|) := mul_le_mul_of_nonneg_left hq (inv_nonneg.2 (abs_nonneg c))
      _ = q := by field_simp
  have hh0 : constantCoeff h = 0 := by simp [hhdef, hcdef]
  have hu_eq : u = C c * (1 - h) := by
    rw [hhdef, sub_neg_eq_add, mul_add, mul_one, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc,
      map_one, one_mul]
    ring
  have hPN : ∀ N : ℕ, u⁻¹ - C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i = u⁻¹ * h ^ N := by
    intro N
    have h1 : u * (C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i) = 1 - h ^ N := by
      calc u * (C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i)
          = (C c * C c⁻¹) * ((1 - h) * ∑ i ∈ Finset.range N, h ^ i) := by
            rw [hu_eq]; ring
        _ = 1 - h ^ N := by rw [← map_mul, mul_inv_cancel₀ hc, map_one, one_mul, mul_neg_geom_sum]
    calc u⁻¹ - C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i
        = u⁻¹ * (1 - u * (C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i)) := by
          rw [mul_sub, mul_one, ← mul_assoc, MvPowerSeries.inv_mul_cancel u hc, one_mul]
      _ = u⁻¹ * h ^ N := by rw [h1]; ring
  have hcoeff : ∀ α N, Finsupp.degree α + 1 ≤ N →
      coeff α u⁻¹ = coeff α (C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i) := by
    intro α N hN
    have hz : coeff α (u⁻¹ * h ^ N) = 0 := by
      apply coeff_of_lt_order
      calc ((Finsupp.degree α : ℕ) : ℕ∞) < N := by exact_mod_cast (Nat.lt_of_succ_le hN)
        _ ≤ (h ^ N).order := le_order_pow_of_constantCoeff_eq_zero N hh0
        _ ≤ u⁻¹.order + (h ^ N).order := le_add_self
        _ ≤ (u⁻¹ * h ^ N).order := le_order_mul
    have := congrArg (coeff α) (hPN N)
    rw [map_sub, hz, sub_eq_zero] at this
    exact this
  have hPc : ∀ N : ℕ, Conv w (C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i) := fun N =>
    Conv.mul hw (conv_C _) (conv_finset_sum hw _ _ (fun i _ => Conv.pow hw hh i)).1
  have hPB : ∀ N : ℕ, wn w (C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i) ≤ |c|⁻¹ * (1 - q)⁻¹ := by
    intro N
    have hS := conv_finset_sum hw (Finset.range N) (fun i => h ^ i) (fun i _ => Conv.pow hw hh i)
    have hsum : ∑ i ∈ Finset.range N, wn w (h ^ i) ≤ (1 - q)⁻¹ :=
      (Finset.sum_le_sum fun i _ => (wn_pow_le hw hh i).trans
        (pow_le_pow_left₀ (wn_nonneg hw h) hwh i)).trans
        (sum_le_hasSum _ (fun i _ => pow_nonneg hq0 i) (hasSum_geometric_of_lt_one hq0 hq1))
    calc wn w (C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i)
        ≤ wn w (C c⁻¹ : MvPowerSeries σ ℝ) * wn w (∑ i ∈ Finset.range N, h ^ i) :=
          wn_mul_le hw (conv_C _) hS.1
      _ = |c|⁻¹ * wn w (∑ i ∈ Finset.range N, h ^ i) := by rw [wn_C, abs_inv]
      _ ≤ |c|⁻¹ * (1 - q)⁻¹ :=
          mul_le_mul_of_nonneg_left (hS.2.trans hsum) (inv_nonneg.2 (abs_nonneg c))
  exact conv_of_approx hw (fun N => C c⁻¹ * ∑ i ∈ Finset.range N, h ^ i)
    (fun α => Finsupp.degree α + 1) hPc hPB hcoeff

end Conv

end SubanalyticLib

/-! SubanalyticLib L2a (body; prepend L1_Conv.lean): a distinguished variable `y`, the operators
`lowPart d` (`y`-degree `< d`) and `hatPart d` (quotient by `y^d`), and the `x`-order `XOrd`. -/

namespace SubanalyticLib

section Split

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ] (y : σ)

/-- the part of `f` of `y`-degree `< d`. -/
noncomputable def lowPart (d : ℕ) (f : MvPowerSeries σ ℝ) : MvPowerSeries σ ℝ :=
  fun α => if α y < d then coeff α f else 0

/-- the quotient of `f` by `y^d`, dropping the low part. -/
noncomputable def hatPart (d : ℕ) (f : MvPowerSeries σ ℝ) : MvPowerSeries σ ℝ :=
  fun α => coeff (α + Finsupp.single y d) f

theorem coeff_lowPart (d : ℕ) (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) :
    coeff α (lowPart y d f) = if α y < d then coeff α f else 0 := rfl

theorem coeff_hatPart (d : ℕ) (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) :
    coeff α (hatPart y d f) = coeff (α + Finsupp.single y d) f := rfl

theorem hatPart_add (d : ℕ) (f g : MvPowerSeries σ ℝ) :
    hatPart y d (f + g) = hatPart y d f + hatPart y d g := by
  ext α; simp only [coeff_hatPart, map_add]

theorem hatPart_sub (d : ℕ) (f g : MvPowerSeries σ ℝ) :
    hatPart y d (f - g) = hatPart y d f - hatPart y d g := by
  ext α; simp only [coeff_hatPart, map_sub]

theorem hatPart_finset_sum (d : ℕ) {ι : Type*} (s : Finset ι) (F : ι → MvPowerSeries σ ℝ) :
    hatPart y d (∑ i ∈ s, F i) = ∑ i ∈ s, hatPart y d (F i) := by
  ext α; simp only [coeff_hatPart, map_sum]

theorem single_le_iff' (d : ℕ) (α : σ →₀ ℕ) : Finsupp.single y d ≤ α ↔ d ≤ α y :=
  Finsupp.single_le_iff

/-- `f = lowPart + y^d * hatPart`. -/
theorem low_add_hat (d : ℕ) (f : MvPowerSeries σ ℝ) :
    f = lowPart y d f + X y ^ d * hatPart y d f := by
  ext α
  rw [map_add, X_pow_eq, coeff_monomial_mul, coeff_lowPart, coeff_hatPart]
  by_cases h : α y < d
  · have : ¬ Finsupp.single y d ≤ α := by rw [single_le_iff']; omega
    rw [if_pos h, if_neg this, add_zero]
  · have : Finsupp.single y d ≤ α := by rw [single_le_iff']; omega
    rw [if_neg h, if_pos this, zero_add, one_mul, tsub_add_cancel_of_le this]

theorem hatPart_X_pow_mul (d : ℕ) (g : MvPowerSeries σ ℝ) : hatPart y d (X y ^ d * g) = g := by
  ext α
  rw [coeff_hatPart, X_pow_eq, add_comm, coeff_add_monomial_mul, one_mul]

theorem hatPart_lowPart (d : ℕ) (f : MvPowerSeries σ ℝ) : hatPart y d (lowPart y d f) = 0 := by
  ext α
  rw [coeff_hatPart, coeff_lowPart, if_neg]
  · simp
  · simp

theorem lowPart_eq_self_iff (d : ℕ) (f : MvPowerSeries σ ℝ) :
    lowPart y d f = f ↔ hatPart y d f = 0 := by
  constructor
  · intro h; rw [← h, hatPart_lowPart]
  · intro h
    conv_rhs => rw [low_add_hat y d f, h, mul_zero, add_zero]

/-! ### weighted bounds -/

variable {w : σ → ℝ}

theorem wt_lowPart_le (d : ℕ) (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) (hw : ∀ i, 0 ≤ w i) :
    wt w (lowPart y d f) α ≤ wt w f α := by
  unfold wt; rw [coeff_lowPart]; split_ifs
  · exact le_rfl
  · simp only [abs_zero, zero_mul]; exact mul_nonneg (abs_nonneg _) (mw_nonneg hw α)

theorem Conv.low (hw : ∀ i, 0 ≤ w i) (d : ℕ) {f : MvPowerSeries σ ℝ} (hf : Conv w f) :
    Conv w (lowPart y d f) :=
  Summable.of_nonneg_of_le (wt_nonneg hw _) (fun α => wt_lowPart_le y d f α hw) hf

theorem wt_hatPart (d : ℕ) (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) (hy : 0 < w y) :
    wt w (hatPart y d f) α = wt w f (α + Finsupp.single y d) / w y ^ d := by
  unfold wt
  rw [coeff_hatPart, mw_add, mw_single]
  field_simp

theorem Conv.hat (hw : ∀ i, 0 ≤ w i) (hy : 0 < w y) (d : ℕ) {f : MvPowerSeries σ ℝ}
    (hf : Conv w f) : Conv w (hatPart y d f) := by
  have : wt w (hatPart y d f) = fun α => wt w f (α + Finsupp.single y d) / w y ^ d :=
    funext fun α => wt_hatPart y d f α hy
  rw [Conv, this]
  exact (hf.comp_injective (add_left_injective (Finsupp.single y d))).div_const _

theorem wn_hatPart_le (hw : ∀ i, 0 ≤ w i) (hy : 0 < w y) (d : ℕ) {f : MvPowerSeries σ ℝ}
    (hf : Conv w f) : wn w (hatPart y d f) ≤ wn w f / w y ^ d := by
  have : wt w (hatPart y d f) = fun α => wt w f (α + Finsupp.single y d) / w y ^ d :=
    funext fun α => wt_hatPart y d f α hy
  rw [wn, this, tsum_div_const]
  gcongr
  exact tsum_comp_le_tsum_of_inj hf (wt_nonneg hw f) (add_left_injective (Finsupp.single y d))

/-! ### the `x`-degree and `x`-order -/

/-- total degree in the variables other than `y`. -/
def xdeg (α : σ →₀ ℕ) : ℕ := ∑ i ∈ Finset.univ.erase y, α i

theorem xdeg_add (α β : σ →₀ ℕ) : xdeg y (α + β) = xdeg y α + xdeg y β := by
  simp [xdeg, Finset.sum_add_distrib]

theorem xdeg_single (d : ℕ) : xdeg y (Finsupp.single y d) = 0 := by
  unfold xdeg
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finsupp.single_apply, if_neg]
  exact fun h => (Finset.mem_erase.1 hi).1 h.symm

theorem eq_single_of_xdeg_eq_zero {α : σ →₀ ℕ} (h : xdeg y α = 0) :
    α = Finsupp.single y (α y) := by
  ext i
  by_cases hi : i = y
  · subst hi; simp
  · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
    exact (Finset.sum_eq_zero_iff.1 h) i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)

/-- all coefficients of `x`-degree `< m` vanish. -/
def XOrd (m : ℕ) (f : MvPowerSeries σ ℝ) : Prop := ∀ α, xdeg y α < m → coeff α f = 0

theorem XOrd.zero_ord (f : MvPowerSeries σ ℝ) : XOrd y 0 f := fun α h => absurd h (Nat.not_lt_zero _)

theorem XOrd.mono {m m' : ℕ} {f : MvPowerSeries σ ℝ} (hf : XOrd y m f) (h : m' ≤ m) :
    XOrd y m' f := fun α hα => hf α (lt_of_lt_of_le hα h)

theorem XOrd.add {m : ℕ} {f g : MvPowerSeries σ ℝ} (hf : XOrd y m f) (hg : XOrd y m g) :
    XOrd y m (f + g) := fun α hα => by rw [map_add, hf α hα, hg α hα, add_zero]

theorem XOrd.neg {m : ℕ} {f : MvPowerSeries σ ℝ} (hf : XOrd y m f) : XOrd y m (-f) :=
  fun α hα => by rw [map_neg, hf α hα, neg_zero]

theorem XOrd.sub {m : ℕ} {f g : MvPowerSeries σ ℝ} (hf : XOrd y m f) (hg : XOrd y m g) :
    XOrd y m (f - g) := fun α hα => by rw [map_sub, hf α hα, hg α hα, sub_zero]

theorem XOrd.zero (m : ℕ) : XOrd y m (0 : MvPowerSeries σ ℝ) := fun α _ => by simp

theorem XOrd.mul {m n : ℕ} {f g : MvPowerSeries σ ℝ} (hf : XOrd y m f) (hg : XOrd y n g) :
    XOrd y (m + n) (f * g) := fun α hα => by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  have : xdeg y p.1 + xdeg y p.2 < m + n := by rw [← xdeg_add, hp]; exact hα
  by_cases h1 : xdeg y p.1 < m
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]

theorem XOrd.hat {m : ℕ} (d : ℕ) {f : MvPowerSeries σ ℝ} (hf : XOrd y m f) :
    XOrd y m (hatPart y d f) := fun α hα => by
  rw [coeff_hatPart]; exact hf _ (by rw [xdeg_add, xdeg_single, add_zero]; exact hα)

/-- the low part of a series regular of order `d` in `y` has positive `x`-order. -/
theorem XOrd.lowPart_of_regular (d : ℕ) {f : MvPowerSeries σ ℝ}
    (hreg : ∀ j < d, coeff (Finsupp.single y j) f = 0) : XOrd y 1 (lowPart y d f) := by
  intro α hα
  rw [coeff_lowPart]
  split_ifs with h
  · rw [eq_single_of_xdeg_eq_zero y (by omega : xdeg y α = 0)]
    exact hreg _ h
  · rfl

end Split

end SubanalyticLib

/-! SubanalyticLib L2b (body; prepend L12.lean): **convergent Weierstrass division**.
Neumann series `W = Σ_k (-T)^k ĝ`, `T v = hatPart d (v*h)`, `h = u⁻¹ * lowPart d f`; it is
coefficientwise finite because `T` raises the `x`-order, and converges by `conv_of_approx`. -/

namespace SubanalyticLib

section Div

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ] (y : σ)

/-- `v ↦ -(hatPart d (v*h))`. -/
noncomputable def divOp (d : ℕ) (h v : MvPowerSeries σ ℝ) : MvPowerSeries σ ℝ :=
  -(hatPart y d (v * h))

/-- Neumann terms. -/
noncomputable def nterm (d : ℕ) (h g0 : MvPowerSeries σ ℝ) (k : ℕ) : MvPowerSeries σ ℝ :=
  (divOp y d h)^[k] g0

/-- Neumann partial sums. -/
noncomputable def npart (d : ℕ) (h g0 : MvPowerSeries σ ℝ) (N : ℕ) : MvPowerSeries σ ℝ :=
  ∑ k ∈ Finset.range N, nterm y d h g0 k

/-- the Neumann solution, read coefficientwise from a long enough partial sum. -/
noncomputable def nsol (d : ℕ) (h g0 : MvPowerSeries σ ℝ) : MvPowerSeries σ ℝ :=
  fun α => coeff α (npart y d h g0 (xdeg y α + 1))

theorem nterm_zero (d : ℕ) (h g0 : MvPowerSeries σ ℝ) : nterm y d h g0 0 = g0 := rfl

theorem nterm_succ (d : ℕ) (h g0 : MvPowerSeries σ ℝ) (k : ℕ) :
    nterm y d h g0 (k + 1) = divOp y d h (nterm y d h g0 k) :=
  Function.iterate_succ_apply' _ _ _

theorem divOp_sub (d : ℕ) (h a b : MvPowerSeries σ ℝ) :
    divOp y d h a - divOp y d h b = divOp y d h (a - b) := by
  simp only [divOp, sub_mul, hatPart_sub]; ring

theorem divOp_finset_sum (d : ℕ) (h : MvPowerSeries σ ℝ) {ι : Type*} (s : Finset ι)
    (F : ι → MvPowerSeries σ ℝ) : divOp y d h (∑ i ∈ s, F i) = ∑ i ∈ s, divOp y d h (F i) := by
  simp only [divOp, Finset.sum_mul, hatPart_finset_sum, Finset.sum_neg_distrib]

theorem XOrd.divOp {d m : ℕ} {h v : MvPowerSeries σ ℝ} (hh : XOrd y 1 h) (hv : XOrd y m v) :
    XOrd y (m + 1) (divOp y d h v) :=
  (XOrd.hat y d (XOrd.mul y hv hh)).neg y

theorem XOrd_nterm (d : ℕ) {h : MvPowerSeries σ ℝ} (hh : XOrd y 1 h) (g0 : MvPowerSeries σ ℝ) :
    ∀ k, XOrd y k (nterm y d h g0 k)
  | 0 => XOrd.zero_ord y _
  | k + 1 => by rw [nterm_succ]; exact XOrd.divOp y hh (XOrd_nterm d hh g0 k)

variable {w : σ → ℝ}

theorem conv_divOp (hw : ∀ i, 0 ≤ w i) (hy : 0 < w y) (d : ℕ) {h v : MvPowerSeries σ ℝ}
    (hh : Conv w h) (hv : Conv w v) :
    Conv w (divOp y d h v) ∧ wn w (divOp y d h v) ≤ wn w h / w y ^ d * wn w v := by
  have hvh : Conv w (v * h) := Conv.mul hw hv hh
  refine ⟨Conv.neg (Conv.hat y hw hy d hvh), ?_⟩
  rw [divOp, wn_neg]
  calc wn w (hatPart y d (v * h)) ≤ wn w (v * h) / w y ^ d := wn_hatPart_le y hw hy d hvh
    _ ≤ wn w v * wn w h / w y ^ d := by
        gcongr; exact wn_mul_le hw hv hh
    _ = wn w h / w y ^ d * wn w v := by ring

theorem conv_nterm (hw : ∀ i, 0 ≤ w i) (hy : 0 < w y) (d : ℕ) {h g0 : MvPowerSeries σ ℝ}
    (hh : Conv w h) (hg : Conv w g0) :
    ∀ k, Conv w (nterm y d h g0 k) ∧
      wn w (nterm y d h g0 k) ≤ (wn w h / w y ^ d) ^ k * wn w g0
  | 0 => by simp only [nterm_zero, pow_zero, one_mul]; exact ⟨hg, le_rfl⟩
  | k + 1 => by
    obtain ⟨hc, hb⟩ := conv_nterm hw hy d hh hg k
    obtain ⟨hc', hb'⟩ := conv_divOp y hw hy d hh hc
    rw [nterm_succ]
    refine ⟨hc', hb'.trans ?_⟩
    rw [pow_succ]
    have hθ : 0 ≤ wn w h / w y ^ d := div_nonneg (wn_nonneg hw h) (pow_nonneg hy.le d)
    calc wn w h / w y ^ d * wn w (nterm y d h g0 k)
        ≤ wn w h / w y ^ d * ((wn w h / w y ^ d) ^ k * wn w g0) :=
          mul_le_mul_of_nonneg_left hb hθ
      _ = (wn w h / w y ^ d) ^ k * (wn w h / w y ^ d) * wn w g0 := by ring

theorem coeff_npart_stable (d : ℕ) {h : MvPowerSeries σ ℝ} (hh : XOrd y 1 h)
    (g0 : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) :
    ∀ N, xdeg y α + 1 ≤ N →
      coeff α (npart y d h g0 N) = coeff α (npart y d h g0 (xdeg y α + 1)) := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => rfl
  | succ N hN ih =>
    rw [npart, Finset.sum_range_succ, map_add, ← npart, ih,
      XOrd_nterm y d hh g0 N α (by omega), add_zero]

theorem coeff_nsol (d : ℕ) {h : MvPowerSeries σ ℝ} (hh : XOrd y 1 h) (g0 : MvPowerSeries σ ℝ)
    (α : σ →₀ ℕ) (N : ℕ) (hN : xdeg y α + 1 ≤ N) :
    coeff α (nsol y d h g0) = coeff α (npart y d h g0 N) :=
  (coeff_npart_stable y d hh g0 α N hN).symm

theorem conv_nsol (hw : ∀ i, 0 ≤ w i) (hy : 0 < w y) (d : ℕ) {h g0 : MvPowerSeries σ ℝ}
    (hh : Conv w h) (hhx : XOrd y 1 h) (hg : Conv w g0) (hθ : wn w h / w y ^ d < 1) :
    Conv w (nsol y d h g0) ∧ wn w (nsol y d h g0) ≤ wn w g0 * (1 - wn w h / w y ^ d)⁻¹ := by
  have hθ0 : 0 ≤ wn w h / w y ^ d := div_nonneg (wn_nonneg hw h) (pow_nonneg hy.le d)
  have hP : ∀ N, Conv w (npart y d h g0 N) ∧
      wn w (npart y d h g0 N) ≤ ∑ k ∈ Finset.range N, wn w (nterm y d h g0 k) := fun N =>
    conv_finset_sum hw _ _ (fun k _ => (conv_nterm y hw hy d hh hg k).1)
  refine conv_of_approx hw (npart y d h g0) (fun α => xdeg y α + 1) (fun N => (hP N).1)
    (fun N => ?_) (fun α N hN => coeff_nsol y d hhx g0 α N hN)
  refine (hP N).2.trans ?_
  calc ∑ k ∈ Finset.range N, wn w (nterm y d h g0 k)
      ≤ ∑ k ∈ Finset.range N, (wn w h / w y ^ d) ^ k * wn w g0 :=
        Finset.sum_le_sum fun k _ => (conv_nterm y hw hy d hh hg k).2
    _ = wn w g0 * ∑ k ∈ Finset.range N, (wn w h / w y ^ d) ^ k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ wn w g0 * (1 - wn w h / w y ^ d)⁻¹ :=
        mul_le_mul_of_nonneg_left
          (sum_le_hasSum _ (fun i _ => pow_nonneg hθ0 i) (hasSum_geometric_of_lt_one hθ0 hθ))
          (wn_nonneg hw g0)

/-- the Neumann solution solves `W + hatPart d (W*h) = g0`. -/
theorem nsol_fixed (d : ℕ) {h : MvPowerSeries σ ℝ} (hh : XOrd y 1 h) (g0 : MvPowerSeries σ ℝ) :
    nsol y d h g0 + hatPart y d (nsol y d h g0 * h) = g0 := by
  ext α
  set N := xdeg y α + 1 with hNdef
  have hX : XOrd y N (nsol y d h g0 - npart y d h g0 N) := by
    intro β hβ
    rw [map_sub, coeff_nsol y d hh g0 β N (by omega), sub_self]
  have h1 : coeff α (divOp y d h (nsol y d h g0)) = coeff α (divOp y d h (npart y d h g0 N)) := by
    have := XOrd.divOp y (d := d) hh hX α (by omega)
    rw [← divOp_sub, map_sub, sub_eq_zero] at this
    exact this
  have h2 : npart y d h g0 N - divOp y d h (npart y d h g0 N) = g0 - nterm y d h g0 N := by
    rw [npart, divOp_finset_sum]
    simp_rw [← nterm_succ]
    rw [← Finset.sum_sub_distrib, Finset.sum_range_sub', nterm_zero]
  have h3 : coeff α (nterm y d h g0 N) = 0 := XOrd_nterm y d hh g0 N α (by omega)
  have key : coeff α (nsol y d h g0 - divOp y d h (nsol y d h g0)) = coeff α g0 := by
    rw [map_sub, h1, coeff_nsol y d hh g0 α N le_rfl, ← map_sub, h2, map_sub, h3, sub_zero]
  rw [divOp, sub_neg_eq_add] at key
  exact key

/-- **Convergent Weierstrass division** (polyradius form).  If `f` is regular of order `d` in `y`
and the polyradius `w` is small enough that `u = hatPart d f` has a convergent inverse and
`‖u⁻¹ * lowPart d f‖_w < w_y^d`, then every convergent `g` is `q*f + r` with `q, r`
convergent and `r` of `y`-degree `< d`. -/
theorem weierstrass_div_conv (hw : ∀ i, 0 ≤ w i) (hy : 0 < w y) (d : ℕ)
    {f g : MvPowerSeries σ ℝ} (hf : Conv w f) (hg : Conv w g)
    (hreg : ∀ j < d, coeff (Finsupp.single y j) f = 0)
    (hd : coeff (Finsupp.single y d) f ≠ 0) (hu : Conv w (hatPart y d f)⁻¹)
    (hθ : wn w ((hatPart y d f)⁻¹ * lowPart y d f) < w y ^ d) :
    ∃ q r : MvPowerSeries σ ℝ, Conv w q ∧ Conv w r ∧ hatPart y d r = 0 ∧ g = q * f + r := by
  set u := hatPart y d f with hudef
  set h := u⁻¹ * lowPart y d f with hhdef
  have hcu : constantCoeff u ≠ 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hudef, coeff_hatPart, zero_add]; exact hd
  have hh : Conv w h := Conv.mul hw hu (Conv.low y hw d hf)
  have hhx : XOrd y 1 h := by
    have := XOrd.mul y (XOrd.zero_ord y u⁻¹) (XOrd.lowPart_of_regular y d hreg)
    rw [zero_add] at this; exact this
  have hθ' : wn w h / w y ^ d < 1 := by
    rw [div_lt_one (pow_pos hy d)]; exact hθ
  set W := nsol y d h (hatPart y d g) with hWdef
  have hW := conv_nsol y hw hy d hh hhx (Conv.hat y hw hy d hg) hθ'
  refine ⟨W * u⁻¹, g - W * u⁻¹ * f, Conv.mul hw hW.1 hu,
    Conv.sub hw hg (Conv.mul hw (Conv.mul hw hW.1 hu) hf), ?_, by ring⟩
  have hqf : W * u⁻¹ * f = W * h + X y ^ d * W := by
    conv_lhs => rw [low_add_hat y d f]
    rw [← hudef, hhdef]
    have : u⁻¹ * u = 1 := MvPowerSeries.inv_mul_cancel u hcu
    calc W * u⁻¹ * (lowPart y d f + X y ^ d * u)
        = W * (u⁻¹ * lowPart y d f) + X y ^ d * W * (u⁻¹ * u) := by ring
      _ = W * (u⁻¹ * lowPart y d f) + X y ^ d * W := by rw [this, mul_one]
  have hfix : W + hatPart y d (W * h) = hatPart y d g := nsol_fixed y d hhx _
  rw [hatPart_sub, hqf, hatPart_add, hatPart_X_pow_mul, ← hfix]
  ring

end Div

end SubanalyticLib

/-! SubanalyticLib L2c (body; prepend L2.lean): choosing the polyradius for Weierstrass division. -/

namespace SubanalyticLib

section Radius

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- scale the radii indexed by `S` by the factor `τ`. -/
noncomputable def scaleW (S : Finset σ) (τ : ℝ) (w : σ → ℝ) (i : σ) : ℝ :=
  if i ∈ S then τ * w i else w i

/-- partial degree in the variables of `S`. -/
def sdeg (S : Finset σ) (α : σ →₀ ℕ) : ℕ := ∑ i ∈ S, α i

theorem mw_scaleW (S : Finset σ) (τ : ℝ) (w : σ → ℝ) (α : σ →₀ ℕ) :
    mw (scaleW S τ w) α = τ ^ sdeg S α * mw w α := by
  unfold mw scaleW sdeg
  have : ∀ i ∈ (Finset.univ : Finset σ),
      (if i ∈ S then τ * w i else w i) ^ α i = (if i ∈ S then τ ^ α i else 1) * w i ^ α i := by
    intro i _; split_ifs <;> simp [mul_pow]
  rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_ite_mem,
    Finset.univ_inter, Finset.prod_pow_eq_pow_sum]

theorem scaleW_le {S : Finset σ} {τ : ℝ} {w : σ → ℝ} (hw : ∀ i, 0 ≤ w i) (hτ : τ ≤ 1) (i : σ) :
    scaleW S τ w i ≤ w i := by
  unfold scaleW; split_ifs
  · exact mul_le_of_le_one_left (hw i) hτ
  · exact le_rfl

theorem conv_scale {w : σ → ℝ} (hw : ∀ i, 0 ≤ w i) (S : Finset σ) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (hτ1 : τ ≤ 1) {f : MvPowerSeries σ ℝ} (hf : Conv w f)
    (hz : ∀ α, sdeg S α = 0 → coeff α f = 0) :
    Conv (scaleW S τ w) f ∧ wn (scaleW S τ w) f ≤ τ * wn w f := by
  have hnn : ∀ i, 0 ≤ scaleW S τ w i := fun i => by
    unfold scaleW; split_ifs
    · exact mul_nonneg hτ0 (hw i)
    · exact hw i
  have hle : ∀ α, wt (scaleW S τ w) f α ≤ τ * wt w f α := by
    intro α
    unfold wt; rw [mw_scaleW]
    by_cases h : sdeg S α = 0
    · rw [hz α h]; simp
    · calc |coeff α f| * (τ ^ sdeg S α * mw w α) ≤ |coeff α f| * (τ * mw w α) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (pow_le_of_le_one hτ0 hτ1 h) (mw_nonneg hw α))
              (abs_nonneg _)
        _ = τ * (|coeff α f| * mw w α) := by ring
  have hc : Conv (scaleW S τ w) f :=
    Summable.of_nonneg_of_le (wt_nonneg hnn f) hle (hf.mul_left τ)
  exact ⟨hc, hasSum_le hle hc.hasSum (hf.hasSum.mul_left τ)⟩

/-- **radius choice**: a series regular of order `d` in `y`, convergent on some polydisc, satisfies
the hypotheses of `weierstrass_div_conv` on a smaller polydisc. -/
theorem exists_radius_div (y : σ) {w0 : σ → ℝ} (hw0 : ∀ i, 0 < w0 i) (d : ℕ)
    {f : MvPowerSeries σ ℝ} (hf : Conv w0 f) (hreg : ∀ j < d, coeff (Finsupp.single y j) f = 0)
    (hd : coeff (Finsupp.single y d) f ≠ 0) :
    ∃ w : σ → ℝ, (∀ i, 0 < w i) ∧ (∀ i, w i ≤ w0 i) ∧ Conv w (hatPart y d f)⁻¹ ∧
      wn w ((hatPart y d f)⁻¹ * lowPart y d f) < w y ^ d := by
  have hw0' : ∀ i, 0 ≤ w0 i := fun i => (hw0 i).le
  set u := hatPart y d f with hudef
  have hu0 : Conv w0 u := Conv.hat y hw0' (hw0 y) d hf
  set c := constantCoeff u with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef, ← coeff_zero_eq_constantCoeff_apply, hudef, coeff_hatPart, zero_add]; exact hd
  have hcpos : 0 < |c| := abs_pos.2 hc
  set A := wn w0 (u - C c) with hAdef
  have hA : 0 ≤ A := wn_nonneg hw0' _
  set t := min 1 (|c| / (2 * (A + 1))) with htdef
  have ht0 : 0 < t := lt_min one_pos (div_pos hcpos (by linarith))
  have ht1 : t ≤ 1 := min_le_left _ _
  have htA : t * A ≤ 1 / 2 * |c| := by
    have : t ≤ |c| / (2 * (A + 1)) := min_le_right _ _
    calc t * A ≤ |c| / (2 * (A + 1)) * A := mul_le_mul_of_nonneg_right this hA
      _ ≤ 1 / 2 * |c| := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        have e : 1 / 2 * |c| * (2 * (A + 1)) = |c| * A + |c| := by ring
        linarith
  set w1 := scaleW Finset.univ t w0 with hw1def
  have hw1pos : ∀ i, 0 < w1 i := fun i => by
    simp only [hw1def, scaleW, Finset.mem_univ, if_true]; exact mul_pos ht0 (hw0 i)
  have hw1' : ∀ i, 0 ≤ w1 i := fun i => (hw1pos i).le
  have hw1le : ∀ i, w1 i ≤ w0 i := fun i => scaleW_le hw0' ht1 i
  have hv := conv_scale hw0' Finset.univ ht0.le ht1 (Conv.sub hw0' hu0 (conv_C c)) (by
    intro α hα
    have h0 : α = 0 := by
      ext i
      have := (Finset.sum_eq_zero_iff.1 hα) i (Finset.mem_univ i)
      simpa using this
    subst h0
    simp [coeff_zero_eq_constantCoeff_apply, hcdef])
  have hu1 : Conv w1 u := Conv.mono hw1' hw1le hu0
  obtain ⟨hinv, hinvB⟩ := conv_inv hw1' hu1 (q := 1 / 2) (by norm_num) (by norm_num) hc
    (hv.2.trans htA)
  set K := |c|⁻¹ * (1 - 1 / 2 : ℝ)⁻¹ with hKdef
  have hK : 0 ≤ K := by positivity
  have hlow1 : Conv w1 (lowPart y d f) := Conv.mono hw1' hw1le (Conv.low y hw0' d hf)
  set L := wn w1 (lowPart y d f) with hLdef
  have hL : 0 ≤ L := wn_nonneg hw1' _
  set s := w1 y with hsdef
  have hs : 0 < s := hw1pos y
  have hKL : 0 ≤ K * L := mul_nonneg hK hL
  set τ := min 1 (s ^ d / (2 * (K * L + 1))) with hτdef
  have hτ0 : 0 < τ := lt_min one_pos (div_pos (pow_pos hs d) (by linarith))
  have hτ1 : τ ≤ 1 := min_le_left _ _
  set w2 := scaleW (Finset.univ.erase y) τ w1 with hw2def
  have hw2pos : ∀ i, 0 < w2 i := fun i => by
    simp only [hw2def, scaleW]; split_ifs
    · exact mul_pos hτ0 (hw1pos i)
    · exact hw1pos i
  have hw2' : ∀ i, 0 ≤ w2 i := fun i => (hw2pos i).le
  have hw2le : ∀ i, w2 i ≤ w1 i := fun i => scaleW_le hw1' hτ1 i
  have hw2y : w2 y = s := by simp [hw2def, scaleW, hsdef]
  have hlow2 := conv_scale hw1' (Finset.univ.erase y) hτ0.le hτ1 hlow1
    (fun α hα => XOrd.lowPart_of_regular y d hreg α (by
      have : xdeg y α = 0 := hα
      omega))
  have hinv2 : Conv w2 u⁻¹ := Conv.mono hw2' hw2le hinv
  have hinv2B : wn w2 u⁻¹ ≤ K := (wn_mono hw2' hw2le hinv).trans hinvB
  refine ⟨w2, hw2pos, fun i => (hw2le i).trans (hw1le i), hinv2, ?_⟩
  rw [hw2y]
  have hsd : 0 < s ^ d := pow_pos hs d
  have h1 : τ ≤ s ^ d / (2 * (K * L + 1)) := min_le_right _ _
  have h2 : K * (τ * L) ≤ K * L * (s ^ d / (2 * (K * L + 1))) := by
    calc K * (τ * L) = K * L * τ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hKL
  have h3 : K * L * (s ^ d / (2 * (K * L + 1))) < s ^ d := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    have e : s ^ d * (2 * (K * L + 1)) = K * L * s ^ d + (K * L * s ^ d + 2 * s ^ d) := by ring
    have h0 : 0 ≤ K * L * s ^ d := mul_nonneg hKL hsd.le
    linarith
  calc wn w2 (u⁻¹ * lowPart y d f) ≤ wn w2 u⁻¹ * wn w2 (lowPart y d f) :=
        wn_mul_le hw2' hinv2 hlow2.1
    _ ≤ K * (τ * L) := mul_le_mul hinv2B hlow2.2 (wn_nonneg hw2' _) hK
    _ < s ^ d := lt_of_le_of_lt h2 h3

end Radius

end SubanalyticLib

/-! SubanalyticLib L2d (body; prepend L2R.lean): convergent Weierstrass division (clean form) and
**convergent Weierstrass preparation** `X_y^d = q*f + r`, `q` a unit, `r` of `y`-degree `< d`
with `r(0,y) = 0`. -/

namespace SubanalyticLib

section Prep

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ] (y : σ)

/-- **Weierstrass division, convergent form**. -/
theorem weierstrass_division (y : σ) {w0 : σ → ℝ} (hw0 : ∀ i, 0 < w0 i) (d : ℕ)
    {f : MvPowerSeries σ ℝ} (hf : Conv w0 f) (hreg : ∀ j < d, coeff (Finsupp.single y j) f = 0)
    (hd : coeff (Finsupp.single y d) f ≠ 0) :
    ∃ w : σ → ℝ, (∀ i, 0 < w i) ∧ (∀ i, w i ≤ w0 i) ∧
      ∀ g : MvPowerSeries σ ℝ, Conv w g →
        ∃ q r : MvPowerSeries σ ℝ, Conv w q ∧ Conv w r ∧ hatPart y d r = 0 ∧ g = q * f + r := by
  obtain ⟨w, hwpos, hwle, hu, hθ⟩ := exists_radius_div y hw0 d hf hreg hd
  have hw' : ∀ i, 0 ≤ w i := fun i => (hwpos i).le
  exact ⟨w, hwpos, hwle, fun g hg =>
    weierstrass_div_conv y hw' (hwpos y) d (Conv.mono hw' hwle hf) hg hreg hd hu hθ⟩

theorem eq_single_of_le_single {γ : σ →₀ ℕ} {j : ℕ} (h : γ ≤ Finsupp.single y j) :
    γ = Finsupp.single y (γ y) := by
  ext i
  by_cases hi : i = y
  · subst hi; simp
  · have := Finsupp.le_def.1 h i
    rw [Finsupp.single_apply, if_neg (Ne.symm hi)] at this ⊢
    omega

/-- pure-`y` coefficients of `q*f` for `f` regular of order `d` in `y`. -/
theorem coeff_single_mul_regular (d : ℕ) {q f : MvPowerSeries σ ℝ}
    (hreg : ∀ j < d, coeff (Finsupp.single y j) f = 0) (j : ℕ) (hj : j ≤ d) :
    coeff (Finsupp.single y j) (q * f) =
      if j = d then constantCoeff q * coeff (Finsupp.single y d) f else 0 := by
  rw [coeff_mul]
  have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal (Finsupp.single y j),
      p ≠ (0, Finsupp.single y j) → coeff p.1 q * coeff p.2 f = 0 := by
    intro p hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hle : p.2 ≤ Finsupp.single y j := hp ▸ le_add_self
    have h2 := eq_single_of_le_single y hle
    have hk : p.2 y ≤ j := by have := Finsupp.le_def.1 hle y; simpa using this
    by_cases hk' : p.2 y < d
    · rw [h2, hreg _ hk', mul_zero]
    · exfalso; apply hne
      have hpj : p.2 = Finsupp.single y j := by rw [h2]; congr 1; omega
      have hp1 : p.1 = 0 := by
        rw [hpj] at hp; exact add_right_cancel (hp.trans (zero_add _).symm)
      exact Prod.ext hp1 hpj
  rw [Finset.sum_eq_single (0, Finsupp.single y j) hterm
    (fun h => absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (zero_add _)) h)]
  dsimp only
  rw [coeff_zero_eq_constantCoeff_apply]
  split_ifs with hjd
  · subst hjd; rfl
  · rw [hreg j (lt_of_le_of_ne hj hjd), mul_zero]

/-- **Weierstrass preparation, convergent form**: `X_y^d = q*f + r` with `q` a unit and
`r` a polynomial in `y` of degree `< d` whose coefficients vanish at `x = 0`. -/
theorem weierstrass_prep (y : σ) {w0 : σ → ℝ} (hw0 : ∀ i, 0 < w0 i) (d : ℕ)
    {f : MvPowerSeries σ ℝ} (hf : Conv w0 f) (hreg : ∀ j < d, coeff (Finsupp.single y j) f = 0)
    (hd : coeff (Finsupp.single y d) f ≠ 0) :
    ∃ w : σ → ℝ, (∀ i, 0 < w i) ∧ (∀ i, w i ≤ w0 i) ∧
      ∃ q r : MvPowerSeries σ ℝ, Conv w q ∧ Conv w r ∧ hatPart y d r = 0 ∧
        constantCoeff q ≠ 0 ∧ (∀ j < d, coeff (Finsupp.single y j) r = 0) ∧
        X y ^ d = q * f + r := by
  obtain ⟨w, hwpos, hwle, hdiv⟩ := weierstrass_division y hw0 d hf hreg hd
  have hw' : ∀ i, 0 ≤ w i := fun i => (hwpos i).le
  obtain ⟨q, r, hq, hr, hr0, heq⟩ := hdiv (X y ^ d) (Conv.pow hw' (conv_X hw' y) d)
  refine ⟨w, hwpos, hwle, q, r, hq, hr, hr0, ?_, ?_, heq⟩
  · have h := congrArg (coeff (Finsupp.single y d)) heq
    rw [map_add, coeff_single_mul_regular y d hreg d le_rfl, if_pos rfl] at h
    have hrd : coeff (Finsupp.single y d) r = 0 := by
      have := congrArg (coeff (Finsupp.single y d)) ((lowPart_eq_self_iff y d r).2 hr0)
      rw [coeff_lowPart, if_neg (by simp)] at this; exact this.symm
    rw [hrd, add_zero, X_pow_eq, coeff_monomial_same] at h
    intro hq0; rw [hq0, zero_mul] at h; exact one_ne_zero h
  · intro j hj
    have h := congrArg (coeff (Finsupp.single y j)) heq
    rw [map_add, coeff_single_mul_regular y d hreg j hj.le, if_neg hj.ne, zero_add, X_pow_eq,
      coeff_monomial, if_neg] at h
    · exact h.symm
    · intro he
      exact absurd (by simpa using congrArg (fun z => z y) he) hj.ne

end Prep

end SubanalyticLib

/-! SubanalyticLib L1b (body; prepend L2P.lean or L1_Conv.lean): evaluating convergent power series
on the closed polydisc; `ev` is a ring homomorphism there. -/

namespace SubanalyticLib

section Eval

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- the monomial `x^α`. -/
def mon (x : σ → ℝ) (α : σ →₀ ℕ) : ℝ := ∏ i, x i ^ α i

/-- evaluation of a power series (meaningful where it converges absolutely). -/
noncomputable def ev (f : MvPowerSeries σ ℝ) (x : σ → ℝ) : ℝ := ∑' α, coeff α f * mon x α

theorem mon_add (x : σ → ℝ) (α β : σ →₀ ℕ) : mon x (α + β) = mon x α * mon x β := by
  simp [mon, pow_add, Finset.prod_mul_distrib]

theorem mon_zero (x : σ → ℝ) : mon x 0 = 1 := by simp [mon]

theorem mon_single (x : σ → ℝ) (i : σ) (k : ℕ) : mon x (Finsupp.single i k) = x i ^ k := by
  unfold mon
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem abs_mon_le {w x : σ → ℝ} (hx : ∀ i, |x i| ≤ w i) (α : σ →₀ ℕ) : |mon x α| ≤ mw w α := by
  unfold mon mw
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun i _ => abs_nonneg _)
    (fun i _ => by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hx i) _)

variable {w : σ → ℝ}

theorem norm_term_le {x : σ → ℝ} (hx : ∀ i, |x i| ≤ w i) (f : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) :
    ‖coeff α f * mon x α‖ ≤ wt w f α := by
  rw [Real.norm_eq_abs, abs_mul, wt]
  exact mul_le_mul_of_nonneg_left (abs_mon_le hx α) (abs_nonneg _)

theorem summable_norm_term {x : σ → ℝ} (hx : ∀ i, |x i| ≤ w i) {f : MvPowerSeries σ ℝ}
    (hf : Conv w f) : Summable fun α => ‖coeff α f * mon x α‖ :=
  Summable.of_nonneg_of_le (fun α => norm_nonneg _) (norm_term_le hx f) hf

theorem summable_term {x : σ → ℝ} (hx : ∀ i, |x i| ≤ w i) {f : MvPowerSeries σ ℝ}
    (hf : Conv w f) : Summable fun α => coeff α f * mon x α :=
  (summable_norm_term hx hf).of_norm

theorem abs_ev_le {x : σ → ℝ} (hx : ∀ i, |x i| ≤ w i) {f : MvPowerSeries σ ℝ} (hf : Conv w f) :
    |ev f x| ≤ wn w f := by
  rw [← Real.norm_eq_abs, ev, wn]
  exact (norm_tsum_le_tsum_norm (summable_norm_term hx hf)).trans
    (hasSum_le (norm_term_le hx f) (summable_norm_term hx hf).hasSum hf.hasSum)

theorem ev_add {x : σ → ℝ} (hx : ∀ i, |x i| ≤ w i) {f g : MvPowerSeries σ ℝ} (hf : Conv w f)
    (hg : Conv w g) : ev (f + g) x = ev f x + ev g x := by
  unfold ev
  rw [← ((summable_term hx hf).hasSum.add (summable_term hx hg).hasSum).tsum_eq]
  congr 1; funext α; rw [map_add, add_mul]

theorem ev_neg (f : MvPowerSeries σ ℝ) (x : σ → ℝ) : ev (-f) x = -ev f x := by
  unfold ev; rw [← tsum_neg]; congr 1; funext α; rw [map_neg, neg_mul]

theorem ev_sub {x : σ → ℝ} (hx : ∀ i, |x i| ≤ w i) {f g : MvPowerSeries σ ℝ} (hf : Conv w f)
    (hg : Conv w g) : ev (f - g) x = ev f x - ev g x := by
  rw [sub_eq_add_neg, ev_add hx hf (Conv.neg hg), ev_neg, ← sub_eq_add_neg]

theorem ev_smul (c : ℝ) (f : MvPowerSeries σ ℝ) (x : σ → ℝ) : ev (c • f) x = c * ev f x := by
  unfold ev; rw [← tsum_mul_left]; congr 1; funext α; rw [map_smul, smul_eq_mul, mul_assoc]

theorem ev_C (a : ℝ) (x : σ → ℝ) : ev (C a : MvPowerSeries σ ℝ) x = a := by
  unfold ev
  rw [tsum_eq_single 0 (fun β hβ => by simp [coeff_C, hβ])]
  simp [coeff_C, mon_zero]

theorem ev_one (x : σ → ℝ) : ev (1 : MvPowerSeries σ ℝ) x = 1 := by
  simpa using ev_C (σ := σ) 1 x

theorem ev_X (i : σ) (x : σ → ℝ) : ev (X i : MvPowerSeries σ ℝ) x = x i := by
  unfold ev
  rw [tsum_eq_single (Finsupp.single i 1) (fun β hβ => by simp [coeff_X, hβ])]
  simp [coeff_X, mon_single]

theorem ev_mul {x : σ → ℝ} (hx : ∀ i, |x i| ≤ w i) (hw : ∀ i, 0 ≤ w i)
    {f g : MvPowerSeries σ ℝ} (hf : Conv w f) (hg : Conv w g) :
    ev (f * g) x = ev f x * ev g x := by
  have h1 : Summable (fun α => coeff α f * mon x α) := summable_term hx hf
  have h2 : Summable (fun α => coeff α g * mon x α) := summable_term hx hg
  have h12 : Summable (fun p : (σ →₀ ℕ) × (σ →₀ ℕ) =>
      (coeff p.1 f * mon x p.1) * (coeff p.2 g * mon x p.2)) :=
    summable_mul_of_summable_norm (f := fun α => coeff α f * mon x α)
      (g := fun α => coeff α g * mon x α) (summable_norm_term hx hf) (summable_norm_term hx hg)
  have key := Summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal h1 h2 h12
  unfold ev
  rw [key]
  congr 1; funext γ
  rw [coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, mon_add]; ring

theorem ev_pow {x : σ → ℝ} (hx : ∀ i, |x i| ≤ w i) (hw : ∀ i, 0 ≤ w i)
    {f : MvPowerSeries σ ℝ} (hf : Conv w f) (n : ℕ) : ev (f ^ n) x = ev f x ^ n := by
  induction n with
  | zero => simp [ev_one]
  | succ n ih => rw [pow_succ, ev_mul hx hw (Conv.pow hw hf n) hf, ih, pow_succ]

theorem ev_zero_pt (f : MvPowerSeries σ ℝ) : ev f 0 = constantCoeff f := by
  unfold ev
  rw [tsum_eq_single 0]
  · simp [mon_zero, coeff_zero_eq_constantCoeff_apply]
  · intro β hβ
    obtain ⟨i, hi⟩ : ∃ i, β i ≠ 0 := by
      by_contra h; exact hβ (Finsupp.ext fun i => by simpa using not_exists.1 h i)
    have : mon (0 : σ → ℝ) β = 0 := by
      unfold mon
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [this, mul_zero]

end Eval

end SubanalyticLib
/-! SubanalyticLib L1c (body; prepend L2E.lean minus its last line, or L1_Conv + L1_Eval.body):
bridge A.  A power series converging absolutely on the closed polydisc of polyradius `w` defines,
through `ev`, a function with an explicit formal multilinear series on the sup-norm ball of any
radius `r ≤ min w`; hence `ev f` is analytic near `0`. -/

namespace SubanalyticLib

section BridgeA

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- the exponent of the monomial `∏_j X (ι j)`. -/
noncomputable def mult {n : ℕ} (ι : Fin n → σ) : σ →₀ ℕ := ∑ j, Finsupp.single (ι j) 1

theorem degree_mult {n : ℕ} (ι : Fin n → σ) : Finsupp.degree (mult ι) = n := by
  simp [mult, map_sum]

theorem mult_cons {n : ℕ} (i : σ) (ι : Fin n → σ) :
    mult (Fin.cons i ι : Fin (n + 1) → σ) = Finsupp.single i 1 + mult ι := by
  simp [mult, Fin.sum_univ_succ]

theorem exists_mult : ∀ (n : ℕ) (α : σ →₀ ℕ), Finsupp.degree α = n →
    ∃ ι : Fin n → σ, mult ι = α := by
  intro n
  induction n with
  | zero =>
    intro α hα
    refine ⟨Fin.elim0, ?_⟩
    rw [(Finsupp.degree_eq_zero_iff α).1 hα]; simp [mult]
  | succ n ih =>
    intro α hα
    have hα0 : α ≠ 0 := by
      intro h; rw [h] at hα; simp at hα
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
      by_contra h; exact hα0 (Finsupp.ext fun j => by simpa using not_exists.1 h j)
    have hle : Finsupp.single i 1 ≤ α := by
      rw [Finsupp.single_le_iff]; omega
    have hsplit : α = Finsupp.single i 1 + (α - Finsupp.single i 1) := by
      rw [add_tsub_cancel_of_le hle]
    have hdeg : Finsupp.degree (α - Finsupp.single i 1) = n := by
      have := congrArg Finsupp.degree hsplit
      rw [map_add, Finsupp.degree_single] at this; omega
    obtain ⟨ι, hι⟩ := ih _ hdeg
    exact ⟨Fin.cons i ι, by rw [mult_cons, hι, ← hsplit]⟩

theorem mon_sum (x : σ → ℝ) {ι : Type*} (s : Finset ι) (a : ι → σ →₀ ℕ) :
    mon x (∑ j ∈ s, a j) = ∏ j ∈ s, mon x (a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mon_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, mon_add, ih]

theorem mw_sum (w : σ → ℝ) {ι : Type*} (s : Finset ι) (a : ι → σ →₀ ℕ) :
    mw w (∑ j ∈ s, a j) = ∏ j ∈ s, mw w (a j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mw_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, mw_add, ih]

theorem mon_mult (x : σ → ℝ) {n : ℕ} (ι : Fin n → σ) : mon x (mult ι) = ∏ j, x (ι j) := by
  rw [mult, mon_sum]; simp [mon_single]

theorem mw_mult (w : σ → ℝ) {n : ℕ} (ι : Fin n → σ) : mw w (mult ι) = ∏ j, w (ι j) := by
  rw [mult, mw_sum]; simp [mw_single]

/-- the exponents of total degree `n`. -/
noncomputable def degs (n : ℕ) : Finset (σ →₀ ℕ) := (Finset.univ : Finset (Fin n → σ)).image mult

theorem mem_degs {n : ℕ} {α : σ →₀ ℕ} : α ∈ degs n ↔ Finsupp.degree α = n := by
  constructor
  · intro h
    obtain ⟨ι, -, rfl⟩ := Finset.mem_image.1 h
    exact degree_mult ι
  · intro h
    obtain ⟨ι, hι⟩ := exists_mult n α h
    exact Finset.mem_image.2 ⟨ι, Finset.mem_univ _, hι⟩

/-- `ι` is the chosen representative of its exponent. -/
def Rep {n : ℕ} (ι : Fin n → σ) : Prop :=
  (⟨ι, rfl⟩ : ∃ ι' : Fin n → σ, mult ι' = mult ι).choose = ι

/-- the chosen representatives. -/
noncomputable def reps (n : ℕ) : Finset (Fin n → σ) := by
  classical exact (Finset.univ : Finset (Fin n → σ)).filter Rep

theorem choose_congr {n : ℕ} {a b : σ →₀ ℕ} (ha : ∃ ι' : Fin n → σ, mult ι' = a)
    (hb : ∃ ι' : Fin n → σ, mult ι' = b) (hab : a = b) : ha.choose = hb.choose := by
  subst hab; rfl

theorem mem_reps {n : ℕ} {ι : Fin n → σ} : ι ∈ reps n ↔ Rep ι := by
  classical
  unfold reps
  simp

theorem sum_reps {n : ℕ} (g : (σ →₀ ℕ) → ℝ) :
    ∑ ι ∈ reps n, g (mult ι) = ∑ α ∈ degs n, g α := by
  classical
  have himg : (reps n).image mult = degs (σ := σ) n := by
    apply Finset.Subset.antisymm
    · intro α hα
      obtain ⟨ι, -, rfl⟩ := Finset.mem_image.1 hα
      exact Finset.mem_image.2 ⟨ι, Finset.mem_univ _, rfl⟩
    · intro α hα
      obtain ⟨ι, -, rfl⟩ := Finset.mem_image.1 hα
      set h0 : ∃ ι' : Fin n → σ, mult ι' = mult ι := ⟨ι, rfl⟩
      have hspec : mult h0.choose = mult ι := h0.choose_spec
      refine Finset.mem_image.2 ⟨h0.choose, mem_reps.2 ?_, hspec⟩
      unfold Rep
      exact choose_congr _ h0 hspec
  rw [← himg, Finset.sum_image]
  intro ι1 h1 ι2 h2 h12
  have r1 := mem_reps.1 h1
  have r2 := mem_reps.1 h2
  unfold Rep at r1 r2
  rw [← r1, ← r2]
  exact choose_congr _ _ h12

/-- the monomial multilinear map `m ↦ ∏_j m_j (ι j)`. -/
noncomputable def pmono {n : ℕ} (ι : Fin n → σ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => σ → ℝ) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
    (fun j => ContinuousLinearMap.proj (ι j))

theorem pmono_apply {n : ℕ} (ι : Fin n → σ) (m : Fin n → σ → ℝ) :
    pmono ι m = ∏ j, m j (ι j) := by
  simp [pmono]

theorem norm_pmono_le {n : ℕ} (ι : Fin n → σ) : ‖pmono ι‖ ≤ 1 := by
  refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one fun m => ?_
  rw [pmono_apply, one_mul, norm_prod]
  exact Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => norm_le_pi_norm (m j) (ι j))

/-- the formal multilinear series of `ev f` at `0`. -/
noncomputable def ps (f : MvPowerSeries σ ℝ) : FormalMultilinearSeries ℝ (σ → ℝ) ℝ :=
  fun n => ∑ ι ∈ reps n, coeff (mult ι) f • pmono ι

theorem ps_diag (f : MvPowerSeries σ ℝ) (n : ℕ) (y : σ → ℝ) :
    ps f n (fun _ => y) = ∑ α ∈ degs n, coeff α f * mon y α := by
  rw [ps, ContinuousMultilinearMap.sum_apply]
  simp_rw [ContinuousMultilinearMap.smul_apply, pmono_apply, smul_eq_mul]
  rw [← sum_reps (fun α => coeff α f * mon y α)]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [mon_mult]

theorem norm_ps_le (f : MvPowerSeries σ ℝ) (n : ℕ) :
    ‖ps f n‖ ≤ ∑ α ∈ degs n, |coeff α f| := by
  rw [← sum_reps (fun α => |coeff α f|)]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ι _ => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (norm_pmono_le ι) (abs_nonneg _)).trans (le_of_eq (mul_one _))

theorem pow_le_mw {w : σ → ℝ} {r : ℝ} (hr : 0 ≤ r) (hrw : ∀ i, r ≤ w i) {n : ℕ} {α : σ →₀ ℕ}
    (hα : α ∈ degs n) : r ^ n ≤ mw w α := by
  obtain ⟨ι, -, rfl⟩ := Finset.mem_image.1 hα
  rw [mw_mult]
  calc r ^ n = ∏ _j : Fin n, r := by simp
    _ ≤ ∏ j, w (ι j) := Finset.prod_le_prod (fun _ _ => hr) (fun j _ => hrw (ι j))

theorem ps_bound {w : σ → ℝ} (hw : ∀ i, 0 ≤ w i) {f : MvPowerSeries σ ℝ} (hf : Conv w f)
    {r : ℝ} (hr : 0 ≤ r) (hrw : ∀ i, r ≤ w i) (n : ℕ) : ‖ps f n‖ * r ^ n ≤ wn w f := by
  calc ‖ps f n‖ * r ^ n ≤ (∑ α ∈ degs n, |coeff α f|) * r ^ n :=
        mul_le_mul_of_nonneg_right (norm_ps_le f n) (pow_nonneg hr n)
    _ = ∑ α ∈ degs n, |coeff α f| * r ^ n := Finset.sum_mul _ _ _
    _ ≤ ∑ α ∈ degs n, wt w f α := Finset.sum_le_sum fun α hα =>
        mul_le_mul_of_nonneg_left (pow_le_mw hr hrw hα) (abs_nonneg _)
    _ ≤ wn w f := hf.sum_le_tsum _ (fun α _ => wt_nonneg hw f α)

/-- Bridge A. -/
theorem hasFPowerSeriesOnBall_ev {w : σ → ℝ} (hw : ∀ i, 0 ≤ w i) {f : MvPowerSeries σ ℝ}
    (hf : Conv w f) {r : NNReal} (hr : 0 < r) (hrw : ∀ i, (r : ℝ) ≤ w i) :
    HasFPowerSeriesOnBall (ev f) (ps f) 0 r where
  r_le := FormalMultilinearSeries.le_radius_of_bound _ (wn w f)
    (ps_bound hw hf r.coe_nonneg hrw)
  r_pos := by exact_mod_cast hr
  hasSum := by
    intro y hy
    rw [mem_eball_zero_iff] at hy
    have hy' : ‖y‖ < r := by exact_mod_cast hy
    have hx : ∀ i, |y i| ≤ w i := fun i =>
      ((norm_le_pi_norm y i).trans hy'.le).trans (hrw i)
    rw [zero_add]
    have h1 : HasSum (fun α => coeff α f * mon y α) (ev f y) := (summable_term hx hf).hasSum
    have h2 := (Equiv.sigmaFiberEquiv (Finsupp.degree : (σ →₀ ℕ) → ℕ)).hasSum_iff.2 h1
    refine h2.sigma fun n => ?_
    rw [ps_diag]
    classical
    have h3 : HasSum (fun c : {α : σ →₀ ℕ // Finsupp.degree α = n} => coeff c.1 f * mon y c.1)
        (∑ c ∈ (degs n).subtype (fun α => Finsupp.degree α = n), coeff c.1 f * mon y c.1) := by
      apply hasSum_sum_of_ne_finset_zero
      intro c hc
      exact absurd (Finset.mem_subtype.2 (mem_degs.2 c.2)) hc
    rw [Finset.sum_subtype_of_mem (fun α => coeff α f * mon y α)
      (fun α hα => mem_degs.1 hα)] at h3
    exact h3

theorem analyticAt_ev_zero {w : σ → ℝ} (hw : ∀ i, 0 < w i) {f : MvPowerSeries σ ℝ}
    (hf : Conv w f) : ∃ r : ℝ, 0 < r ∧ ∀ x : σ → ℝ, ‖x‖ < r → AnalyticAt ℝ (ev f) x := by
  classical
  by_cases hσ : Nonempty σ
  · obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ w
      (Finset.univ_nonempty_iff.2 hσ)
    refine ⟨w i0, hw i0, fun x hx => ?_⟩
    let r0 : NNReal := ⟨w i0, (hw i0).le⟩
    have hpow := hasFPowerSeriesOnBall_ev (fun i => (hw i).le) hf
      (r := r0) (hw i0) (fun i => hi0 i (Finset.mem_univ _))
    refine hpow.analyticAt_of_mem ?_
    rw [mem_eball_zero_iff, enorm_eq_nnnorm]
    exact ENNReal.coe_lt_coe.2 (NNReal.coe_lt_coe.1 hx)
  · refine ⟨1, one_pos, fun x _ => ?_⟩
    have hpow := hasFPowerSeriesOnBall_ev (fun i => (hw i).le) hf (r := 1) one_pos
      (fun i => absurd ⟨i⟩ hσ)
    refine hpow.analyticAt_of_mem ?_
    have : x = 0 := funext fun i => absurd ⟨i⟩ hσ
    rw [this]; exact Metric.mem_eball_self (by simp)

end BridgeA

end SubanalyticLib
/-! SubanalyticLib L1d (body; after L1c_Bridge.body): bridge B.  A function with a power series
expansion at `x0` (on `σ → ℝ`, sup norm) agrees near `x0` with `ev a` for a power series `a`
converging absolutely on a small cube (`Conv (fun _ => ρ) a`). -/

namespace SubanalyticLib

section BridgeB

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem hasSum_fiber (g : (σ →₀ ℕ) → ℝ) (n : ℕ) :
    HasSum (fun c : {α : σ →₀ ℕ // Finsupp.degree α = n} => g c.1) (∑ α ∈ degs n, g α) := by
  classical
  have h3 : HasSum (fun c : {α : σ →₀ ℕ // Finsupp.degree α = n} => g c.1)
      (∑ c ∈ (degs n).subtype (fun α => Finsupp.degree α = n), g c.1) := by
    apply hasSum_sum_of_ne_finset_zero
    intro c hc
    exact absurd (Finset.mem_subtype.2 (mem_degs.2 c.2)) hc
  rwa [Finset.sum_subtype_of_mem g (fun α hα => mem_degs.1 hα)] at h3

/-- `ev` as the sum of its homogeneous parts. -/
theorem hasSum_ev_graded {w : σ → ℝ} {f : MvPowerSeries σ ℝ} (hf : Conv w f) {x : σ → ℝ}
    (hx : ∀ i, |x i| ≤ w i) :
    HasSum (fun n => ∑ α ∈ degs n, coeff α f * mon x α) (ev f x) := by
  have h1 : HasSum (fun α => coeff α f * mon x α) (ev f x) := (summable_term hx hf).hasSum
  have h2 := (Equiv.sigmaFiberEquiv (Finsupp.degree : (σ →₀ ℕ) → ℕ)).hasSum_iff.2 h1
  exact h2.sigma fun n => hasSum_fiber (fun α => coeff α f * mon x α) n

theorem cmm_diag_expand {n : ℕ} (q : ContinuousMultilinearMap ℝ (fun _ : Fin n => σ → ℝ) ℝ)
    (y : σ → ℝ) :
    q (fun _ => y) = ∑ ι : Fin n → σ, (∏ j, y (ι j)) * q (fun j => Pi.single (ι j) 1) := by
  have hy : y = ∑ i, y i • (Pi.single i (1 : ℝ) : σ → ℝ) := by
    ext k; simp [Pi.single_apply]
  have h := ContinuousMultilinearMap.map_sum q (fun (_ : Fin n) (i : σ) => y i • (Pi.single i (1 : ℝ) : σ → ℝ))
  rw [← hy] at h
  rw [h]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul]

/-- the coefficient of `x^α` in the degree-`n` part of `p`. -/
noncomputable def ecA (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) (n : ℕ) (α : σ →₀ ℕ) : ℝ :=
  ∑ ι ∈ (Finset.univ : Finset (Fin n → σ)) with mult ι = α, p n (fun j => Pi.single (ι j) 1)

/-- the power series of coefficients of `p`. -/
noncomputable def ecoef (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) : MvPowerSeries σ ℝ :=
  fun α => ecA p (Finsupp.degree α) α

theorem coeff_ecoef (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) (α : σ →₀ ℕ) :
    coeff α (ecoef p) = ecA p (Finsupp.degree α) α := rfl

theorem coeff_ecoef_of_mem (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) {n : ℕ} {α : σ →₀ ℕ}
    (hα : α ∈ degs n) : coeff α (ecoef p) = ecA p n α := by
  rw [coeff_ecoef, mem_degs.1 hα]

theorem p_diag_eq (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) (n : ℕ) (y : σ → ℝ) :
    p n (fun _ => y) = ∑ α ∈ degs n, coeff α (ecoef p) * mon y α := by
  rw [cmm_diag_expand]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := degs n) (g := mult)
     (fun ι _ => Finset.mem_image.2 ⟨ι, Finset.mem_univ _, rfl⟩)]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [coeff_ecoef_of_mem p hα, ecA, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ι hι => ?_
  rw [Finset.mem_filter] at hι
  rw [← hι.2, mon_mult]; ring

theorem norm_single_one (i : σ) : ‖(Pi.single i (1 : ℝ) : σ → ℝ)‖ = 1 := by
  rw [Pi.norm_single]; simp

theorem abs_ecA_le (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) (n : ℕ) (α : σ →₀ ℕ) :
    |ecA p n α| ≤ ∑ ι ∈ (Finset.univ : Finset (Fin n → σ)) with mult ι = α, ‖p n‖ := by
  unfold ecA
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ι _ => ?_)
  rw [← Real.norm_eq_abs]
  refine ((p n).le_opNorm _).trans (le_of_eq ?_)
  simp [norm_single_one]

theorem fiber_bound (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) :
    ∑ α ∈ degs n, |coeff α (ecoef p)| * ρ ^ n ≤ ‖p n‖ * ((Fintype.card σ : ℝ) * ρ) ^ n := by
  calc ∑ α ∈ degs n, |coeff α (ecoef p)| * ρ ^ n
      ≤ ∑ α ∈ degs n,
          (∑ ι ∈ (Finset.univ : Finset (Fin n → σ)) with mult ι = α, ‖p n‖) * ρ ^ n :=
        Finset.sum_le_sum fun α hα => by
          rw [coeff_ecoef_of_mem p hα]
          exact mul_le_mul_of_nonneg_right (abs_ecA_le p n α) (pow_nonneg hρ n)
    _ = ∑ ι : Fin n → σ, ‖p n‖ * ρ ^ n := by
        simp_rw [Finset.sum_mul]
        exact Finset.sum_fiberwise_of_maps_to
          (fun ι _ => Finset.mem_image.2 ⟨ι, Finset.mem_univ _, rfl⟩) _
    _ = ‖p n‖ * ((Fintype.card σ : ℝ) * ρ) ^ n := by
        simp [Finset.sum_const, mul_pow]; ring

theorem mw_const (ρ : ℝ) (α : σ →₀ ℕ) : mw (fun _ => ρ) α = ρ ^ Finsupp.degree α := by
  rw [mw, Finsupp.degree_eq_sum, Finset.prod_pow_eq_pow_sum]

theorem conv_ecoef (p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ) {ρ : NNReal}
    (h : (((Fintype.card σ : NNReal) * ρ : NNReal) : ENNReal) < p.radius) :
    Conv (fun _ => (ρ : ℝ)) (ecoef p) := by
  have hs := p.summable_norm_mul_pow h
  unfold Conv
  rw [← (Equiv.sigmaFiberEquiv (Finsupp.degree : (σ →₀ ℕ) → ℕ)).summable_iff]
  have hfib : ∀ n, HasSum
      (fun c : {α : σ →₀ ℕ // Finsupp.degree α = n} => wt (fun _ => (ρ : ℝ)) (ecoef p) c.1)
      (∑ α ∈ degs n, |coeff α (ecoef p)| * (ρ : ℝ) ^ n) := by
    intro n
    have := hasSum_fiber (fun α => wt (fun _ => (ρ : ℝ)) (ecoef p) α) n
    convert this using 1
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [wt, mw_const, mem_degs.1 hα]
  refine (summable_sigma_of_nonneg (f := wt (fun _ => (ρ : ℝ)) (ecoef p) ∘
    ⇑(Equiv.sigmaFiberEquiv (Finsupp.degree : (σ →₀ ℕ) → ℕ)))
    (fun c => wt_nonneg (fun _ => ρ.coe_nonneg) _ _)).2 ⟨fun n => (hfib n).summable, ?_⟩
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · exact tsum_nonneg fun c => wt_nonneg (fun _ => ρ.coe_nonneg) _ _
  · have hb : ∑ α ∈ degs n, |coeff α (ecoef p)| * (ρ : ℝ) ^ n ≤
        ‖p n‖ * (((Fintype.card σ : NNReal) * ρ : NNReal) : ℝ) ^ n := by
      have := fiber_bound p ρ.coe_nonneg n
      simpa using this
    exact (le_of_eq (hfib n).tsum_eq).trans hb

/-- Bridge B. -/
theorem exists_conv_of_hasFPowerSeriesOnBall {F : (σ → ℝ) → ℝ}
    {p : FormalMultilinearSeries ℝ (σ → ℝ) ℝ} {x0 : σ → ℝ} {R : ENNReal}
    (hF : HasFPowerSeriesOnBall F p x0 R) :
    ∃ ρ : ℝ, 0 < ρ ∧ Conv (fun _ => ρ) (ecoef p) ∧
      ∀ x : σ → ℝ, ‖x‖ ≤ ρ → F (x0 + x) = ev (ecoef p) x := by
  obtain ⟨r, hr0, hrR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hF.r_pos
  have hr0' : 0 < r := by exact_mod_cast hr0
  set c : NNReal := (Fintype.card σ : NNReal) + 1 with hc_def
  have hc1 : 1 ≤ c := le_add_of_nonneg_left zero_le
  have hc0 : c ≠ 0 := (lt_of_lt_of_le zero_lt_one hc1).ne'
  set ρ : NNReal := r / c with hρ_def
  have hcρ_eq : c * ρ = r := by rw [hρ_def]; field_simp
  have hcρ : (Fintype.card σ : NNReal) * ρ ≤ r := by
    rw [← hcρ_eq]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) zero_le
  have hρr : ρ ≤ r := by
    rw [← hcρ_eq]; exact le_mul_of_one_le_left zero_le hc1
  have hρ0 : 0 < ρ := by rw [hρ_def]; exact div_pos hr0' (lt_of_lt_of_le zero_lt_one hc1)
  have hconv : (((Fintype.card σ : NNReal) * ρ : NNReal) : ENNReal) < p.radius :=
    lt_of_lt_of_le (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hcρ) hrR) hF.r_le
  refine ⟨ρ, NNReal.coe_pos.2 hρ0, conv_ecoef p hconv, fun x hx => ?_⟩
  have hxb : x ∈ Metric.eball (0 : σ → ℝ) R := by
    rw [mem_eball_zero_iff, enorm_eq_nnnorm]
    have hx' : ‖x‖₊ ≤ ρ := NNReal.coe_le_coe.1 hx
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hx'.trans hρr)) hrR
  have h1 := hF.hasSum hxb
  have hxi : ∀ i, |x i| ≤ (fun _ => (ρ : ℝ)) i := fun i => (norm_le_pi_norm x i).trans hx
  have h2 := hasSum_ev_graded (w := fun _ => (ρ : ℝ)) (conv_ecoef p hconv) hxi
  have h3 : (fun n => p n (fun _ => x)) = fun n => ∑ α ∈ degs n, coeff α (ecoef p) * mon x α :=
    funext fun n => p_diag_eq p n x
  rw [h3] at h1
  exact h1.unique h2

theorem exists_conv_of_analyticAt {F : (σ → ℝ) → ℝ} {x0 : σ → ℝ} (hF : AnalyticAt ℝ F x0) :
    ∃ a : MvPowerSeries σ ℝ, ∃ ρ : ℝ, 0 < ρ ∧ Conv (fun _ => ρ) a ∧
      ∀ x : σ → ℝ, ‖x‖ ≤ ρ → F (x0 + x) = ev a x := by
  obtain ⟨p, R, hp⟩ := hF
  obtain ⟨ρ, h1, h2, h3⟩ := exists_conv_of_hasFPowerSeriesOnBall hp
  exact ⟨_, ρ, h1, h2, h3⟩

end BridgeB

end SubanalyticLib
/-! SubanalyticLib L2e (body; after L2E.lean): Weierstrass preparation at the level of values.
On a small polydisc, `x_y^d = ev q x * ev f x + ev r x` with `ev q x ≠ 0`, and
`ev r x = Σ_{j<d} x_y^j * c_j(x)` where each `c_j` does not depend on `x_y`. -/

namespace SubanalyticLib

section EvPrep

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem ev_X_pow (i : σ) (d : ℕ) (x : σ → ℝ) {w : σ → ℝ} (hx : ∀ i, |x i| ≤ w i)
    (hw : ∀ i, 0 ≤ w i) : ev ((X i : MvPowerSeries σ ℝ) ^ d) x = x i ^ d := by
  rw [ev_pow hx hw (conv_X hw i) d, ev_X]

/-- the `j`-th coefficient of `r` as a series in the distinguished variable `y`. -/
noncomputable def yslice (y : σ) (j : ℕ) (r : MvPowerSeries σ ℝ) : MvPowerSeries σ ℝ :=
  lowPart y 1 (hatPart y j r)

theorem coeff_yslice (y : σ) (j : ℕ) (r : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) :
    coeff α (yslice y j r) = if α y < 1 then coeff (α + Finsupp.single y j) r else 0 := by
  rw [yslice, coeff_lowPart, coeff_hatPart]

theorem eq_sum_yslice (y : σ) (d : ℕ) (r : MvPowerSeries σ ℝ) (hr : hatPart y d r = 0) :
    r = ∑ j ∈ Finset.range d, X y ^ j * yslice y j r := by
  have hlow : lowPart y d r = r := (lowPart_eq_self_iff y d r).2 hr
  ext α
  rw [map_sum]
  simp_rw [X_pow_eq, coeff_monomial_mul, one_mul, coeff_yslice]
  rw [Finset.sum_eq_single (α y)]
  · by_cases hαd : α y < d
    · have hle : Finsupp.single y (α y) ≤ α := by
        rw [Finsupp.single_le_iff]
      have hsub : (α - Finsupp.single y (α y)) y = 0 := by simp
      rw [if_pos hle, hsub, if_pos Nat.one_pos, tsub_add_cancel_of_le hle]
    · have h0 : coeff α r = 0 := by rw [← hlow, coeff_lowPart, if_neg hαd]
      have hle : Finsupp.single y (α y) ≤ α := by rw [Finsupp.single_le_iff]
      rw [if_pos hle, tsub_add_cancel_of_le hle, h0, ite_self]
  · intro j _ hj
    split_ifs with h1 h2
    · exfalso
      have e1 : (α - Finsupp.single y j) y = α y - j := by simp
      have e2 : j ≤ α y := by
        have := (Finsupp.single_le_iff).1 h1; simpa using this
      omega
    · rfl
    · rfl
  · intro hd
    rw [Finset.mem_range, not_lt] at hd
    have : coeff α r = 0 := by
      rw [← hlow, coeff_lowPart, if_neg (by omega)]
    split_ifs with h1 h2
    · rw [tsub_add_cancel_of_le h1, this]
    · rfl
    · rfl

/-- `y`-free series do not see the `y` coordinate. -/
theorem ev_yslice_update (y : σ) (j : ℕ) (r : MvPowerSeries σ ℝ) (x : σ → ℝ) (t : ℝ) :
    ev (yslice y j r) (Function.update x y t) = ev (yslice y j r) x := by
  unfold ev
  congr 1; funext α
  rw [coeff_yslice]
  split_ifs with h
  · congr 1
    unfold mon
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i = y
    · subst hi; have : α i = 0 := by omega
      simp [this]
    · rw [Function.update_of_ne hi]
  · simp

theorem ev_sum_X_pow_mul (y : σ) {w : σ → ℝ} (hw : ∀ i, 0 ≤ w i) {x : σ → ℝ}
    (hx : ∀ i, |x i| ≤ w i) (s : Finset ℕ) (g : ℕ → MvPowerSeries σ ℝ) (hg : ∀ j, Conv w (g j)) :
    ev (∑ j ∈ s, X y ^ j * g j) x = ∑ j ∈ s, x y ^ j * ev (g j) x := by
  classical
  have hterm : ∀ j, Conv w ((X y : MvPowerSeries σ ℝ) ^ j * g j) := fun j =>
    Conv.mul hw (Conv.pow hw (conv_X hw y) j) (hg j)
  induction s using Finset.induction_on with
  | empty => simp [ev]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      ev_add hx (hterm j) (conv_finset_sum hw s _ (fun k _ => hterm k)).1,
      ev_mul hx hw (Conv.pow hw (conv_X hw y) j) (hg j), ev_X_pow y j x hx hw, ih]

theorem ev_eq_sum_yslice (y : σ) (d : ℕ) {w : σ → ℝ} (hw : ∀ i, 0 ≤ w i) (hy : 0 < w y)
    {r : MvPowerSeries σ ℝ} (hrc : Conv w r) (hr : hatPart y d r = 0) {x : σ → ℝ}
    (hx : ∀ i, |x i| ≤ w i) :
    ev r x = ∑ j ∈ Finset.range d, x y ^ j * ev (yslice y j r) x := by
  have hs : ∀ j, Conv w (yslice y j r) := fun j => Conv.low y hw 1 (Conv.hat y hw hy j hrc)
  conv_lhs => rw [eq_sum_yslice y d r hr]
  exact ev_sum_X_pow_mul y hw hx _ _ hs

end EvPrep

end SubanalyticLib
/-! SubanalyticLib L3g (body; after L2F.lean): power-growth of positive zeros of a nonzero
convergent series in two variables.  If `G ≠ 0` converges on the polydisc `w` and `t = ψ(s) > 0`
solves `G(s,t) = 0` whenever `t ≤ w 1`, then `ψ(s) ≥ c s^m` near `0⁺`.  No Puiseux expansion
is needed: `G = t^k (g(s) + t H)` with `g(s) = s^m (b + o(1))`, `b ≠ 0`. -/

namespace SubanalyticLib

section Growth

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem ev_single_axis (v : σ) {h : MvPowerSeries σ ℝ}
    (hz : ∀ j, coeff (Finsupp.single v j) h = 0) (s : ℝ) : ev h (Pi.single v s) = 0 := by
  have key : ∀ α, coeff α h * mon (Pi.single v s) α = 0 := by
    intro α
    by_cases hα : ∃ i, i ≠ v ∧ α i ≠ 0
    · obtain ⟨i, hiv, hi⟩ := hα
      have : mon (Pi.single v s) α = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Pi.single_apply, hiv, hi])
      rw [this, mul_zero]
    · push_neg at hα
      have : α = Finsupp.single v (α v) := by
        ext i
        by_cases hi : i = v
        · subst hi; simp
        · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]; exact hα i hi
      rw [this, hz, zero_mul]
  unfold ev
  simp only [key, tsum_zero]

end Growth

end SubanalyticLib

/-! SubanalyticLib CS-5d prelude: `ev_weierstrass_prep` also exposing that the remainder has no pure-`y` terms
below degree `d` (copied from L2e with that extra conjunct). -/

namespace SubanalyticLib

section WP2

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem ev_weierstrass_prep2 (y : σ) {w0 : σ → ℝ} (hw0 : ∀ i, 0 < w0 i) (d : ℕ)
    {f : MvPowerSeries σ ℝ} (hf : Conv w0 f) (hreg : ∀ j < d, coeff (Finsupp.single y j) f = 0)
    (hd : coeff (Finsupp.single y d) f ≠ 0) :
    ∃ w : σ → ℝ, (∀ i, 0 < w i) ∧ (∀ i, w i ≤ w0 i) ∧
      ∃ q r : MvPowerSeries σ ℝ, Conv w q ∧ Conv w r ∧ hatPart y d r = 0 ∧
        (∀ j < d, coeff (Finsupp.single y j) r = 0) ∧
        ∀ x : σ → ℝ, (∀ i, |x i| ≤ w i) → ev q x ≠ 0 ∧ x y ^ d = ev q x * ev f x + ev r x := by
  obtain ⟨w1, hw1, hw10, q, r, hq, hr, hr0, hc, hrc0, heq⟩ := weierstrass_prep y hw0 d hf hreg hd
  have hw1' : ∀ i, 0 ≤ w1 i := fun i => (hw1 i).le
  set c := constantCoeff q with hc_def
  set g := q - C c with hg_def
  have hg : Conv w1 g := Conv.sub hw1' hq (conv_C c)
  have hgz : ∀ α, sdeg (Finset.univ : Finset σ) α = 0 → coeff α g = 0 := by
    intro α hα
    have : α = 0 := by
      ext i
      have := (Finset.sum_eq_zero_iff.1 hα) i (Finset.mem_univ _)
      simpa using this
    subst this
    rw [hg_def, map_sub, coeff_zero_eq_constantCoeff_apply, coeff_zero_C, hc_def, sub_self]
  have hcpos : 0 < |c| := abs_pos.2 hc
  have hgn : 0 ≤ wn w1 g := wn_nonneg hw1' g
  set τ : ℝ := min 1 (|c| / (2 * (wn w1 g + 1))) with hτ_def
  have hτ0 : 0 < τ := lt_min one_pos (div_pos hcpos (by linarith))
  have hτ1 : τ ≤ 1 := min_le_left _ _
  obtain ⟨hgw, hgwn⟩ := conv_scale hw1' Finset.univ hτ0.le hτ1 hg hgz
  set w := scaleW (Finset.univ : Finset σ) τ w1 with hw_def
  have hwpos : ∀ i, 0 < w i := fun i => by
    simp only [hw_def, scaleW, Finset.mem_univ, if_true]; exact mul_pos hτ0 (hw1 i)
  have hw' : ∀ i, 0 ≤ w i := fun i => (hwpos i).le
  have hwle : ∀ i, w i ≤ w1 i := scaleW_le hw1' hτ1
  have hgsmall : wn w g < |c| := by
    refine lt_of_le_of_lt hgwn ?_
    have h1 : τ ≤ |c| / (2 * (wn w1 g + 1)) := min_le_right _ _
    have h2 : τ * wn w1 g ≤ |c| / (2 * (wn w1 g + 1)) * wn w1 g :=
      mul_le_mul_of_nonneg_right h1 hgn
    have h3 : |c| / (2 * (wn w1 g + 1)) * wn w1 g < |c| := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  have hqw : Conv w q := Conv.mono hw' hwle hq
  have hrw : Conv w r := Conv.mono hw' hwle hr
  have hfw : Conv w f := Conv.mono hw' (fun i => (hwle i).trans (hw10 i)) hf
  refine ⟨w, hwpos, fun i => (hwle i).trans (hw10 i), q, r, hqw, hrw, hr0, hrc0, fun x hx => ⟨?_, ?_⟩⟩
  · have hqx : ev q x = c + ev g x := by
      have : q = C c + g := by rw [hg_def]; ring
      rw [this, ev_add hx (conv_C c) hgw, ev_C]
    rw [hqx]
    intro h0
    have h4 : |ev g x| ≤ wn w g := abs_ev_le hx hgw
    have h5 : ev g x = -c := by linarith
    rw [h5, abs_neg] at h4
    linarith
  · have : ev (X y ^ d) x = ev (q * f + r) x := by rw [heq]
    rw [ev_X_pow y d x hx hw', ev_add hx (Conv.mul hw' hqw hfw) hrw, ev_mul hx hw' hqw hfw] at this
    exact this

end WP2

end SubanalyticLib

/-! SubanalyticLib CS-5a: real Newton–Puiseux in one parameter, infrastructure.
`Ran` = functions analytic at `0`; `pv P v` = the real polynomial obtained by evaluating the
coefficients of `P : Ran[X]` at `v`; `BranchesAt P q` = the real roots of `pv P (v ^ q)` for
small `v > 0` are exactly the values `φ v` of finitely many analytic germs `φ`. -/

open Filter Topology Set Polynomial

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace SubanalyticLib
namespace Pui

noncomputable section

/-- Real functions analytic at `0`, as a subring of `ℝ → ℝ`. -/
def Ran : Subring (ℝ → ℝ) where
  carrier := {f | AnalyticAt ℝ f 0}
  mul_mem' {a b} ha hb := by
    show AnalyticAt ℝ (fun x => a x * b x) 0
    exact ha.mul hb
  one_mem' := by
    show AnalyticAt ℝ (fun _ => (1 : ℝ)) 0
    exact analyticAt_const
  add_mem' {a b} ha hb := by
    show AnalyticAt ℝ (fun x => a x + b x) 0
    exact ha.add hb
  zero_mem' := by
    show AnalyticAt ℝ (fun _ => (0 : ℝ)) 0
    exact analyticAt_const
  neg_mem' {a} ha := by
    show AnalyticAt ℝ (fun x => -a x) 0
    exact ha.neg

/-- Constant germ. -/
def cst (c : ℝ) : Ran := ⟨fun _ => c, analyticAt_const⟩

@[simp] lemma cst_apply (c v : ℝ) : (cst c : ℝ → ℝ) v = c := rfl

/-- Evaluation at a point. -/
def evAt (v : ℝ) : Ran →+* ℝ := (Pi.evalRingHom (fun _ : ℝ => ℝ) v).comp Ran.subtype

@[simp] lemma evAt_apply (v : ℝ) (a : Ran) : evAt v a = (a : ℝ → ℝ) v := rfl

/-- The real polynomial at parameter `v`. -/
def pv (P : Ran[X]) (v : ℝ) : ℝ[X] := P.map (evAt v)

/-- The branch property with ramification index `q`. -/
def BranchesAt (P : Ran[X]) (q : ℕ) : Prop :=
  ∃ Φ : Set (ℝ → ℝ), Φ.Finite ∧ (∀ φ ∈ Φ, AnalyticAt ℝ φ 0) ∧
    ∀ᶠ v in 𝓝[>] (0 : ℝ), ∀ y : ℝ, (pv P (v ^ q)).IsRoot y ↔ ∃ φ ∈ Φ, φ v = y

lemma tendsto_pow_nhdsGT {k : ℕ} (hk : 0 < k) :
    Tendsto (fun w : ℝ => w ^ k) (𝓝[>] 0) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, eventually_mem_nhdsWithin.mono fun w (hw : 0 < w) => show w ^ k ∈ Ioi 0 from pow_pos hw k⟩
  have : Tendsto (fun w : ℝ => w ^ k) (𝓝 0) (𝓝 (0 ^ k)) := (continuous_pow k).tendsto 0
  rw [zero_pow hk.ne'] at this
  exact this.mono_left nhdsWithin_le_nhds

lemma analyticAt_comp_pow {φ : ℝ → ℝ} (hφ : AnalyticAt ℝ φ 0) {k : ℕ} (hk : 0 < k) :
    AnalyticAt ℝ (fun w => φ (w ^ k)) 0 :=
  hφ.comp_of_eq ((analyticAt_id).pow k) (by simp [hk.ne'])

/-- Reparametrize `v = w ^ k`. -/
lemma BranchesAt.mul {P : Ran[X]} {q : ℕ} (h : BranchesAt P q) {k : ℕ} (hk : 0 < k) :
    BranchesAt P (q * k) := by
  obtain ⟨Φ, hfin, han, hev⟩ := h
  refine ⟨(fun φ => fun w => φ (w ^ k)) '' Φ, hfin.image _, ?_, ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact analyticAt_comp_pow (han φ hφ) hk
  · filter_upwards [(tendsto_pow_nhdsGT hk).eventually hev] with w hw y
    have e : w ^ (q * k) = (w ^ k) ^ q := by rw [← pow_mul, mul_comm]
    rw [e, hw y]
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
      exact ⟨φ, hφ, rfl⟩

end

end Pui
end SubanalyticLib

/-! SubanalyticLib CS-5b: Newton-polygon rescaling for real Puiseux (appended to L5p_Pui). -/

namespace SubanalyticLib
namespace Pui

noncomputable section

end

end Pui
end SubanalyticLib

/-! SubanalyticLib CS-5c: real Newton–Puiseux, assembly by induction on the degree, from the local
Weierstrass factorization `LocalFactor` (proved separately from L3G's `ev_weierstrass_prep`). -/

namespace SubanalyticLib
namespace Pui

noncomputable section

end

end Pui
end SubanalyticLib

/-! SubanalyticLib CS-5d: `LocalFactor` from convergent Weierstrass preparation (L3G), hence the
real Newton–Puiseux theorem `puiseux`. Appended after L3G + L5s_WP2 + L5R (MvPowerSeries names are
qualified here because `Polynomial` is open). -/

namespace SubanalyticLib
namespace Pui

noncomputable section

/-- The two-variable function `(v, z) ↦ (pv Q v)(c + z)`. -/
def F2 (Q : Ran[X]) (c : ℝ) (x : Fin 2 → ℝ) : ℝ := (pv Q (x 0)).eval (c + x 1)

end

end Pui
end SubanalyticLib


/-! SubanalyticLib CS-4: Thom's lemma (Bochnak–Coste–Roy, Real Algebraic Geometry, Prop. 2.5.4 /
Basu–Pollack–Roy Lemma 2.37). For a finite family of real polynomials closed under derivation,
every sign condition defines an order-connected set that is a point (subsingleton) or open,
i.e. empty, a point or an open interval. -/

open Polynomial Set

set_option linter.unusedSectionVars false

namespace SubanalyticLib

/-- Relaxed sign: `t` is `s` or `0`. -/
def Relax (s t : SignType) : Prop := t = s ∨ t = 0

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-b (part 2): ends of a sign-condition cell.
Appended to L4t_Thom.lean (uses `signSet`, `relaxSet`, `Relax`, `relax_iff`, `thom`, `thom_relax`).
* eventual signs of a real polynomial at `±∞` (`eventually_sign_atTop/atBot`);
* indexed sign sets `iSign Q ev μ` / `iRelax Q ev μ` and their transfer to `signSet`/`relaxSet`;
* `iSign` eventually contains `[c,∞)` iff every code is the sign at `+∞` (`eventually_mem_iSign_atTop_iff`);
* closure of a nonempty cell = its relaxed set (`mem_closure_of_iRelax`, `closure_iSign_subset`);
* realized signs of a strictly monotone continuous function on an open interval, read off at the
  finite endpoints and at the infinite ends (`realized_pos_iff`, `realized_zero_iff`). -/

open Polynomial Set Filter Topology

namespace SubanalyticLib

section Indexed

variable {ι : Type*}

/-- Realization of a sign condition on an indexed family of polynomials. -/
def iSign (Q : Finset ι) (ev : ι → ℝ[X]) (μ : ι → SignType) : Set ℝ :=
  {x : ℝ | ∀ i ∈ Q, SignType.sign ((ev i).eval x) = μ i}

/-- Indexed derivative closure. -/
def IDerivClosed (Q : Finset ι) (ev : ι → ℝ[X]) : Prop :=
  ∀ i ∈ Q, ∃ j ∈ Q, ev j = derivative (ev i)

end Indexed

section Realized

variable {C : Set ℝ} {f : ℝ → ℝ}

end Realized

end SubanalyticLib

/-! SubanalyticLib CS-3 (Tarski–Seidenberg) infrastructure, part 1.
* `IsSA R S`: `S ⊆ A` lies in the Boolean algebra generated by `{f > 0}`, `{f = 0}` for `f` in a
  subring `R` of `A → ℝ` (polynomial functions give semialgebraic sets, analytic germs on a ball
  give semianalytic sets). Closure lemmas and finite-cover locality.
* Pseudo-division in `S[X]` over any commutative ring (with an even power of the leading
  coefficient, so that signs at the roots of the divisor are preserved). -/

open Polynomial Set

set_option linter.unusedSectionVars false

namespace SubanalyticLib

section SA

variable {A : Type*} (R : Subring (A → ℝ))

/-- Boolean algebra generated by the sign conditions of the functions in `R`. -/
inductive IsSA : Set A → Prop
  | pos {f : A → ℝ} (hf : f ∈ R) : IsSA {a | 0 < f a}
  | zero {f : A → ℝ} (hf : f ∈ R) : IsSA {a | f a = 0}
  | compl {S : Set A} : IsSA S → IsSA Sᶜ
  | inter {S T : Set A} : IsSA S → IsSA T → IsSA (S ∩ T)

variable {R}

theorem IsSA.univ : IsSA R (Set.univ : Set A) := by
  have h := IsSA.zero (R := R) (Subring.zero_mem R)
  have : {a : A | (0 : A → ℝ) a = 0} = Set.univ := by ext a; simp
  rwa [this] at h

theorem IsSA.empty : IsSA R (∅ : Set A) := by
  have h := (IsSA.univ (R := R)).compl
  rwa [Set.compl_univ] at h

theorem IsSA.union {S T : Set A} (hS : IsSA R S) (hT : IsSA R T) : IsSA R (S ∪ T) := by
  have h := (hS.compl.inter hT.compl).compl
  rwa [← Set.compl_union, compl_compl] at h

theorem IsSA.neg {f : A → ℝ} (hf : f ∈ R) : IsSA R {a | f a < 0} := by
  have h := IsSA.pos (R := R) (Subring.neg_mem R hf)
  have : {a : A | 0 < (-f) a} = {a | f a < 0} := by ext a; simp
  rwa [this] at h

theorem IsSA.ne {f : A → ℝ} (hf : f ∈ R) : IsSA R {a | f a ≠ 0} := by
  have h := (IsSA.zero (R := R) hf).compl
  exact h

theorem IsSA.sign {f : A → ℝ} (hf : f ∈ R) (s : SignType) :
    IsSA R {a | SignType.sign (f a) = s} := by
  rcases s with _ | _ | _
  · have : {a : A | SignType.sign (f a) = SignType.zero} = {a | f a = 0} := by
      ext a; simp only [mem_setOf_eq]; exact sign_eq_zero_iff
    rw [this]; exact IsSA.zero hf
  · have : {a : A | SignType.sign (f a) = SignType.neg} = {a | f a < 0} := by
      ext a; simp only [mem_setOf_eq]; exact sign_eq_neg_one_iff
    rw [this]; exact IsSA.neg hf
  · have : {a : A | SignType.sign (f a) = SignType.pos} = {a | 0 < f a} := by
      ext a; simp only [mem_setOf_eq]; exact sign_eq_one_iff
    rw [this]; exact IsSA.pos hf

theorem IsSA.biUnion {ι : Type*} (s : Finset ι) {S : ι → Set A} (h : ∀ i ∈ s, IsSA R (S i)) :
    IsSA R (⋃ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty]; exact IsSA.empty
  | insert i s hi ih =>
    rw [Finset.set_biUnion_insert]
    exact (h i (Finset.mem_insert_self i s)).union
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem IsSA.biInter {ι : Type*} (s : Finset ι) {S : ι → Set A} (h : ∀ i ∈ s, IsSA R (S i)) :
    IsSA R (⋂ i ∈ s, S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.notMem_empty, iInter_of_empty, iInter_univ]; exact IsSA.univ
  | insert i s hi ih =>
    rw [Finset.set_biInter_insert]
    exact (h i (Finset.mem_insert_self i s)).inter
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem IsSA.iUnion_fintype {ι : Type*} [Fintype ι] {S : ι → Set A} (h : ∀ i, IsSA R (S i)) :
    IsSA R (⋃ i, S i) := by
  have := IsSA.biUnion (R := R) Finset.univ (S := S) (fun i _ => h i)
  simpa using this

theorem IsSA.iInter_fintype {ι : Type*} [Fintype ι] {S : ι → Set A} (h : ∀ i, IsSA R (S i)) :
    IsSA R (⋂ i, S i) := by
  have := IsSA.biInter (R := R) Finset.univ (S := S) (fun i _ => h i)
  simpa using this

/-- Evaluation of the coefficient functions at a parameter `a`. -/
def evR (a : A) : R →+* ℝ := (Pi.evalRingHom (fun _ : A => ℝ) a).comp R.subtype

theorem evR_apply (a : A) (f : R) : evR (R := R) a f = (f : A → ℝ) a := rfl

/-- A polynomial with coefficients in `R`, specialised at the parameter `a`. -/
noncomputable def pe (p : R[X]) (a : A) : ℝ[X] := p.map (evR (R := R) a)

theorem pe_coeff (p : R[X]) (a : A) (i : ℕ) : (pe p a).coeff i = ((p.coeff i : R) : A → ℝ) a := by
  simp [pe, coeff_map, evR_apply]

end SA

section PseudoDiv

variable {S : Type*} [CommRing S]

end PseudoDiv

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-b (part 1): per-parameter cell lemmas for the Cohen–Hörmander step.
* `sign_at_root`: at a root of `q`, `P` has the sign of its pseudo-remainder by `q`.
* realized signs of a strictly increasing continuous function on an open order-connected set
  `C`, read off from its eventual signs at the two ends of `C` (filters `atBot`/`atTop` of the
  subtype `C`). -/

open Polynomial Set Filter

set_option linter.unusedSectionVars false

namespace SubanalyticLib

section Realized

variable {C : Set ℝ} {f : ℝ → ℝ}

end Realized

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-c: parametric families, codes, the (max degree, count) measure and
normalisation by truncation (so that formal degree = effective degree on each branch).
Appended to L4TB.lean (= L4t_Thom + L4tc_Ends + L4s_SA + L4tb_Cells). -/

open Polynomial Set Filter

namespace SubanalyticLib

section TSc

open scoped Classical

variable {A : Type*} {R : Subring (A → ℝ)} {ι : Type*}

/-- Parameters at which the sign condition `ν` on the specialised family is realized. -/
def Rlz (F : Finset ι) (ev : ι → R[X]) (ν : ι → SignType) : Set A :=
  {a | (iSign F (fun i => pe (ev i) a) ν).Nonempty}

/-- Derivative-closed at every parameter of `B`. -/
def DCl (F : Finset ι) (ev : ι → R[X]) (B : Set A) : Prop :=
  ∀ a ∈ B, IDerivClosed F (fun i => pe (ev i) a)

/-- Formal degree = effective degree on `B` (or the polynomial is formally zero). -/
def Nrm (F : Finset ι) (ev : ι → R[X]) (B : Set A) : Prop :=
  ∀ i ∈ F, ∀ a ∈ B, (((ev i).leadingCoeff : R) : A → ℝ) a ≠ 0 ∨ ev i = 0

/-- Codes on `s`, extended by `0`. -/
noncomputable def codes (s : Finset ι) : Finset (ι → SignType) :=
  (Finset.univ : Finset (s → SignType)).image (fun c i => if h : i ∈ s then c ⟨i, h⟩ else 0)

/-- Maximal formal degree. -/
noncomputable def mdeg (F : Finset ι) (ev : ι → R[X]) : ℕ := F.sup fun i => (ev i).natDegree

end TSc

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-d (part 1): data of one Cohen–Hörmander elimination step.
A normalised derivative-closed family `F`, a member `iP` of maximal degree `d ≥ 1`,
`Q = F.erase iP`, pseudo-remainders `rem q` of `P` by each nonconstant `q ∈ Q`, and the new
family `F' = Q ⊕ {derivatives of the remainders}` (index type `ι ⊕ (ι × ℕ)`), which has
smaller (max degree, count) measure. Appended to L4TD.lean. -/

open Polynomial Set Filter

namespace SubanalyticLib

section TSd

open scoped Classical

variable {A : Type*} {R : Subring (A → ℝ)} {ι : Type*}

/-- Data of one elimination step on the branch `B`. -/
structure SD (F : Finset ι) (ev : ι → R[X]) (B : Set A) where
  iP : ι
  hiP : iP ∈ F
  hdeg : (ev iP).natDegree = mdeg F ev
  hpos : 0 < mdeg F ev
  rem : ι → R[X]
  kk : ι → ℕ
  ss : ι → R[X]
  hrem : ∀ i, 0 < (ev i).natDegree →
    (ev i).leadingCoeff ^ (2 * kk i) • ev iP = ss i * ev i + rem i ∧
      (rem i).natDegree < (ev i).natDegree
  hN : Nrm F ev B
  hD : DCl F ev B

/-- New index set. -/
noncomputable def Fp (Q : Finset ι) (ev : ι → R[X]) (d : ℕ) : Finset (ι ⊕ (ι × ℕ)) :=
  Q.disjSum ((Q.filter fun i => 0 < (ev i).natDegree) ×ˢ Finset.range (d + 1))

/-- New family. -/
noncomputable def evp (ev rem : ι → R[X]) : ι ⊕ (ι × ℕ) → R[X] :=
  Sum.elim ev (fun x => derivative^[x.2] (rem x.1))

variable {F : Finset ι} {ev : ι → R[X]} {B : Set A}

namespace SD

variable (S : SD F ev B)

/-- The rest of the family. -/
noncomputable def Q : Finset ι := F.erase S.iP

/-- The new family's index set. -/
noncomputable def F' : Finset (ι ⊕ (ι × ℕ)) := Fp S.Q ev (mdeg F ev)

/-- The new family. -/
noncomputable def ev' : ι ⊕ (ι × ℕ) → R[X] := evp ev S.rem

end SD

end TSd

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-d (part 2): the per-parameter case analysis of one step.
Case A (some nonconstant `q ∈ Q` must vanish): replace `P` by its remainder.
Case B0 (a nonzero constant must vanish): empty.
Case C (only formally-zero members may vanish): the cell `C` of `Q` is an open interval on
which `P` is strictly monotone; realized signs of `P` are read off at the finite endpoints
(codes of `F'`, `T1`) and at `±∞` (leading coefficients, `T2`/`T3`). Appended to L4TE.lean. -/

open Polynomial Set Filter

namespace SubanalyticLib

section TSd2

open scoped Classical

variable {A : Type*} {R : Subring (A → ℝ)} {ι : Type*}

variable {F : Finset ι} {ev : ι → R[X]} {B : Set A}

namespace SD

variable (S : SD F ev B)

/-- Endpoint codes: relax `ν` on `Q`, one nonconstant `q` with strict code drops to `0`, and the
remainder of `P` by `q` has sign `s`. -/
def good (ν : ι → SignType) (s : SignType) (c : ι ⊕ (ι × ℕ) → SignType) : Prop :=
  (∀ i ∈ S.Q, Relax (ν i) (c (Sum.inl i))) ∧
    ∃ q ∈ S.Q, 0 < (ev q).natDegree ∧ ν q ≠ 0 ∧ c (Sum.inl q) = 0 ∧ c (Sum.inr (q, 0)) = s

end SD

end TSd2

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-d (part 3): assembly. One elimination step is SA given the
induction hypothesis on `Q` and `F'`; well-founded induction on `(max degree, count)` with
normalisation gives the **parametric one-variable Tarski–Seidenberg theorem** `ts`:
for a derivative-closed (at every parameter) finite family of polynomials in one variable with
coefficients in a subring `R` of `A → ℝ`, every realizable-sign-condition set
`{a | ∃ y, ∀ i ∈ F, sign ((pe (ev i) a).eval y) = ν i}` is in the Boolean algebra generated by
`{f > 0}`, `{f = 0}`, `f ∈ R`. Appended to L4TF.lean. -/

open Polynomial Set Filter

namespace SubanalyticLib

section TSd3

open scoped Classical

variable {A : Type*} {R : Subring (A → ℝ)} {ι : Type*}

variable {F : Finset ι} {ev : ι → R[X]} {B : Set A}

namespace SD

variable (S : SD F ev B)

/-- Parameters with a good endpoint code. -/
def U (ν : ι → SignType) (s : SignType) : Set A :=
  {a | ∃ c ∈ codes S.F', S.good ν s c ∧ a ∈ Rlz S.F' S.ev' c}

end SD

end TSd3

end SubanalyticLib

/-! SubanalyticLib CS-3 TS-e: Tarski–Seidenberg for an arbitrary finite family (close it under
derivatives first). Appended to L4TG.lean. -/

open Polynomial Set Filter

namespace SubanalyticLib

section TSe

open scoped Classical

variable {A : Type*} {R : Subring (A → ℝ)}

/-- **Parametric Tarski–Seidenberg in one variable**, any finite family. -/
theorem ts_any {κ : Type} (F : Finset κ) (ev : κ → R[X]) (ν : κ → SignType) :
    IsSA R (Rlz (A := A) F ev ν) := by
  exact NonsmoothLojasiewicz.Continuous.tarski_seidenberg_parametric R F ev ν {S | IsSA R S}
    (fun f hf => IsSA.pos hf) (fun S hS => IsSA.compl hS) (fun S hS T hT => IsSA.inter hS hT)

end TSe

end SubanalyticLib


/-! SubanalyticLib CS-6a: sign-code normal form of `IsSA` sets; monotonicity in the ring.
(Appended to L4s_SA.lean.) -/

namespace SubanalyticLib

section Code

variable {A : Type*}

/-- `S` is the set where the sign vector of finitely many functions of `R` lies in `N`. -/
def CodeForm (R : Subring (A → ℝ)) (S : Set A) : Prop :=
  ∃ (n : ℕ) (h : Fin n → A → ℝ), (∀ i, h i ∈ R) ∧
    ∃ N : Set (Fin n → SignType), S = {a | (fun i => SignType.sign (h i a)) ∈ N}

theorem IsSA.mono {R R' : Subring (A → ℝ)} (hRR : R ≤ R') {S : Set A} (hS : IsSA R S) :
    IsSA R' S := by
  induction hS with
  | pos hf => exact IsSA.pos (hRR hf)
  | zero hf => exact IsSA.zero (hRR hf)
  | compl _ ih => exact IsSA.compl ih
  | inter _ _ ih1 ih2 => exact IsSA.inter ih1 ih2

theorem IsSA.codeForm {R : Subring (A → ℝ)} {S : Set A} (hS : IsSA R S) : CodeForm R S := by
  induction hS with
  | @pos f hf =>
    refine ⟨1, ![f], fun i => by fin_cases i; exact hf, {c | c 0 = 1}, ?_⟩
    ext a
    simp [sign_eq_one_iff]
  | @zero f hf =>
    refine ⟨1, ![f], fun i => by fin_cases i; exact hf, {c | c 0 = 0}, ?_⟩
    ext a
    simp [sign_eq_zero_iff]
  | compl _ ih =>
    obtain ⟨n, h, hh, N, hN⟩ := ih
    refine ⟨n, h, hh, Nᶜ, ?_⟩
    rw [hN]
    rfl
  | inter _ _ ih1 ih2 =>
    obtain ⟨n, h, hh, N, hN⟩ := ih1
    obtain ⟨m, g, hg, M, hM⟩ := ih2
    refine ⟨n + m, Fin.append h g, fun i => ?_,
      {c | (fun i => c (Fin.castAdd m i)) ∈ N ∧ (fun j => c (Fin.natAdd n j)) ∈ M}, ?_⟩
    · refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hh i
      · rw [Fin.append_right]; exact hg j
    · rw [hN, hM]
      ext a
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Fin.append_left, Fin.append_right]

theorem CodeForm.isSA {R : Subring (A → ℝ)} {S : Set A} (hS : CodeForm R S) : IsSA R S := by
  classical
  obtain ⟨n, h, hh, N, rfl⟩ := hS
  have e : {a | (fun i => SignType.sign (h i a)) ∈ N} =
      ⋃ c ∈ N.toFinset, ⋂ i, {a | SignType.sign (h i a) = c i} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter, Set.mem_toFinset, exists_prop]
    constructor
    · intro ha
      exact ⟨_, ha, fun i => rfl⟩
    · rintro ⟨c, hc, hca⟩
      have : (fun i => SignType.sign (h i a)) = c := funext hca
      rw [this]
      exact hc
  rw [e]
  exact IsSA.biUnion _ fun c _ => IsSA.iInter_fintype fun i => IsSA.sign (hh i) (c i)

end Code

end SubanalyticLib


/-! SubanalyticLib CS-1: a non-zero analytic germ becomes regular in a coordinate after a
linear change of coordinates (a shear), the first step of every Weierstrass-preparation induction. -/

open Filter Topology Set

set_option linter.unusedSectionVars false

namespace SubanalyticLib

/-- A germ that is not `≡ 0` near `0` is not `≡ 0` along some line through `0`. -/
theorem exists_dir_nonzero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : AnalyticAt ℝ f 0) (hnz : ¬ ∀ᶠ x in 𝓝 (0 : E), f x = 0) :
    ∃ v : E, ¬ ∀ᶠ t in 𝓝 (0 : ℝ), f (t • v) = 0 := by
  by_contra hall
  push Not at hall
  apply hnz
  obtain ⟨r, hr, hball⟩ := hf.exists_ball_analyticOnNhd
  filter_upwards [Metric.ball_mem_nhds (0 : E) hr] with x hx
  set U : Set ℝ := {t : ℝ | t • x ∈ Metric.ball (0 : E) r} with hU
  have hUo : IsOpen U :=
    Metric.isOpen_ball.preimage (continuous_id.smul continuous_const)
  have hUc : Convex ℝ U := by
    have hUeq : U = (LinearMap.toSpanSingleton ℝ E x) ⁻¹' Metric.ball 0 r := by
      ext t; simp [hU]
    rw [hUeq]
    exact (convex_ball (0 : E) r).linear_preimage (LinearMap.toSpanSingleton ℝ E x)
  have h0 : (0 : ℝ) ∈ U := by simp [hU, hr]
  have h1 : (1 : ℝ) ∈ U := by simpa [hU] using hx
  have han : AnalyticOnNhd ℝ (fun t : ℝ => f (t • x)) U := by
    intro t ht
    have hlin : AnalyticAt ℝ (fun t : ℝ => t • x) t :=
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) x).analyticAt t
    exact AnalyticAt.comp (g := f) (f := fun t : ℝ => t • x) (hball (t • x) ht) hlin
  have hev : (fun t : ℝ => f (t • x)) =ᶠ[𝓝 0] 0 := hall x
  have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc.isPreconnected h0 hev h1
  simpa using this

/-- The shear `x ↦ x + x k • w` (with `w k = 0`) as a continuous linear equivalence. -/
noncomputable def shear {σ : Type*} [Fintype σ] [DecidableEq σ] (k : σ) (w : σ → ℝ) (hw : w k = 0) :
    (σ → ℝ) ≃L[ℝ] (σ → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => x + x k • w
      map_add' := by intro x y; simp only [Pi.add_apply, add_smul]; abel
      map_smul' := by intro c x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
        smul_add, mul_smul]
      invFun := fun x => x - x k • w
      left_inv := by intro x; simp [hw]
      right_inv := by intro x; simp [hw] }

theorem shear_apply {σ : Type*} [Fintype σ] [DecidableEq σ] (k : σ) (w : σ → ℝ) (hw : w k = 0)
    (x : σ → ℝ) : shear k w hw x = x + x k • w := rfl

/-- **Generic regularity.** A non-zero analytic germ on `σ → ℝ` becomes regular in some coordinate
`k` (not `≡ 0` on the `k`-axis) after a linear change of coordinates. -/
theorem exists_regular_coord {σ : Type*} [Fintype σ] [DecidableEq σ] [Nonempty σ]
    {f : (σ → ℝ) → ℝ} (hf : AnalyticAt ℝ f 0) (hnz : ¬ ∀ᶠ x in 𝓝 (0 : σ → ℝ), f x = 0) :
    ∃ k : σ, ∃ L : (σ → ℝ) ≃L[ℝ] (σ → ℝ),
      ¬ ∀ᶠ t in 𝓝 (0 : ℝ), f (L (Pi.single k t)) = 0 := by
  obtain ⟨v, hv⟩ := exists_dir_nonzero hf hnz
  by_cases hv0 : v = 0
  · -- f 0 ≠ 0: any coordinate, identity map
    obtain ⟨k⟩ := ‹Nonempty σ›
    refine ⟨k, ContinuousLinearEquiv.refl ℝ _, ?_⟩
    intro h; apply hv
    have hf0 : f 0 = 0 := by
      have := h.self_of_nhds
      simpa using this
    filter_upwards with t
    simp [hv0, hf0]
  · obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra hcon; push Not at hcon; exact hv0 (funext hcon)
    set w : σ → ℝ := (v k)⁻¹ • v - Pi.single k 1 with hw
    have hwk : w k = 0 := by simp [hw, hk]
    refine ⟨k, shear k w hwk, ?_⟩
    intro h
    apply hv
    have hL : ∀ t : ℝ, shear k w hwk (Pi.single k t) = (t * (v k)⁻¹) • v := by
      intro t
      rw [shear_apply]
      ext i
      by_cases hi : i = k
      · subst hi; simp [hw, hk]
      · simp [hw, hi]
        ring
    -- reparametrize t ↦ t * v k
    have hmap : Tendsto (fun t : ℝ => t * v k) (𝓝 0) (𝓝 0) := by
      have := (tendsto_id (x := 𝓝 (0:ℝ))).mul_const (v k)
      simpa using this
    filter_upwards [hmap.eventually h] with t ht
    rw [hL] at ht
    have : t * v k * (v k)⁻¹ = t := by field_simp
    rwa [this] at ht

end SubanalyticLib


/-! SubanalyticLib CS-6b: germs of real-analytic functions form an integral domain
(a product of two non-flat analytic germs is non-flat). Standalone. -/

open Filter Topology Set

set_option autoImplicit false

namespace SubanalyticLib

theorem nonflat_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x₀ : E} (hf : AnalyticAt ℝ f x₀) (hg : AnalyticAt ℝ g x₀)
    (hf0 : ¬ ∀ᶠ x in 𝓝 x₀, f x = 0) (hg0 : ¬ ∀ᶠ x in 𝓝 x₀, g x = 0) :
    ¬ ∀ᶠ x in 𝓝 x₀, f x * g x = 0 := by
  intro hfg
  obtain ⟨r1, hr1, hfA⟩ := hf.exists_ball_analyticOnNhd
  obtain ⟨r2, hr2, hgA⟩ := hg.exists_ball_analyticOnNhd
  obtain ⟨r3, hr3, hball⟩ := Metric.eventually_nhds_iff_ball.mp hfg
  set r := min r1 (min r2 r3) with hr
  have hr0 : 0 < r := lt_min hr1 (lt_min hr2 hr3)
  have hrr1 : r ≤ r1 := min_le_left _ _
  have hrr3 : r ≤ r3 := (min_le_right _ _).trans (min_le_right _ _)
  -- a point of the ball where g ≠ 0
  have hx1 : ∃ x1 ∈ Metric.ball x₀ r, g x1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hg0 (Filter.mem_of_superset (Metric.ball_mem_nhds x₀ hr0) fun x hx => hcon x hx)
  obtain ⟨x1, hx1B, hgx1⟩ := hx1
  -- near x1, g ≠ 0, so f = 0
  have hfz : f =ᶠ[𝓝 x1] 0 := by
    have hgc : ∀ᶠ x in 𝓝 x1, g x ≠ 0 :=
      (hgA x1 (Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) hx1B)
        ).continuousAt.eventually_ne hgx1
    filter_upwards [hgc, Metric.isOpen_ball.mem_nhds hx1B] with x hgx hxB
    have := hball x (Metric.ball_subset_ball hrr3 hxB)
    exact (mul_eq_zero.mp this).resolve_right hgx
  have hEq : EqOn f 0 (Metric.ball x₀ r) :=
    (hfA.mono (Metric.ball_subset_ball hrr1)).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball x₀ r).isPreconnected hx1B hfz
  exact hf0 (Filter.mem_of_superset (Metric.ball_mem_nhds x₀ hr0) fun x hx => hEq hx)

/-- A finite product of non-flat analytic germs is non-flat. -/
theorem nonflat_prod {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (s : Finset ι) {f : ι → E → ℝ} {x₀ : E} (hf : ∀ i ∈ s, AnalyticAt ℝ (f i) x₀)
    (hf0 : ∀ i ∈ s, ¬ ∀ᶠ x in 𝓝 x₀, f i x = 0) :
    AnalyticAt ℝ (fun x => ∏ i ∈ s, f i x) x₀ ∧ ¬ ∀ᶠ x in 𝓝 x₀, ∏ i ∈ s, f i x = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using analyticAt_const, ?_⟩
    simp only [Finset.prod_empty, one_ne_zero, Filter.eventually_false_iff_eq_bot]
    exact NeBot.ne inferInstance
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hf0 i (Finset.mem_insert_of_mem hi))
    have hA := hf a (Finset.mem_insert_self a s)
    simp only [Finset.prod_insert ha]
    exact ⟨hA.mul ih1, nonflat_mul hA ih1 (hf0 a (Finset.mem_insert_self a s)) ih2⟩

end SubanalyticLib


/-! SubanalyticLib CS-6 shared: the subring `An n` of germs analytic at `0` on `ℝ^n` (body; needs nothing). -/

namespace SubanalyticLib

/-- germs of functions on `ℝ^n` analytic at `0`. -/
def An (n : ℕ) : Subring ((Fin n → ℝ) → ℝ) where
  carrier := {f | AnalyticAt ℝ f 0}
  mul_mem' {a b} ha hb := by
    show AnalyticAt ℝ (fun x => a x * b x) 0
    exact ha.mul hb
  one_mem' := by
    show AnalyticAt ℝ (fun _ => (1 : ℝ)) 0
    exact analyticAt_const
  add_mem' {a b} ha hb := by
    show AnalyticAt ℝ (fun x => a x + b x) 0
    exact ha.add hb
  zero_mem' := by
    show AnalyticAt ℝ (fun _ => (0 : ℝ)) 0
    exact analyticAt_const
  neg_mem' {a} ha := by
    show AnalyticAt ℝ (fun x => -a x) 0
    exact ha.neg

theorem mem_An {n : ℕ} {f : (Fin n → ℝ) → ℝ} : f ∈ An n ↔ AnalyticAt ℝ f 0 := Iff.rfl

lemma snoc_zero_zero (n : ℕ) : (Fin.snoc (0 : Fin n → ℝ) (0 : ℝ) : Fin (n + 1) → ℝ) = 0 := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

end SubanalyticLib


/-! SubanalyticLib CS-6c (body; after L5S-prefix (L3G + WP2) + L6S + L5g + L6b): local polynomial normal form.
Finitely many analytic germs `h k` at `0 ∈ ℝ^(n+1)`: after one linear change of coordinates `L`, on a ball,
`sign (h k (L x)) = ε k * sign (P k (x', y))` with `P k` monic in `y = x (last n)`, coefficients analytic germs
in `x' = Fin.init x` vanishing at `0` (distinguished); flat germs get `ε k = 0`, `P k = 1`. -/

namespace SubanalyticLib

section Form

open Filter Topology Set Polynomial

set_option autoImplicit false

/-- monic polynomial `X^d + Σ_{i<d} b_i X^i` over any commutative ring. -/
noncomputable def mkMon {S : Type*} [CommRing S] (d : ℕ) (b : Fin d → S) : S[X] :=
  X ^ d + ∑ i : Fin d, C (b i) * X ^ (i : ℕ)

lemma mkMon_monic {S : Type*} [CommRing S] [Nontrivial S] (d : ℕ) (b : Fin d → S) :
    (mkMon d b).Monic :=
  monic_X_pow_add (degree_sum_fin_lt b)

lemma mkMon_natDegree {S : Type*} [CommRing S] [Nontrivial S] (d : ℕ) (b : Fin d → S) :
    (mkMon d b).natDegree = d := by
  unfold mkMon
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_sum_fin_lt b

lemma mkMon_coeff {S : Type*} [CommRing S] (d : ℕ) (b : Fin d → S) {j : ℕ} (hj : j < d) :
    (mkMon d b).coeff j = b ⟨j, hj⟩ := by
  unfold mkMon
  rw [coeff_add, coeff_X_pow, if_neg hj.ne, zero_add, finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single ⟨j, hj⟩]
  · simp
  · intro i _ hi
    rw [if_neg]
    intro h; apply hi; ext; exact h.symm
  · intro h; exact absurd (Finset.mem_univ _) h

lemma eval_pe_mkMon {A : Type*} {R : Subring (A → ℝ)} (d : ℕ) (b : Fin d → R) (a : A) (z : ℝ) :
    (pe (mkMon d b) a).eval z = z ^ d + ∑ i : Fin d, (b i : A → ℝ) a * z ^ (i : ℕ) := by
  simp [pe, mkMon, eval_map, eval₂_finset_sum, evR_apply]

/-- a positive lower bound for finitely many positive numbers. -/
lemma exists_pos_le_all {ι : Type*} [Fintype ι] (ρ : ι → ℝ) (h : ∀ k, 0 < ρ k) :
    ∃ r > 0, ∀ k, r ≤ ρ k := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun k => (IsEmpty.false k).elim⟩
  · obtain ⟨k0, -, hk0⟩ := Finset.exists_min_image Finset.univ ρ Finset.univ_nonempty
    exact ⟨ρ k0, h k0, fun k => hk0 k (Finset.mem_univ _)⟩

/-- a continuous function without zeros on a ball has constant sign there. -/
lemma sign_const_ball {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {ρ : ℝ}
    (hc : ContinuousOn f (Metric.ball 0 ρ)) (hne : ∀ x ∈ Metric.ball (0 : E) ρ, f x ≠ 0)
    {x : E} (hx : x ∈ Metric.ball (0 : E) ρ) : SignType.sign (f x) = SignType.sign (f 0) := by
  have h0 : (0 : E) ∈ Metric.ball (0 : E) ρ := by
    have : 0 < ρ := by
      have := Metric.mem_ball.1 hx
      exact lt_of_le_of_lt dist_nonneg this
    exact Metric.mem_ball_self this
  have hpc : IsPreconnected (Metric.ball (0 : E) ρ) := (convex_ball 0 ρ).isPreconnected
  have hx0 := hne x hx
  have h00 := hne 0 h0
  rcases lt_or_gt_of_ne hx0 with hxn | hxp <;> rcases lt_or_gt_of_ne h00 with h0n | h0p
  · rw [sign_neg hxn, sign_neg h0n]
  · exfalso
    obtain ⟨z, hz, hz0⟩ := hpc.intermediate_value hx h0 hc ⟨hxn.le, h0p.le⟩
    exact hne z hz hz0
  · exfalso
    obtain ⟨z, hz, hz0⟩ := hpc.intermediate_value h0 hx hc ⟨h0n.le, hxp.le⟩
    exact hne z hz hz0
  · rw [sign_pos hxp, sign_pos h0p]

lemma analyticAt_snoc0 (n : ℕ) :
    AnalyticAt ℝ (fun x' : Fin n → ℝ => (Fin.snoc x' (0 : ℝ) : Fin (n + 1) → ℝ)) 0 := by
  refine analyticAt_pi_iff.2 fun i => ?_
  induction i using Fin.lastCases with
  | last => simpa using (analyticAt_const : AnalyticAt ℝ (fun _ : Fin n → ℝ => (0 : ℝ)) 0)
  | cast j =>
    simp only [Fin.snoc_castSucc]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).analyticAt _

lemma sign_mul_cancel {ε s t : SignType} (hε : ε ≠ 0) (h : t = ε * s) : s = ε * t := by
  subst h
  rcases ε with _ | _ | _
  · exact absurd rfl hε
  · rcases s with _ | _ | _ <;> rfl
  · rcases s with _ | _ | _ <;> rfl

/-- **Local polynomial form of one regular germ.** -/
theorem local_form_one {n : ℕ} {g : (Fin (n + 1) → ℝ) → ℝ} (hg : AnalyticAt ℝ g 0)
    (hax : ¬ ∀ᶠ t in 𝓝 (0 : ℝ), g (Pi.single (Fin.last n) t) = 0) :
    ∃ ρ > 0, ∃ P : (An n)[X], P.Monic ∧
      (∀ i < P.natDegree, ((P.coeff i : An n) : (Fin n → ℝ) → ℝ) 0 = 0) ∧
      ∃ ε : SignType, ∀ x : Fin (n + 1) → ℝ, ‖x‖ < ρ →
        SignType.sign (g x) = ε * SignType.sign ((pe P (Fin.init x)).eval (x (Fin.last n))) := by
  classical
  set y : Fin (n + 1) := Fin.last n with hy
  obtain ⟨a, ρ0, hρ0, hconv, heq⟩ := exists_conv_of_analyticAt hg
  have hex : ∃ j, MvPowerSeries.coeff (Finsupp.single y j) a ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hax
    have hball : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < ρ0 := by
      have := (continuous_abs.tendsto (0 : ℝ))
      simp only [abs_zero] at this
      exact this.eventually (gt_mem_nhds hρ0)
    filter_upwards [hball] with t ht
    have hn : ‖(Pi.single y t : Fin (n + 1) → ℝ)‖ ≤ ρ0 := by
      rw [Pi.norm_single, Real.norm_eq_abs]; exact ht.le
    have := heq _ hn
    rw [zero_add] at this
    rw [this]
    exact ev_single_axis y hcon t
  let d := Nat.find hex
  have hd : MvPowerSeries.coeff (Finsupp.single y d) a ≠ 0 := Nat.find_spec hex
  have hreg : ∀ j < d, MvPowerSeries.coeff (Finsupp.single y j) a = 0 := by
    intro j hj
    by_contra h
    exact Nat.find_min hex hj h
  obtain ⟨w, hw, hwle, q, r, hq, hr, hhat, hr0, hmain⟩ :=
    ev_weierstrass_prep2 y (fun _ => hρ0) d hconv hreg hd
  have hw' : ∀ i, 0 ≤ w i := fun i => (hw i).le
  -- coefficient germs
  have hsl : ∀ j, Conv w (yslice y j r) := fun j => Conv.low y hw' 1 (Conv.hat y hw' (hw y) j hr)
  let c : ℕ → (Fin n → ℝ) → ℝ := fun j x' => ev (yslice y j r) (Fin.snoc x' 0)
  have hcA : ∀ j, c j ∈ An n := by
    intro j
    obtain ⟨r1, hr1, hr1a⟩ := analyticAt_ev_zero hw (hsl j)
    have h0 : AnalyticAt ℝ (ev (yslice y j r)) 0 := hr1a 0 (by simpa using hr1)
    exact h0.comp_of_eq (analyticAt_snoc0 n) (snoc_zero_zero n)
  have hc0 : ∀ j < d, c j 0 = 0 := by
    intro j hj
    show ev (yslice y j r) (Fin.snoc 0 0) = 0
    rw [snoc_zero_zero, ev_zero_pt, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      coeff_yslice]
    simp [hr0 j hj]
  have hcx : ∀ j (x : Fin (n + 1) → ℝ), ev (yslice y j r) x = c j (Fin.init x) := by
    intro j x
    show _ = ev (yslice y j r) (Fin.snoc (Fin.init x) 0)
    have e1 : Function.update (Fin.snoc (Fin.init x) (0 : ℝ) : Fin (n + 1) → ℝ) (Fin.last n)
        (x (Fin.last n)) = x := by
      rw [Fin.update_snoc_last (α := fun _ => ℝ), Fin.snoc_init_self (α := fun _ => ℝ)]
    conv_lhs => rw [← e1]
    exact ev_yslice_update y j r _ _
  let b : Fin d → An n := fun i => ⟨fun x' => -c i x', (hcA i).neg⟩
  set P : (An n)[X] := mkMon d b with hP
  obtain ⟨r1, hr1, hr1a⟩ := analyticAt_ev_zero hw hq
  obtain ⟨wm, hwm, hwmle⟩ := exists_pos_le_all w hw
  have hq0 : ev q 0 ≠ 0 := (hmain 0 (fun i => by simpa using hw' i)).1
  refine ⟨min wm r1, lt_min hwm hr1, P, mkMon_monic d b, ?_, SignType.sign (ev q 0), ?_⟩
  · intro i hi
    rw [hP, mkMon_natDegree] at hi
    rw [hP, mkMon_coeff d b hi]
    show -c i 0 = 0
    rw [hc0 i hi, neg_zero]
  · have hbd : ∀ z : Fin (n + 1) → ℝ, ‖z‖ < min wm r1 → ∀ i, |z i| ≤ w i := fun z hz i => by
      have := norm_le_pi_norm z i
      rw [Real.norm_eq_abs] at this
      exact this.trans (hz.le.trans ((min_le_left _ _).trans (hwmle i)))
    intro x hx
    obtain ⟨hqx, hmx⟩ := hmain x (hbd x hx)
    have hgx : g x = ev a x := by
      have hn : ‖x‖ ≤ ρ0 := hx.le.trans ((min_le_left _ _).trans ((hwmle y).trans (hwle y)))
      simpa using heq x hn
    have hrx : ev r x = ∑ j ∈ Finset.range d, x y ^ j * ev (yslice y j r) x :=
      ev_eq_sum_yslice y d hw' (hw y) hr hhat (hbd x hx)
    have hPx : (pe P (Fin.init x)).eval (x y) = ev q x * g x := by
      rw [hP, eval_pe_mkMon, hgx]
      have hs : ∑ i : Fin d, ((b i : An n) : (Fin n → ℝ) → ℝ) (Fin.init x) * x y ^ (i : ℕ)
          = - ev r x := by
        rw [hrx, ← Finset.sum_neg_distrib,
          ← Fin.sum_univ_eq_sum_range (fun j => -(x y ^ j * ev (yslice y j r) x)) d]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcx]
        show -c i (Fin.init x) * _ = _
        ring
      rw [hs]
      linarith
    have hsq : SignType.sign (ev q x) = SignType.sign (ev q 0) := by
      refine sign_const_ball (ρ := min wm r1) ?_ ?_ ?_
      · intro z hz
        rw [Metric.mem_ball, dist_zero_right] at hz
        exact (hr1a z (hz.trans_le (min_le_right _ _))).continuousAt.continuousWithinAt
      · intro z hz
        rw [Metric.mem_ball, dist_zero_right] at hz
        exact (hmain z (hbd z hz)).1
      · rw [Metric.mem_ball, dist_zero_right]; exact hx
    refine sign_mul_cancel (sign_ne_zero.2 hq0) ?_
    rw [hPx, sign_mul, hsq]

/-- swap of two coordinates as a continuous linear equivalence. -/
noncomputable def coordSwap {m : ℕ} (k l : Fin m) : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv (LinearEquiv.funCongrLeft ℝ ℝ (Equiv.swap k l))

lemma coordSwap_single {m : ℕ} (k l : Fin m) (t : ℝ) :
    coordSwap k l (Pi.single l t) = Pi.single k t := by
  funext i
  show (Pi.single l t : Fin m → ℝ) (Equiv.swap k l i) = _
  simp only [Pi.single_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]

end Form

end SubanalyticLib


/-! SubanalyticLib CS-6d/6e (body; after L5p_Pui (or L5S) + L6S + L6_An.body): curve selection for
`IsSA (An n)` germs at `0`, by induction on `n`, from three inputs stated as Props
(local polynomial form `LFStmt` = CS-6c `local_form`, one-variable Tarski–Seidenberg `TSStmt` = `ts_any`,
real Puiseux `PuiStmt` = `Pui.puiseux`). Lift along an arc: candidates = Puiseux branches, their
midpoints, branch ± v, and 0; each candidate's sign code is eventually constant. -/

namespace SubanalyticLib

section Lift

open Filter Topology Set Polynomial

set_option autoImplicit false

end Lift

end SubanalyticLib


/-! SubanalyticLib CS-6f (body; last): the three inputs of `csg_all` discharged by `local_form`,
`ts_any`, `Pui.puiseux`: curve selection for `IsSA (An n)` sets at `0`, every `n`. -/

namespace SubanalyticLib

section CSfinal

open Filter Topology Set Polynomial

end CSfinal

end SubanalyticLib

end L6Fwrap


/-! SubanalyticLib G4c part 1 (route G): the class `Λ p` of D-functions on `ℝ^p` (coordinates,
constants, ring operations, the restricted quotient `Dfn`, restricted analytic composition on a box),
substitution, local agreement with analytic functions, and locally-Λ sets (`LocLam`). -/

namespace SubanalyticLib

section Lam

open Filter Topology

/-- the restricted quotient `D(u,v) = u/v` if `|u| ≤ |v|` and `v ≠ 0`, else `0`. -/
noncomputable def Dfn (u v : ℝ) : ℝ := if |u| ≤ |v| ∧ v ≠ 0 then u / v else 0

theorem abs_Dfn_le (u v : ℝ) : |Dfn u v| ≤ 1 := by
  unfold Dfn
  split_ifs with h
  · rw [abs_div]
    exact div_le_one_of_le₀ h.1 (abs_nonneg _)
  · simp

theorem Dfn_eq {u v : ℝ} (huv : |u| ≤ |v|) (hv : v ≠ 0) : Dfn u v = u / v := by
  unfold Dfn
  rw [if_pos ⟨huv, hv⟩]

theorem mul_Dfn {u v : ℝ} (huv : |u| ≤ |v|) (hv : v ≠ 0) : v * Dfn u v = u := by
  rw [Dfn_eq huv hv]
  field_simp

open Classical in
/-- restricted analytic composition: `H (h x)` if `h x` lies in the box `Icc lo hi`, else `0`. -/
noncomputable def rcomp {p q : ℕ} (H : (Fin q → ℝ) → ℝ) (lo hi : Fin q → ℝ)
    (h : Fin q → (Fin p → ℝ) → ℝ) : (Fin p → ℝ) → ℝ :=
  fun x => if (fun j => h j x) ∈ Set.Icc lo hi then H (fun j => h j x) else 0

/-- the D-function class `Λ p`. -/
inductive InLam (p : ℕ) : ((Fin p → ℝ) → ℝ) → Prop
  | coord (i : Fin p) : InLam p (fun x => x i)
  | const (c : ℝ) : InLam p (fun _ => c)
  | add {f g : (Fin p → ℝ) → ℝ} : InLam p f → InLam p g → InLam p (f + g)
  | mul {f g : (Fin p → ℝ) → ℝ} : InLam p f → InLam p g → InLam p (f * g)
  | neg {f : (Fin p → ℝ) → ℝ} : InLam p f → InLam p (-f)
  | dfn {f g : (Fin p → ℝ) → ℝ} : InLam p f → InLam p g → InLam p (fun x => Dfn (f x) (g x))
  | rcomp {q : ℕ} (H : (Fin q → ℝ) → ℝ) (lo hi : Fin q → ℝ)
      (hH : ∀ w ∈ Set.Icc lo hi, AnalyticAt ℝ H w) (h : Fin q → (Fin p → ℝ) → ℝ)
      (hh : ∀ j, InLam p (h j)) : InLam p (rcomp H lo hi h)

/-- `Λ p` as a subring of `ℝ^p → ℝ`. -/
def Lam (p : ℕ) : Subring ((Fin p → ℝ) → ℝ) where
  carrier := {f | InLam p f}
  mul_mem' := InLam.mul
  one_mem' := InLam.const 1
  add_mem' := InLam.add
  zero_mem' := InLam.const 0
  neg_mem' := InLam.neg

/-- **Substitution**: `f ∈ Λ r`, `z_1..z_r ∈ Λ p` ⟹ `f ∘ z ∈ Λ p`. -/
theorem InLam.subst {r p : ℕ} {f : (Fin r → ℝ) → ℝ} (hf : InLam r f)
    {z : Fin r → (Fin p → ℝ) → ℝ} (hz : ∀ j, InLam p (z j)) :
    InLam p (fun x => f (fun j => z j x)) := by
  induction hf with
  | coord i => exact hz i
  | const c => exact InLam.const c
  | add _ _ ihf ihg => exact InLam.add ihf ihg
  | mul _ _ ihf ihg => exact InLam.mul ihf ihg
  | neg _ ihf => exact InLam.neg ihf
  | dfn _ _ ihf ihg => exact InLam.dfn ihf ihg
  | rcomp H lo hi hH h hh ih =>
    exact InLam.rcomp H lo hi hH (fun j x => h j (fun i => z i x)) ih

/-- a function analytic at `a` agrees near `a` with a member of `Λ p`. -/
theorem exists_inLam_of_analyticAt {p : ℕ} {g : (Fin p → ℝ) → ℝ} {a : Fin p → ℝ}
    (hg : AnalyticAt ℝ g a) : ∃ f, InLam p f ∧ ∀ᶠ x in 𝓝 a, f x = g x := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hg.eventually_analyticAt
  set lo : Fin p → ℝ := fun i => a i - ε / 2 with hlo
  set hi : Fin p → ℝ := fun i => a i + ε / 2 with hhi
  have hbox : ∀ x ∈ Set.Icc lo hi, dist x a < ε := by
    intro x hx
    have : dist x a ≤ ε / 2 := by
      rw [dist_pi_le_iff (by positivity)]
      intro i
      rw [Real.dist_eq, abs_le]
      have h1 := hx.1 i
      have h2 := hx.2 i
      simp only [lo, hi] at h1 h2
      constructor <;> linarith
    linarith
  refine ⟨rcomp g lo hi (fun j x => x j),
    InLam.rcomp g lo hi (fun w hw => hball (hbox w hw)) _ (fun j => InLam.coord j), ?_⟩
  filter_upwards [Metric.ball_mem_nhds a (half_pos hε)] with x hx
  have hmem : x ∈ Set.Icc lo hi := by
    rw [Metric.mem_ball, dist_pi_lt_iff (half_pos hε)] at hx
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := hx i
      rw [Real.dist_eq, abs_lt] at this
      simp only [lo]
      linarith [this.1]
    · have := hx i
      rw [Real.dist_eq, abs_lt] at this
      simp only [hi]
      linarith [this.2]
  exact if_pos hmem

/-- members of `Λ p` are locally bounded. -/
theorem InLam.locBdd {p : ℕ} {f : (Fin p → ℝ) → ℝ} (hf : InLam p f) (a : Fin p → ℝ) :
    ∃ M, ∀ᶠ x in 𝓝 a, |f x| ≤ M := by
  induction hf generalizing a with
  | coord i =>
    have hc : Continuous fun x : Fin p → ℝ => |x i| := (continuous_apply i).abs
    exact ⟨|a i| + 1, (hc.continuousAt.eventually (gt_mem_nhds (lt_add_one |a i|))).mono
      fun x hx => hx.le⟩
  | const c => exact ⟨|c|, Filter.Eventually.of_forall fun _ => le_rfl⟩
  | add _ _ ih1 ih2 =>
    obtain ⟨M1, h1⟩ := ih1 a
    obtain ⟨M2, h2⟩ := ih2 a
    refine ⟨M1 + M2, (h1.and h2).mono fun x hx => ?_⟩
    simp only [Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add hx.1 hx.2)
  | mul _ _ ih1 ih2 =>
    obtain ⟨M1, h1⟩ := ih1 a
    obtain ⟨M2, h2⟩ := ih2 a
    refine ⟨M1 * M2, (h1.and h2).mono fun x hx => ?_⟩
    simp only [Pi.mul_apply, abs_mul]
    exact mul_le_mul hx.1 hx.2 (abs_nonneg _) ((abs_nonneg _).trans hx.1)
  | neg _ ih =>
    obtain ⟨M, h⟩ := ih a
    exact ⟨M, h.mono fun x hx => by simpa only [Pi.neg_apply, abs_neg] using hx⟩
  | dfn _ _ _ _ => exact ⟨1, Filter.Eventually.of_forall fun x => abs_Dfn_le _ _⟩
  | rcomp H lo hi hH h hh ih =>
    have hcont : ContinuousOn H (Set.Icc lo hi) := fun w hw =>
      (hH w hw).continuousAt.continuousWithinAt
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
    refine ⟨max C 0, Filter.Eventually.of_forall fun x => ?_⟩
    unfold SubanalyticLib.rcomp
    split_ifs with hx
    · exact (by simpa only [Real.norm_eq_abs] using hC _ hx : |H _| ≤ C).trans (le_max_left _ _)
    · simp

/-- `A` is locally a `Λ`-set at every point of `U`. -/
def LocLam (p : ℕ) (A U : Set (Fin p → ℝ)) : Prop :=
  ∀ a ∈ U, ∃ U0 ∈ 𝓝 a, ∃ T, IsSA (Lam p) T ∧ A ∩ U0 = T ∩ U0

theorem LocLam.compl {p : ℕ} {A U : Set (Fin p → ℝ)} (h : LocLam p A U) : LocLam p Aᶜ U := by
  intro a ha
  obtain ⟨U0, hU0, T, hT, hAT⟩ := h a ha
  refine ⟨U0, hU0, Tᶜ, hT.compl, ?_⟩
  ext x
  have := Set.ext_iff.1 hAT x
  simp only [Set.mem_inter_iff] at this
  simp only [Set.mem_inter_iff, Set.mem_compl_iff]
  exact ⟨fun ⟨hn, hu⟩ => ⟨fun ht => hn (this.2 ⟨ht, hu⟩).1, hu⟩,
    fun ⟨hn, hu⟩ => ⟨fun ha => hn (this.1 ⟨ha, hu⟩).1, hu⟩⟩

theorem LocLam.inter {p : ℕ} {A B U : Set (Fin p → ℝ)} (hA : LocLam p A U) (hB : LocLam p B U) :
    LocLam p (A ∩ B) U := by
  intro a ha
  obtain ⟨U0, hU0, T, hT, hAT⟩ := hA a ha
  obtain ⟨U1, hU1, T', hT', hBT⟩ := hB a ha
  refine ⟨U0 ∩ U1, Filter.inter_mem hU0 hU1, T ∩ T', hT.inter hT', ?_⟩
  ext x
  have h1 := Set.ext_iff.1 hAT x
  have h2 := Set.ext_iff.1 hBT x
  simp only [Set.mem_inter_iff] at h1 h2 ⊢
  exact ⟨fun ⟨⟨ha, hb⟩, hu0, hu1⟩ => ⟨⟨(h1.1 ⟨ha, hu0⟩).1, (h2.1 ⟨hb, hu1⟩).1⟩, hu0, hu1⟩,
    fun ⟨⟨ht, ht'⟩, hu0, hu1⟩ => ⟨⟨(h1.2 ⟨ht, hu0⟩).1, (h2.2 ⟨ht', hu1⟩).1⟩, hu0, hu1⟩⟩

theorem LocLam.union {p : ℕ} {A B U : Set (Fin p → ℝ)} (hA : LocLam p A U) (hB : LocLam p B U) :
    LocLam p (A ∪ B) U := by
  have := (hA.compl.inter hB.compl).compl
  rwa [← Set.compl_union, compl_compl] at this

theorem LocLam.mono {p : ℕ} {A U V : Set (Fin p → ℝ)} (h : LocLam p A U) (hVU : V ⊆ U) :
    LocLam p A V := fun a ha => h a (hVU ha)

/-- sets agreeing on an open `U` are locally Λ together. -/
theorem LocLam.congr {p : ℕ} {A B U : Set (Fin p → ℝ)} (hU : IsOpen U) (h : LocLam p A U)
    (hAB : A ∩ U = B ∩ U) : LocLam p B U := by
  intro a ha
  obtain ⟨U0, hU0, T, hT, hAT⟩ := h a ha
  refine ⟨U0 ∩ U, Filter.inter_mem hU0 (hU.mem_nhds ha), T, hT, ?_⟩
  ext x
  have h1 := Set.ext_iff.1 hAT x
  have h2 := Set.ext_iff.1 hAB x
  simp only [Set.mem_inter_iff] at h1 h2 ⊢
  exact ⟨fun ⟨hb, hu0, hu⟩ => ⟨(h1.1 ⟨(h2.2 ⟨hb, hu⟩).1, hu0⟩).1, hu0, hu⟩,
    fun ⟨ht, hu0, hu⟩ => ⟨(h2.1 ⟨(h1.2 ⟨ht, hu0⟩).1, hu⟩).1, hu0, hu⟩⟩

/-- **Base case** (`m = 0`): sign-pattern sets of finitely many analytic functions on an open set
are locally Λ there. -/
theorem locLam_flat {p n : ℕ} {U : Set (Fin p → ℝ)} {g : Fin n → (Fin p → ℝ) → ℝ}
    (hg : ∀ k, ∀ x ∈ U, AnalyticAt ℝ (g k) x) (N : Set (Fin n → SignType)) :
    LocLam p {x | (fun k => SignType.sign (g k x)) ∈ N} U := by
  intro a ha
  choose f hf hfg using fun k => exists_inLam_of_analyticAt (hg k a ha)
  have hev : ∀ᶠ x in 𝓝 a, ∀ k, f k x = g k x := Filter.eventually_all.2 hfg
  refine ⟨{x | ∀ k, f k x = g k x}, hev, {x | (fun k => SignType.sign (f k x)) ∈ N},
    CodeForm.isSA ⟨n, f, hf, N, rfl⟩, ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa only [h2] using h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by simpa only [h2] using h1, h2⟩

end Lam

end SubanalyticLib


/-! SubanalyticLib G4c part 2 (route G): graphs of Λ-functions are subanalytic; Λ-sets
(`IsSA (Lam p)`) and locally-Λ sets are subanalytic.  Needs L0 (imports Definitions). -/

namespace SubanalyticLib

section LamGraph

open Filter Topology NonsmoothLojasiewicz.Continuous

/-- local criterion for subanalyticity. -/
theorem sub_of_local {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {A : Set X} (h : ∀ x₀ : X, ∃ W ∈ 𝓝 x₀, ∃ A' : Set X, IsSubanalytic A' ∧ A ∩ W = A' ∩ W) :
    IsSubanalytic A := by
  rw [sub_iff_locWit]
  intro x₀
  obtain ⟨W, hW, A', hA', hEq⟩ := h x₀
  obtain ⟨W₁, hW₁, hL⟩ := (sub_iff_locWit.1 hA') x₀
  obtain ⟨r, hr, hsub⟩ := ebox_sub x₀ (Filter.inter_mem hW hW₁)
  refine ⟨ebox x₀ r, ebox_nhds x₀ hr,
    (hL.mono (fun y hy => (hsub hy).2) (ebox_semi x₀ r)).congr ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hyr⟩
    have : y ∈ A ∩ W := by rw [hEq]; exact ⟨hy, (hsub hyr).1⟩
    exact ⟨this.1, hyr⟩
  · rintro ⟨hy, hyr⟩
    have : y ∈ A' ∩ W := by rw [← hEq]; exact ⟨hy, (hsub hyr).1⟩
    exact ⟨this.1, hyr⟩

theorem sub_iInter_fin {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] : ∀ {k : ℕ} {S : Fin k → Set X},
    (∀ j, IsSubanalytic (S j)) → IsSubanalytic (⋂ j, S j)
  | 0, S, _ => by simpa using (sub_univ : IsSubanalytic (Set.univ : Set X))
  | k + 1, S, h => by
    have e : (⋂ j, S j) = S 0 ∩ ⋂ j : Fin k, S j.succ := by
      ext x
      simp only [Set.mem_iInter, Set.mem_inter_iff]
      exact Fin.forall_fin_succ
    rw [e]
    exact sub_inter (h 0) (sub_iInter_fin fun j => h j.succ)

theorem anA_apply {n : ℕ} (i : Fin n) (x : Fin n → ℝ) :
    AnalyticAt ℝ (fun x : Fin n → ℝ => x i) x :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).analyticAt x

/-- the graph of `f : ℝ^p → ℝ` is subanalytic. -/
def SubGraph {p : ℕ} (f : (Fin p → ℝ) → ℝ) : Prop :=
  IsSubanalytic {q : (Fin p → ℝ) × ℝ | f q.1 = q.2}

theorem subGraph_of_analytic {p : ℕ} {f : (Fin p → ℝ) → ℝ} (hf : ∀ x, AnalyticAt ℝ f x) :
    SubGraph f :=
  sub_graph_analytic hf

/-- composition: `φ` with subanalytic graph, `f_j` with subanalytic graphs, locally bounded. -/
theorem subGraph_comp {p k : ℕ} {φ : (Fin k → ℝ) → ℝ} (hφ : SubGraph φ)
    {f : Fin k → (Fin p → ℝ) → ℝ} (hf : ∀ j, SubGraph (f j))
    (hb : ∀ j a, ∃ M, ∀ᶠ x in 𝓝 a, |f j x| ≤ M) :
    SubGraph (fun x => φ (fun j => f j x)) := by
  apply sub_of_local
  intro z₀
  choose M hM using fun j => hb j z₀.1
  have hev : ∀ᶠ z in 𝓝 z₀, ∀ j, |f j z.1| ≤ M j := by
    rw [Filter.eventually_all]
    intro j
    exact (continuous_fst.tendsto z₀).eventually (hM j)
  obtain ⟨r, hr, hsub⟩ := ebox_sub z₀ hev
  let E : Set (((Fin p → ℝ) × ℝ) × (Fin k → ℝ)) :=
    (Prod.fst ⁻¹' ebox z₀ r) ∩ ((⋂ j, (fun e : ((Fin p → ℝ) × ℝ) × (Fin k → ℝ) =>
      (e.1.1, e.2 j)) ⁻¹' {q | f j q.1 = q.2}) ∩
      ((fun e : ((Fin p → ℝ) × ℝ) × (Fin k → ℝ) => (e.2, e.1.2)) ⁻¹' {q | φ q.1 = q.2}))
  have hmem : ∀ e, e ∈ E ↔ e.1 ∈ ebox z₀ r ∧ (∀ j, f j e.1.1 = e.2 j) ∧ φ e.2 = e.1.2 := by
    intro e
    simp only [E, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, Set.mem_setOf_eq]
  refine ⟨ebox z₀ r, ebox_nhds z₀ hr, Prod.fst '' E, sub_proj ?_ ?_, ?_⟩
  · refine sub_inter (sub_of_semi (semi_preimage (fun _ => analyticAt_fst) (ebox_semi z₀ r)))
      (sub_inter (sub_iInter_fin fun j => sub_preimage ?_ (hf j)) (sub_preimage ?_ hφ))
    · intro e
      exact (analyticAt_fst.comp analyticAt_fst).prod ((anA_apply j e.2).comp analyticAt_snd)
    · intro e
      exact analyticAt_snd.prod (analyticAt_snd.comp analyticAt_fst)
  · set C : ℝ := ∑ j, |M j|
    have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => abs_nonneg _
    refine ((ebox_bdd z₀ r).prod (Metric.isBounded_closedBall (x := (0 : Fin k → ℝ)) (r := C))).subset ?_
    intro e he
    rw [hmem] at he
    refine ⟨he.1, ?_⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hC]
    intro j
    rw [Real.norm_eq_abs, ← he.2.1 j]
    exact ((hsub he.1) j).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |M j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)))
  · ext z
    constructor
    · rintro ⟨hz, hzW⟩
      refine ⟨⟨(z, fun j => f j z.1), (hmem _).2 ⟨hzW, fun j => rfl, hz⟩, rfl⟩, hzW⟩
    · rintro ⟨⟨e, he, rfl⟩, hW⟩
      rw [hmem] at he
      refine ⟨?_, hW⟩
      show φ (fun j => f j e.1.1) = e.1.2
      have : (fun j => f j e.1.1) = e.2 := funext he.2.1
      rw [this]
      exact he.2.2

theorem subGraph_comp₂ {p : ℕ} {φ : (Fin 2 → ℝ) → ℝ} (hφ : SubGraph φ)
    {f g : (Fin p → ℝ) → ℝ} (hf : SubGraph f) (hg : SubGraph g)
    (bf : ∀ a, ∃ M, ∀ᶠ x in 𝓝 a, |f x| ≤ M) (bg : ∀ a, ∃ M, ∀ᶠ x in 𝓝 a, |g x| ≤ M) :
    SubGraph (fun x => φ ![f x, g x]) := by
  have e : (fun x => φ ![f x, g x]) = fun x => φ (fun j => ![f, g] j x) := by
    funext x
    congr 1
    funext j
    fin_cases j <;> rfl
  rw [e]
  refine subGraph_comp hφ (fun j => ?_) (fun j => ?_)
  · fin_cases j
    · exact hf
    · exact hg
  · fin_cases j
    · exact bf
    · exact bg

theorem subGraph_neg {p : ℕ} {f : (Fin p → ℝ) → ℝ} (hf : SubGraph f) : SubGraph (-f) := by
  have e : {q : (Fin p → ℝ) × ℝ | (-f) q.1 = q.2} =
      (fun q : (Fin p → ℝ) × ℝ => (q.1, -q.2)) ⁻¹' {q | f q.1 = q.2} := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Pi.neg_apply]
    constructor <;> intro h <;> linarith
  unfold SubGraph
  rw [e]
  exact sub_preimage (fun q => analyticAt_fst.prod analyticAt_snd.neg) hf

theorem semi_graph_Dfn :
    IsSemianalytic {q : (Fin 2 → ℝ) × ℝ | Dfn (q.1 0) (q.1 1) = q.2} := by
  have hc : ∀ i : Fin 2, AnalyticOnNhd ℝ (fun q : (Fin 2 → ℝ) × ℝ => q.1 i) Set.univ := by
    intro i q _
    exact (anA_apply i q.1).comp analyticAt_fst
  have h2 : AnalyticOnNhd ℝ (fun q : (Fin 2 → ℝ) × ℝ => q.2) Set.univ := fun q _ => analyticAt_snd
  set C : Set ((Fin 2 → ℝ) × ℝ) := {q | |q.1 0| ≤ |q.1 1| ∧ q.1 1 ≠ 0} with hCdef
  have hC : IsSemianalytic C := by
    have e : C = {q : (Fin 2 → ℝ) × ℝ | (q.1 0) ^ 2 ≤ (q.1 1) ^ 2} ∩
        {q : (Fin 2 → ℝ) × ℝ | q.1 1 = 0}ᶜ := by
      ext q
      simp [C, sq_le_sq]
    rw [e]
    exact semi_inter (semi_le ((hc 0).pow 2) ((hc 1).pow 2))
      (semi_compl (semi_zero (hc 1)))
  have e : {q : (Fin 2 → ℝ) × ℝ | Dfn (q.1 0) (q.1 1) = q.2} =
      (C ∩ {q | q.2 * q.1 1 = q.1 0}) ∪ (Cᶜ ∩ {q | q.2 = 0}) := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    by_cases hq : q ∈ C
    · have hq' := hq
      simp only [C, Set.mem_setOf_eq] at hq'
      rw [Dfn_eq hq'.1 hq'.2, div_eq_iff hq'.2]
      constructor
      · intro h
        exact Or.inl ⟨hq, by linarith⟩
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · linarith
        · exact absurd hq h
    · have hq' : ¬ (|q.1 0| ≤ |q.1 1| ∧ q.1 1 ≠ 0) := hq
      unfold Dfn
      rw [if_neg hq']
      constructor
      · intro h
        exact Or.inr ⟨hq, h.symm⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd h hq
        · exact h.symm
  rw [e]
  exact semi_union (semi_inter hC (semi_eq (h2.mul (hc 1)) (hc 0)))
    (semi_inter (semi_compl hC) (semi_zero h2))

theorem semi_Icc {q : ℕ} (lo hi : Fin q → ℝ) : IsSemianalytic (Set.Icc lo hi) := by
  have e : Set.Icc lo hi = ⋂ j : Fin q, ({w : Fin q → ℝ | lo j ≤ w j} ∩ {w | w j ≤ hi j}) := by
    ext w
    simp only [Set.mem_Icc, Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩ j
      exact ⟨h1 j, h2 j⟩
    · intro h
      exact ⟨fun j => (h j).1, fun j => (h j).2⟩
  rw [e]
  refine semi_iInter fun j => semi_inter (semi_le (fun _ _ => analyticAt_const) ?_)
    (semi_le ?_ (fun _ _ => analyticAt_const))
  · intro w _
    exact anA_apply j w
  · intro w _
    exact anA_apply j w

theorem semi_graph_rcomp {q : ℕ} (H : (Fin q → ℝ) → ℝ) (lo hi : Fin q → ℝ)
    (hH : ∀ w ∈ Set.Icc lo hi, AnalyticAt ℝ H w) :
    IsSemianalytic {qq : (Fin q → ℝ) × ℝ |
      rcomp H lo hi (fun j w => w j) qq.1 = qq.2} := by
  set K' : Set ((Fin q → ℝ) × ℝ) := Prod.fst ⁻¹' Set.Icc lo hi with hK'def
  have hK' : IsSemianalytic K' := semi_preimage (fun _ => analyticAt_fst) (semi_Icc lo hi)
  have h2 : AnalyticOnNhd ℝ (fun q : (Fin q → ℝ) × ℝ => q.2) Set.univ :=
    fun q _ => analyticAt_snd
  set A1 : Set ((Fin q → ℝ) × ℝ) := K' ∩ {qq | H qq.1 - qq.2 = 0} with hA1def
  have hA1 : IsSemianalytic A1 := by
    intro q₀
    by_cases hq : q₀.1 ∈ Set.Icc lo hi
    · obtain ⟨U, hUa, hUo, hqU⟩ := eventually_nhds_iff.1 (hH q₀.1 hq).eventually_analyticAt
      obtain ⟨V₂, hV₂o, hqV₂, hL⟩ := hK' q₀
      refine ⟨(Prod.fst ⁻¹' U) ∩ V₂, (hUo.preimage continuous_fst).inter hV₂o, ⟨hqU, hqV₂⟩, ?_⟩
      have hL' : LocForm ((Prod.fst ⁻¹' U) ∩ V₂) K' := LocForm.mono hL Set.inter_subset_right
      refine LocForm.inter hL' (locForm_zero ?_)
      intro z hz
      exact ((hUa z.1 hz.1).comp analyticAt_fst).sub analyticAt_snd
    · refine ⟨Prod.fst ⁻¹' (Set.Icc lo hi)ᶜ, (isClosed_Icc.isOpen_compl).preimage continuous_fst,
        hq, (locForm_empty _).congr ?_⟩
      ext z
      simp only [Set.mem_empty_iff_false, Set.empty_inter, false_iff, Set.mem_inter_iff,
        Set.mem_preimage, Set.mem_compl_iff, not_and, A1, K']
      intro h1 h3
      exact h3 h1.1
  have e : {qq : (Fin q → ℝ) × ℝ | rcomp H lo hi (fun j w => w j) qq.1 = qq.2} =
      A1 ∪ (K'ᶜ ∩ {qq | qq.2 = 0}) := by
    ext z
    simp only [rcomp, Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
      A1, K', Set.mem_preimage]
    by_cases hz : z.1 ∈ Set.Icc lo hi
    · have hz' : (fun j => z.1 j) ∈ Set.Icc lo hi := hz
      rw [if_pos hz']
      constructor
      · intro h
        exact Or.inl ⟨hz, by rw [← h]; ring⟩
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · linarith
        · exact absurd hz h
    · have hz' : (fun j => z.1 j) ∉ Set.Icc lo hi := hz
      rw [if_neg hz']
      constructor
      · intro h
        exact Or.inr ⟨hz, h.symm⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd h hz
        · exact h.symm
  rw [e]
  exact semi_union hA1 (semi_inter (semi_compl hK') (semi_zero h2))

/-- **every Λ-function has a subanalytic graph.** -/
theorem subGraph_of_inLam {p : ℕ} {f : (Fin p → ℝ) → ℝ} (hf : InLam p f) : SubGraph f := by
  induction hf with
  | coord i => exact subGraph_of_analytic (fun x => anA_apply i x)
  | const c => exact subGraph_of_analytic (fun x => analyticAt_const)
  | @add f g hf hg ihf ihg =>
    have e : f + g = fun x => (fun a : Fin 2 → ℝ => a 0 + a 1) ![f x, g x] := by
      funext x
      simp
    rw [e]
    exact subGraph_comp₂ (φ := fun a : Fin 2 → ℝ => a 0 + a 1)
      (subGraph_of_analytic (fun a => (anA_apply 0 a).add (anA_apply 1 a))) ihf ihg hf.locBdd hg.locBdd
  | @mul f g hf hg ihf ihg =>
    have e : f * g = fun x => (fun a : Fin 2 → ℝ => a 0 * a 1) ![f x, g x] := by
      funext x
      simp
    rw [e]
    exact subGraph_comp₂ (φ := fun a : Fin 2 → ℝ => a 0 * a 1)
      (subGraph_of_analytic (fun a => (anA_apply 0 a).mul (anA_apply 1 a))) ihf ihg hf.locBdd hg.locBdd
  | neg _ ihf => exact subGraph_neg ihf
  | @dfn f g hf hg ihf ihg =>
    have e : (fun x => Dfn (f x) (g x)) =
        fun x => (fun a : Fin 2 → ℝ => Dfn (a 0) (a 1)) ![f x, g x] := by
      funext x
      simp
    rw [e]
    exact subGraph_comp₂ (φ := fun a : Fin 2 → ℝ => Dfn (a 0) (a 1)) (sub_of_semi semi_graph_Dfn) ihf ihg hf.locBdd hg.locBdd
  | rcomp H lo hi hH h hh ih =>
    have e : SubanalyticLib.rcomp H lo hi h =
        fun x => SubanalyticLib.rcomp H lo hi (fun j w => w j) (fun j => h j x) := rfl
    rw [e]
    exact subGraph_comp (sub_of_semi (semi_graph_rcomp H lo hi hH)) ih
      (fun j => (hh j).locBdd)

/-- preimage of a semianalytic subset of `ℝ` under a locally bounded function with
subanalytic graph. -/
theorem sub_preimage_fn {p : ℕ} {f : (Fin p → ℝ) → ℝ} (hf : SubGraph f)
    (hb : ∀ a, ∃ M, ∀ᶠ x in 𝓝 a, |f x| ≤ M) {S : Set ℝ} (hS : IsSemianalytic S) :
    IsSubanalytic (f ⁻¹' S) := by
  apply sub_of_local
  intro x₀
  obtain ⟨M, hM⟩ := hb x₀
  obtain ⟨r, hr, hsub⟩ := ebox_sub x₀ hM
  let E : Set ((Fin p → ℝ) × ℝ) :=
    (Prod.fst ⁻¹' ebox x₀ r) ∩ ({q | f q.1 = q.2} ∩ (Prod.snd ⁻¹' S))
  refine ⟨ebox x₀ r, ebox_nhds x₀ hr, Prod.fst '' E, sub_proj ?_ ?_, ?_⟩
  · exact sub_inter (sub_of_semi (semi_preimage (fun _ => analyticAt_fst) (ebox_semi x₀ r)))
      (sub_inter hf (sub_of_semi (semi_preimage (fun _ => analyticAt_snd) hS)))
  · refine ((ebox_bdd x₀ r).prod (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := M))).subset ?_
    rintro q ⟨h1, h2, -⟩
    refine ⟨h1, ?_⟩
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs, ← h2]
    exact hsub h1
  · ext x
    constructor
    · rintro ⟨hx, hxW⟩
      exact ⟨⟨(x, f x), ⟨hxW, rfl, hx⟩, rfl⟩, hxW⟩
    · rintro ⟨⟨q, ⟨h1, h2, h3⟩, rfl⟩, hW⟩
      refine ⟨?_, hW⟩
      show f q.1 ∈ S
      rw [show f q.1 = q.2 from h2]
      exact h3

/-- **Λ-sets are subanalytic** (together with their complements). -/
theorem sub_of_isSA_Lam {p : ℕ} {T : Set (Fin p → ℝ)} (hT : IsSA (Lam p) T) :
    IsSubanalytic T ∧ IsSubanalytic Tᶜ := by
  have hid : AnalyticOnNhd ℝ (fun t : ℝ => t) Set.univ := fun _ _ => analyticAt_id
  induction hT with
  | @pos f hf =>
    have hf' : InLam p f := hf
    have hS : IsSemianalytic {t : ℝ | 0 < t} := semi_pos hid
    exact ⟨sub_preimage_fn (subGraph_of_inLam hf') hf'.locBdd hS,
      sub_preimage_fn (subGraph_of_inLam hf') hf'.locBdd (semi_compl hS)⟩
  | @zero f hf =>
    have hf' : InLam p f := hf
    have hS : IsSemianalytic {t : ℝ | t = 0} := semi_zero hid
    exact ⟨sub_preimage_fn (subGraph_of_inLam hf') hf'.locBdd hS,
      sub_preimage_fn (subGraph_of_inLam hf') hf'.locBdd (semi_compl hS)⟩
  | compl _ ih => exact ⟨ih.2, by rw [compl_compl]; exact ih.1⟩
  | inter _ _ ih1 ih2 =>
    exact ⟨sub_inter ih1.1 ih2.1, by rw [Set.compl_inter]; exact sub_union ih1.2 ih2.2⟩

/-- a set that is locally Λ everywhere is subanalytic. -/
theorem sub_of_locLam {p : ℕ} {A : Set (Fin p → ℝ)} (h : LocLam p A Set.univ) :
    IsSubanalytic A := by
  apply sub_of_local
  intro a
  obtain ⟨U0, hU0, T, hT, hEq⟩ := h a (Set.mem_univ a)
  exact ⟨U0, hU0, T, (sub_of_isSA_Lam hT).1, hEq⟩

end LamGraph

end SubanalyticLib


/-! SubanalyticLib G5a (route G): finite unions of locally-Λ sets, projections over boxes,
compactness gluing over a box (`glue_boxes`), the statement `StarM m` of (★_m) and its base case. -/

namespace SubanalyticLib

section Glue

open Filter Topology

theorem locLam_empty {p : ℕ} (U : Set (Fin p → ℝ)) : LocLam p ∅ U :=
  fun _ _ => ⟨Set.univ, Filter.univ_mem, ∅, IsSA.empty, by simp⟩

theorem LocLam.biUnion {p : ℕ} {ι : Type*} (s : Finset ι) {A : ι → Set (Fin p → ℝ)}
    {U : Set (Fin p → ℝ)} (h : ∀ i ∈ s, LocLam p (A i) U) : LocLam p (⋃ i ∈ s, A i) U := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using locLam_empty (p := p) U
  · intro i s _ ih h
    rw [Finset.set_biUnion_insert]
    exact LocLam.union (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- projection over `K` of `{(x, y) | Φ x y}`. -/
def projBox {p m : ℕ} (Φ : (Fin p → ℝ) → (Fin m → ℝ) → Prop) (K : Set (Fin m → ℝ)) :
    Set (Fin p → ℝ) :=
  {x | ∃ y ∈ K, Φ x y}

/-- the box `K ∩ [y₀ - δ, y₀ + δ]`. -/
theorem icc_sub_ball {m : ℕ} (lo hi y0 : Fin m → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Set.Icc (fun j => max (lo j) (y0 j - δ)) (fun j => min (hi j) (y0 j + δ)) ⊆
      Set.Icc lo hi ∩ Metric.closedBall y0 δ := by
  intro y hy
  have h1 : ∀ j, max (lo j) (y0 j - δ) ≤ y j := hy.1
  have h2 : ∀ j, y j ≤ min (hi j) (y0 j + δ) := hy.2
  refine ⟨⟨fun j => (le_max_left _ _).trans (h1 j), fun j => (h2 j).trans (min_le_left _ _)⟩, ?_⟩
  rw [Metric.mem_closedBall, dist_pi_le_iff hδ.le]
  intro j
  rw [Real.dist_eq, abs_le]
  have a1 := (le_max_right _ _).trans (h1 j)
  have a2 := (h2 j).trans (min_le_right _ _)
  constructor <;> linarith

theorem mem_icc_of_ball {m : ℕ} {lo hi y0 y : Fin m → ℝ} {δ : ℝ} (hy : y ∈ Set.Icc lo hi)
    (hb : y ∈ Metric.ball y0 δ) :
    y ∈ Set.Icc (fun j => max (lo j) (y0 j - δ)) (fun j => min (hi j) (y0 j + δ)) := by
  have hδ : 0 < δ := lt_of_le_of_lt dist_nonneg hb
  rw [Metric.mem_ball, dist_pi_lt_iff hδ] at hb
  refine ⟨fun j => max_le (hy.1 j) ?_, fun j => le_min (hy.2 j) ?_⟩
  · have := hb j
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  · have := hb j
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]

/-- **compactness gluing over a box**: if near every point of the box, projections over all small
sub-boxes are locally Λ at `a`, so is the projection over the whole box. -/
theorem glue_boxes {p m : ℕ} (Φ : (Fin p → ℝ) → (Fin m → ℝ) → Prop) (a : Fin p → ℝ)
    (lo hi : Fin m → ℝ)
    (h : ∀ y0 ∈ Set.Icc lo hi, ∃ δ > 0, ∀ lo' hi' : Fin m → ℝ,
      Set.Icc lo' hi' ⊆ Set.Icc lo hi ∩ Metric.closedBall y0 δ →
        LocLam p (projBox Φ (Set.Icc lo' hi')) {a}) :
    LocLam p (projBox Φ (Set.Icc lo hi)) {a} := by
  classical
  choose! δ hδ hloc using h
  obtain ⟨t, ht, hcov⟩ := (isCompact_Icc (a := lo) (b := hi)).elim_nhds_subcover
    (fun y0 => Metric.ball y0 (δ y0)) (fun y0 hy0 => Metric.ball_mem_nhds y0 (hδ y0 hy0))
  have e : projBox Φ (Set.Icc lo hi) = ⋃ y0 ∈ t, projBox Φ
      (Set.Icc (fun j => max (lo j) (y0 j - δ y0)) (fun j => min (hi j) (y0 j + δ y0))) := by
    ext x
    simp only [projBox, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨y, hy, hΦ⟩
      have := hcov hy
      simp only [Set.mem_iUnion] at this
      obtain ⟨y0, hy0t, hyb⟩ := this
      exact ⟨y0, hy0t, y, mem_icc_of_ball hy hyb, hΦ⟩
    · rintro ⟨y0, hy0t, y, hy, hΦ⟩
      exact ⟨y, (icc_sub_ball lo hi y0 (hδ y0 (ht y0 hy0t)) hy).1, hΦ⟩
  rw [e]
  exact LocLam.biUnion t fun y0 hy0t =>
    hloc y0 (ht y0 hy0t) _ _ (icc_sub_ball lo hi y0 (hδ y0 (ht y0 hy0t)))

/-- the sign-code predicate of a family `g` at `(x, y)`. -/
def codeIn {p m r : ℕ} (g : Fin r → (Fin p → ℝ) × (Fin m → ℝ) → ℝ)
    (N : Set (Fin r → SignType)) (x : Fin p → ℝ) (y : Fin m → ℝ) : Prop :=
  (fun k => SignType.sign (g k (x, y))) ∈ N

/-- **(★_m)**: projections over a closed box of sign-pattern sets of finitely many functions
analytic near `{a} × box` are locally Λ at `a`. -/
def StarM (m : ℕ) : Prop :=
  ∀ (p r : ℕ) (g : Fin r → (Fin p → ℝ) × (Fin m → ℝ) → ℝ) (a : Fin p → ℝ)
    (lo hi : Fin m → ℝ) (N : Set (Fin r → SignType)),
    (∀ k, ∀ y ∈ Set.Icc lo hi, AnalyticAt ℝ (g k) (a, y)) →
    LocLam p (projBox (codeIn g N) (Set.Icc lo hi)) {a}

/-- base case `m = 0`. -/
theorem star_zero : StarM 0 := by
  intro p r g a lo hi N hg
  have hmem : lo ∈ Set.Icc lo hi := ⟨le_rfl, by rw [Subsingleton.elim lo hi]⟩
  have e : projBox (codeIn g N) (Set.Icc lo hi) =
      {x | (fun k => SignType.sign ((fun x => g k (x, lo)) x)) ∈ N} := by
    ext x
    simp only [projBox, codeIn, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, -, hy⟩
      rwa [Subsingleton.elim y lo] at hy
    · intro hx
      exact ⟨lo, hmem, hx⟩
  rw [e]
  refine locLam_flat (U := {a}) (fun k x hx => ?_) N
  rw [Set.mem_singleton_iff] at hx
  rw [hx]
  have h1 : AnalyticAt ℝ (fun x : Fin p → ℝ => (x, lo)) a := analyticAt_id.prod analyticAt_const
  have h2 : AnalyticAt ℝ (g k ∘ fun x : Fin p → ℝ => (x, lo)) a :=
    AnalyticAt.comp (g := g k) (f := fun x : Fin p → ℝ => (x, lo)) (hg k lo hmem) h1
  exact h2

end Glue

end SubanalyticLib


/-! SubanalyticLib G5b (route G): local polynomial form with a shear acting on the last `m+1`
coordinates only (the eliminated `y`-variables), for germs that are nondegenerate in `y`.
Needs L6F (local_form_one, coordSwap, nonflat_prod, exists_regular_coord, An, pe). -/

namespace SubanalyticLib

section FormY

open Filter Topology Polynomial

/-- `y` placed in the last `m` coordinates, the first `p` being zero. -/
def yemb (p : ℕ) {m : ℕ} (y : Fin m → ℝ) : Fin (p + m) → ℝ := Fin.append (0 : Fin p → ℝ) y

theorem yemb_zero (p m : ℕ) : yemb p (0 : Fin m → ℝ) = 0 := by
  funext i
  induction i using Fin.addCases with
  | left i => simp [yemb, Fin.append_left]
  | right j => simp [yemb, Fin.append_right]

theorem analyticAt_yemb (p : ℕ) {m : ℕ} (y : Fin m → ℝ) :
    AnalyticAt ℝ (yemb p : (Fin m → ℝ) → Fin (p + m) → ℝ) y := by
  rw [analyticAt_pi_iff]
  intro i
  induction i using Fin.addCases with
  | left i =>
    simp only [yemb, Fin.append_left, Pi.zero_apply]
    exact analyticAt_const
  | right j =>
    simp only [yemb, Fin.append_right]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j).analyticAt y

/-- the linear map acting by `L` on the last `m` coordinates. -/
noncomputable def liftY (p : ℕ) {m : ℕ} (L : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)) :
    (Fin (p + m) → ℝ) ≃L[ℝ] (Fin (p + m) → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun x => Fin.append (fun i => x (Fin.castAdd m i)) (L (fun j => x (Fin.natAdd p j)))
    invFun := fun x =>
      Fin.append (fun i => x (Fin.castAdd m i)) (L.symm (fun j => x (Fin.natAdd p j)))
    map_add' := by
      intro x y
      funext i
      induction i using Fin.addCases with
      | left i => simp only [Fin.append_left, Pi.add_apply]
      | right j =>
        simp only [Fin.append_right, Pi.add_apply]
        have e : (fun j => x (Fin.natAdd p j) + y (Fin.natAdd p j)) =
            (fun j => x (Fin.natAdd p j)) + (fun j => y (Fin.natAdd p j)) := rfl
        rw [e, map_add]
        rfl
    map_smul' := by
      intro c x
      funext i
      induction i using Fin.addCases with
      | left i => simp only [Fin.append_left, Pi.smul_apply, RingHom.id_apply]
      | right j =>
        simp only [Fin.append_right, Pi.smul_apply, RingHom.id_apply]
        have e : (fun j => c • x (Fin.natAdd p j)) = c • (fun j => x (Fin.natAdd p j)) := rfl
        rw [e, map_smul]
        rfl
    left_inv := by
      intro x
      funext i
      induction i using Fin.addCases with
      | left i => simp only [Fin.append_left]
      | right j =>
        simp only [Fin.append_right]
        have e : (fun j => L (fun j => x (Fin.natAdd p j)) j) = L (fun j => x (Fin.natAdd p j)) :=
          rfl
        rw [e, ContinuousLinearEquiv.symm_apply_apply]
    right_inv := by
      intro x
      funext i
      induction i using Fin.addCases with
      | left i => simp only [Fin.append_left]
      | right j =>
        simp only [Fin.append_right]
        have e : (fun j => L.symm (fun j => x (Fin.natAdd p j)) j) =
            L.symm (fun j => x (Fin.natAdd p j)) := rfl
        rw [e, ContinuousLinearEquiv.apply_symm_apply] }

theorem liftY_apply (p : ℕ) {m : ℕ} (L : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ)) (x : Fin (p + m) → ℝ) :
    liftY p L x =
      Fin.append (fun i => x (Fin.castAdd m i)) (L (fun j => x (Fin.natAdd p j))) := rfl

theorem liftY_single_last (p m : ℕ) (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ)) (t : ℝ) :
    liftY p L (Pi.single (Fin.last (p + m)) t) = yemb p (L (Pi.single (Fin.last m) t)) := by
  have hs : (fun j : Fin (m + 1) =>
      (Pi.single (Fin.last (p + m)) t : Fin (p + m + 1) → ℝ) (Fin.natAdd p j)) =
      Pi.single (Fin.last m) t := by
    funext j
    by_cases hj : (j : ℕ) = m
    · have h1 : Fin.natAdd p j = Fin.last (p + m) := Fin.ext (by simp [hj])
      have h2 : j = Fin.last m := Fin.ext (by simp [hj])
      rw [h1, h2, Pi.single_eq_same, Pi.single_eq_same]
    · have h1 : Fin.natAdd p j ≠ Fin.last (p + m) := by
        intro h
        have := congrArg Fin.val h
        simp at this
        exact hj this
      have h2 : j ≠ Fin.last m := by
        intro h
        exact hj (by rw [h]; simp)
      rw [Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2]
  funext i
  induction i using Fin.addCases with
  | left i =>
    rw [liftY_apply, Fin.append_left]
    simp only [yemb, Fin.append_left, Pi.zero_apply]
    have h1 : (Fin.castAdd (m + 1) i : Fin (p + m + 1)) ≠ Fin.last (p + m) := by
      intro h
      have := congrArg Fin.val h
      simp at this
      have := i.isLt
      omega
    rw [Pi.single_apply, if_neg h1]
  | right j =>
    rw [liftY_apply, Fin.append_right, hs]
    simp only [yemb, Fin.append_right]

/-- **G5b: local polynomial form, shearing only the `y`-coordinates.**  For germs at `0` in
`ℝ^(p+m+1)` that are not flat along the `y`-subspace, a linear change of the last `m+1`
coordinates puts all of them (up to a sign) in monic distinguished polynomial form in the last
coordinate. -/
theorem local_form_y {p m K : ℕ} (h : Fin K → (Fin (p + m + 1) → ℝ) → ℝ)
    (hh : ∀ k, AnalyticAt ℝ (h k) 0)
    (hnd : ∀ k, ¬ ∀ᶠ y in 𝓝 (0 : Fin (m + 1) → ℝ), h k (yemb p y) = 0) :
    ∃ Ly : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ), ∃ ρ > 0, ∃ P : Fin K → (An (p + m))[X],
      (∀ k, (P k).Monic ∧
        ∀ i < (P k).natDegree, (((P k).coeff i : An (p + m)) : (Fin (p + m) → ℝ) → ℝ) 0 = 0) ∧
      ∃ ε : Fin K → SignType, ∀ k, ∀ x : Fin (p + m + 1) → ℝ, ‖x‖ < ρ →
        SignType.sign (h k (liftY p Ly x)) =
          ε k * SignType.sign ((pe (P k) (Fin.init x)).eval (x (Fin.last (p + m)))) := by
  classical
  have hyA : ∀ k, AnalyticAt ℝ (fun y : Fin (m + 1) → ℝ => h k (yemb p y)) 0 := fun k =>
    (hh k).comp_of_eq (analyticAt_yemb p 0) (yemb_zero p (m + 1))
  obtain ⟨hHa, hHn⟩ := nonflat_prod Finset.univ
    (f := fun k (y : Fin (m + 1) → ℝ) => h k (yemb p y)) (x₀ := (0 : Fin (m + 1) → ℝ)) (fun k _ => hyA k) (fun k _ => hnd k)
  obtain ⟨k0, L0, hL0⟩ := exists_regular_coord hHa hHn
  let Ly := (coordSwap k0 (Fin.last m)).trans L0
  have hLs : ∀ t, Ly (Pi.single (Fin.last m) t) = L0 (Pi.single k0 t) := fun t => by
    show L0 (coordSwap k0 (Fin.last m) _) = _
    rw [coordSwap_single]
  have hper : ∀ k, ∃ ρ > 0, ∃ P : (An (p + m))[X],
      (P.Monic ∧ ∀ i < P.natDegree, ((P.coeff i : An (p + m)) : (Fin (p + m) → ℝ) → ℝ) 0 = 0) ∧
      ∃ ε : SignType, ∀ x : Fin (p + m + 1) → ℝ, ‖x‖ < ρ →
        SignType.sign (h k (liftY p Ly x)) =
          ε * SignType.sign ((pe P (Fin.init x)).eval (x (Fin.last (p + m)))) := by
    intro k
    have hgA : AnalyticAt ℝ (fun x => h k (liftY p Ly x)) 0 :=
      (hh k).comp_of_eq (((liftY p Ly : (Fin (p + m + 1) → ℝ) ≃L[ℝ] (Fin (p + m + 1) → ℝ)) :
        (Fin (p + m + 1) → ℝ) →L[ℝ] (Fin (p + m + 1) → ℝ)).analyticAt 0) (by simp)
    have hax : ¬ ∀ᶠ t in 𝓝 (0 : ℝ), h k (liftY p Ly (Pi.single (Fin.last (p + m)) t)) = 0 := by
      intro hev
      apply hL0
      filter_upwards [hev] with t ht
      rw [liftY_single_last, hLs] at ht
      exact Finset.prod_eq_zero (Finset.mem_univ k) ht
    obtain ⟨ρ, hρ, P, hPm, hPc, ε, hε⟩ := local_form_one hgA hax
    exact ⟨ρ, hρ, P, ⟨hPm, hPc⟩, ε, hε⟩
  choose ρ hρ P hP ε hε using hper
  obtain ⟨r, hr, hrle⟩ := exists_pos_le_all ρ hρ
  exact ⟨Ly, r, hr, P, hP, ε, fun k x hx => hε k x (lt_of_lt_of_le hx (hrle k))⟩

end FormY

end SubanalyticLib


/-! SubanalyticLib G5c (route G): nondegenerate elimination at one point (`ne_loc`).  Assuming
(★_m), the projection over every small box near `y0` of a sign-pattern set of functions that are
nondegenerate in `y` at `(a, y0)` is locally Λ on a ball around `a`.  Needs L9d (local_form_y),
L9c (StarM, projBox, codeIn), ts_any, IsSA.codeForm. -/

namespace SubanalyticLib

section NEloc

open Filter Topology Polynomial

set_option autoImplicit false

/-- functions analytic at every point of the ball `ball 0 r`. -/
def AnB (n : ℕ) (r : ℝ) : Subring ((Fin n → ℝ) → ℝ) where
  carrier := {f | ∀ w ∈ Metric.ball (0 : Fin n → ℝ) r, AnalyticAt ℝ f w}
  mul_mem' {a b} ha hb := by
    intro w hw
    show AnalyticAt ℝ (fun x => a x * b x) w
    exact (ha w hw).mul (hb w hw)
  one_mem' := by
    intro w _
    show AnalyticAt ℝ (fun _ => (1 : ℝ)) w
    exact analyticAt_const
  add_mem' {a b} ha hb := by
    intro w hw
    show AnalyticAt ℝ (fun x => a x + b x) w
    exact (ha w hw).add (hb w hw)
  zero_mem' := by
    intro w _
    show AnalyticAt ℝ (fun _ => (0 : ℝ)) w
    exact analyticAt_const
  neg_mem' {a} ha := by
    intro w hw
    show AnalyticAt ℝ (fun x => -a x) w
    exact (ha w hw).neg

/-- a polynomial over `An n` whose coefficients lie in `R` has a copy over `R` with the same
specialisations. -/
theorem exists_transfer {n : ℕ} (R : Subring ((Fin n → ℝ) → ℝ)) (P : (An n)[X])
    (h : ∀ i, ((P.coeff i : An n) : (Fin n → ℝ) → ℝ) ∈ R) :
    ∃ Q : R[X], ∀ w t, (pe Q w).eval t = (pe P w).eval t := by
  refine ⟨∑ i ∈ Finset.range (P.natDegree + 1), C (⟨_, h i⟩ : R) * X ^ i, fun w t => ?_⟩
  rw [eval_eq_sum_range' (n := P.natDegree + 1) (p := pe P w)]
  · simp only [pe_coeff]
    simp only [pe, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
      Polynomial.map_X, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, evR_apply]
  · have : (pe P w).natDegree ≤ P.natDegree := natDegree_map_le
    omega

theorem init_append_fin {p m : ℕ} (u : Fin p → ℝ) (v : Fin (m + 1) → ℝ) :
    Fin.init (n := p + m) (Fin.append (m := p) (n := m + 1) u v) = Fin.append u (Fin.init v) := by
  funext i
  induction i using Fin.addCases with
  | left i =>
    have e : (Fin.castSucc (Fin.castAdd m i) : Fin (p + m + 1)) = Fin.castAdd (m + 1) i :=
      Fin.ext rfl
    simp only [Fin.init, Fin.append_left]
    rw [e, Fin.append_left]
  | right j =>
    have e : (Fin.castSucc (Fin.natAdd p j) : Fin (p + m + 1)) = Fin.natAdd p (Fin.castSucc j) :=
      Fin.ext rfl
    simp only [Fin.init, Fin.append_right]
    rw [e, Fin.append_right]

theorem append_last_fin {p m : ℕ} (u : Fin p → ℝ) (v : Fin (m + 1) → ℝ) :
    (Fin.append (m := p) (n := m + 1) u v : Fin (p + m + 1) → ℝ) (Fin.last (p + m)) =
      v (Fin.last m) := by
  have e : (Fin.last (p + m) : Fin (p + m + 1)) = Fin.natAdd p (Fin.last m) := Fin.ext rfl
  rw [e, Fin.append_right]

theorem norm_append_lt {p q : ℕ} {u : Fin p → ℝ} {v : Fin q → ℝ} {s : ℝ} (hu : ‖u‖ < s)
    (hv : ‖v‖ < s) : ‖(Fin.append u v : Fin (p + q) → ℝ)‖ < s := by
  have hs : 0 < s := lt_of_le_of_lt (norm_nonneg _) hu
  rw [pi_norm_lt_iff hs]
  intro i
  induction i using Fin.addCases with
  | left i =>
    rw [Fin.append_left]
    exact lt_of_le_of_lt (norm_le_pi_norm u i) hu
  | right j =>
    rw [Fin.append_right]
    exact lt_of_le_of_lt (norm_le_pi_norm v j) hv

/-- the first `p` coordinates. -/
noncomputable def clmL (p q : ℕ) : (Fin (p + q) → ℝ) →L[ℝ] (Fin p → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castAdd q i)

/-- the last `q` coordinates. -/
noncomputable def clmR (p q : ℕ) : (Fin (p + q) → ℝ) →L[ℝ] (Fin q → ℝ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (Fin.natAdd p j)

theorem clmR_apply {p q : ℕ} (x : Fin (p + q) → ℝ) :
    clmR p q x = fun j => x (Fin.natAdd p j) := rfl

theorem clmL_append {p q : ℕ} (u : Fin p → ℝ) (v : Fin q → ℝ) :
    clmL p q (Fin.append u v) = u := by
  funext i
  exact Fin.append_left u v i

theorem clmR_append {p q : ℕ} (u : Fin p → ℝ) (v : Fin q → ℝ) :
    clmR p q (Fin.append u v) = v := by
  funext j
  exact Fin.append_right u v j

theorem snoc_split {m : ℕ} (u : Fin m → ℝ) (t : ℝ) :
    (Fin.snoc u t : Fin (m + 1) → ℝ) = Fin.snoc u 0 + t • Pi.single (Fin.last m) 1 := by
  funext j
  induction j using Fin.lastCases with
  | last => simp
  | cast i =>
    simp [Fin.snoc_castSucc, Pi.single_eq_of_ne (Fin.castSucc_ne_last i)]

theorem analyticAt_snoc_clmR (p m : ℕ) (w : Fin (p + m) → ℝ) :
    AnalyticAt ℝ (fun w : Fin (p + m) → ℝ => (Fin.snoc (clmR p m w) 0 : Fin (m + 1) → ℝ)) w := by
  rw [analyticAt_pi_iff]
  intro j
  induction j using Fin.lastCases with
  | last =>
    simp only [Fin.snoc_last]
    exact analyticAt_const
  | cast i =>
    simp only [Fin.snoc_castSucc, clmR_apply]
    exact anA_apply (Fin.natAdd p i) w

theorem analyticAt_append_sub {p m : ℕ} (a : Fin p → ℝ) (q0 : (Fin p → ℝ) × (Fin m → ℝ)) :
    AnalyticAt ℝ (fun q : (Fin p → ℝ) × (Fin m → ℝ) => (Fin.append (q.1 - a) q.2 : Fin (p + m) → ℝ))
      q0 := by
  rw [analyticAt_pi_iff]
  intro i
  induction i using Fin.addCases with
  | left i =>
    simp only [Fin.append_left, Pi.sub_apply]
    have h1 : AnalyticAt ℝ (fun q : (Fin p → ℝ) × (Fin m → ℝ) => q.1 i) q0 :=
      (anA_apply i q0.1).comp analyticAt_fst
    exact h1.sub analyticAt_const
  | right j =>
    simp only [Fin.append_right]
    exact (anA_apply j q0.2).comp analyticAt_snd

theorem sign_ne_neg_one_iff' (x : ℝ) : SignType.sign x ≠ -1 ↔ 0 ≤ x := by
  rw [Ne, sign_eq_neg_one_iff, not_lt]

/-- **G5c: nondegenerate elimination at one point** (assuming (★_m)). -/
theorem ne_loc {m : ℕ} (hS : StarM m) {p K : ℕ}
    (G : Fin K → (Fin p → ℝ) × (Fin (m + 1) → ℝ) → ℝ) (a : Fin p → ℝ) (y0 : Fin (m + 1) → ℝ)
    (hG : ∀ k, AnalyticAt ℝ (G k) (a, y0))
    (hnd : ∀ k, ¬ ∀ᶠ y in 𝓝 y0, G k (a, y) = 0) :
    ∃ δ > 0, ∃ r > 0, ∀ (N : Set (Fin K → SignType)) (lo' hi' : Fin (m + 1) → ℝ),
      Set.Icc lo' hi' ⊆ Metric.closedBall y0 δ →
        LocLam p (projBox (codeIn G N) (Set.Icc lo' hi')) (Metric.ball a r) := by
  classical
  -- Step A: recentre at `0 ∈ ℝ^(p+m+1)`
  obtain ⟨h, hh_def⟩ : ∃ h : Fin K → (Fin (p + m + 1) → ℝ) → ℝ, ∀ k X,
      h k X = G k (a + clmL p (m + 1) X, y0 + clmR p (m + 1) X) := ⟨_, fun _ _ => rfl⟩
  have hhA : ∀ k, AnalyticAt ℝ (h k) 0 := by
    intro k
    have hφ : AnalyticAt ℝ (fun X : Fin (p + m + 1) → ℝ =>
        (a + clmL p (m + 1) X, y0 + clmR p (m + 1) X)) 0 :=
      (analyticAt_const.add ((clmL p (m + 1)).analyticAt 0)).prod
        (analyticAt_const.add ((clmR p (m + 1)).analyticAt 0))
    have e : h k = G k ∘ (fun X : Fin (p + m + 1) → ℝ =>
        (a + clmL p (m + 1) X, y0 + clmR p (m + 1) X)) := by
      funext X
      rw [hh_def]
      rfl
    rw [e]
    exact (hG k).comp_of_eq hφ (by simp)
  have hhnd : ∀ k, ¬ ∀ᶠ y in 𝓝 (0 : Fin (m + 1) → ℝ), h k (yemb p y) = 0 := by
    intro k hk
    apply hnd k
    have e : ∀ y : Fin (m + 1) → ℝ, h k (yemb p y) = G k (a, y0 + y) := by
      intro y
      rw [hh_def]
      simp only [yemb, clmL_append, clmR_append, add_zero]
    have ht : Tendsto (fun y : Fin (m + 1) → ℝ => y - y0) (𝓝 y0) (𝓝 0) :=
      tendsto_sub_nhds_zero_iff.2 tendsto_id
    filter_upwards [ht.eventually hk] with y hy
    rw [e] at hy
    simpa using hy
  -- Step B: local polynomial form in the sheared `y`
  obtain ⟨Ly, ρ, hρ, P, -, ε, hsign⟩ := local_form_y h hhA hhnd
  -- Step C: a common ball on which all coefficients are analytic
  have hev : ∀ᶠ w in 𝓝 (0 : Fin (p + m) → ℝ), ∀ k i,
      AnalyticAt ℝ (((P k).coeff i : An (p + m)) : (Fin (p + m) → ℝ) → ℝ) w := by
    rw [Filter.eventually_all]
    intro k
    have h1 : ∀ᶠ w in 𝓝 (0 : Fin (p + m) → ℝ), ∀ i ∈ Finset.range ((P k).natDegree + 1),
        AnalyticAt ℝ (((P k).coeff i : An (p + m)) : (Fin (p + m) → ℝ) → ℝ) w := by
      rw [Filter.eventually_all_finset]
      intro i _
      exact (mem_An.1 ((P k).coeff i).2).eventually_analyticAt
    filter_upwards [h1] with w hw i
    by_cases hi : i < (P k).natDegree + 1
    · exact hw i (Finset.mem_range.2 hi)
    · have h0 : (P k).coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [h0]
      exact analyticAt_const
  obtain ⟨r0, hr0, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  set r₁ := min r0 (ρ / 2) with hr₁
  have hr₁pos : 0 < r₁ := lt_min hr0 (by linarith)
  have hr₁ρ : r₁ / 4 < ρ := by
    have := min_le_right r0 (ρ / 2)
    linarith
  -- Step D: transfer to the ring of functions analytic on `ball 0 r₁`
  choose Q hQ using fun k => exists_transfer (AnB (p + m) r₁) (P k) (fun i w hw =>
    hball w (Metric.ball_subset_ball (min_le_left r0 (ρ / 2)) hw) k i)
  -- Step E: the radius `δ`
  set M := ‖(Ly.symm : (Fin (m + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ))‖ with hM
  have hM0 : 0 ≤ M := norm_nonneg _
  have hLs : ∀ v : Fin (m + 1) → ℝ, ‖v‖ ≤ M * ‖Ly v‖ := by
    intro v
    have := (Ly.symm : (Fin (m + 1) → ℝ) →L[ℝ] (Fin (m + 1) → ℝ)).le_opNorm (Ly v)
    simpa using this
  set δ := r₁ / (4 * (M + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have hMδ : M * δ < r₁ / 4 := by
    have e : (M + 1) * δ = r₁ / 4 := by
      rw [hδ]
      field_simp
    nlinarith
  have hsmall : ∀ v : Fin (m + 1) → ℝ, ‖Ly v‖ ≤ δ → ‖v‖ < r₁ / 4 := by
    intro v hv
    calc ‖v‖ ≤ M * ‖Ly v‖ := hLs v
      _ ≤ M * δ := mul_le_mul_of_nonneg_left hv hM0
      _ < r₁ / 4 := hMδ
  -- KEY: the sign identity
  have KEY : ∀ x : Fin p → ℝ, ‖x - a‖ < r₁ / 4 → ∀ v : Fin (m + 1) → ℝ, ‖v‖ < r₁ / 4 →
      ∀ k, SignType.sign (G k (x, y0 + Ly v)) =
        ε k * SignType.sign ((pe (P k) (Fin.append (x - a) (Fin.init v))).eval (v (Fin.last m))) := by
    intro x hx v hv k
    have hX : ‖(Fin.append (m := p) (n := m + 1) (x - a) v : Fin (p + m + 1) → ℝ)‖ < ρ :=
      lt_trans (norm_append_lt hx hv) hr₁ρ
    have hs := hsign k _ hX
    rw [init_append_fin, append_last_fin] at hs
    have h1 : liftY p Ly (Fin.append (m := p) (n := m + 1) (x - a) v : Fin (p + m + 1) → ℝ) =
        Fin.append (m := p) (n := m + 1) (x - a) (Ly v) := by
      rw [liftY_apply]
      have e1 : (fun i => (Fin.append (m := p) (n := m + 1) (x - a) v : Fin (p + m + 1) → ℝ) (Fin.castAdd (m + 1) i)) =
          x - a := clmL_append (x - a) v
      have e2 : (fun j => (Fin.append (m := p) (n := m + 1) (x - a) v : Fin (p + m + 1) → ℝ) (Fin.natAdd p j)) = v :=
        clmR_append (x - a) v
      rw [e1, e2]
    have e : h k (liftY p Ly (Fin.append (m := p) (n := m + 1) (x - a) v : Fin (p + m + 1) → ℝ)) = G k (x, y0 + Ly v) := by
      rw [h1, hh_def, clmL_append, clmR_append, add_sub_cancel]
    rw [← e]
    exact hs
  refine ⟨δ, hδpos, r₁ / 4, by positivity, fun N lo' hi' hbox => ?_⟩
  -- Step F: the box conditions, affine in the eliminated variable
  obtain ⟨b, hb⟩ : ∃ b : Fin (m + 1) → ℝ, b = Ly (Pi.single (Fin.last m) 1) := ⟨_, rfl⟩
  obtain ⟨cf, hcf⟩ : ∃ cf : Fin (m + 1) → (Fin (p + m) → ℝ) → ℝ, ∀ j w,
      cf j w = y0 j + Ly (Fin.snoc (clmR p m w) 0) j := ⟨_, fun _ _ => rfl⟩
  have hcfA : ∀ j w, AnalyticAt ℝ (cf j) w := by
    intro j w
    have e : cf j = fun w => y0 j + Ly (Fin.snoc (clmR p m w) 0) j := funext (hcf j)
    rw [e]
    have h2 : AnalyticAt ℝ (fun w : Fin (p + m) → ℝ => Ly (Fin.snoc (clmR p m w) 0)) w :=
      (Ly.toContinuousLinearMap.analyticAt _).comp (analyticAt_snoc_clmR p m w)
    exact analyticAt_const.add ((anA_apply j _).comp h2)
  have hzj : ∀ w t j, (y0 + Ly (Fin.snoc (clmR p m w) t)) j = cf j w + b j * t := by
    intro w t j
    rw [snoc_split, map_add, map_smul, hcf, hb]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hboxiff : ∀ w t, y0 + Ly (Fin.snoc (clmR p m w) t) ∈ Set.Icc lo' hi' ↔
      ∀ j, 0 ≤ cf j w - lo' j + b j * t ∧ 0 ≤ hi' j - cf j w - b j * t := by
    intro w t
    simp only [Set.mem_Icc, Pi.le_def, hzj]
    constructor
    · rintro ⟨h1, h2⟩ j
      exact ⟨by linarith [h1 j], by linarith [h2 j]⟩
    · intro h
      exact ⟨fun j => by linarith [(h j).1], fun j => by linarith [(h j).2]⟩
  -- Step G: the polynomial family over `AnB (p+m) r₁` and Tarski–Seidenberg
  obtain ⟨ev, hev1, hev2, hev3⟩ : ∃ ev : Fin K ⊕ (Fin (m + 1) ⊕ Fin (m + 1)) → (AnB (p + m) r₁)[X],
      (∀ k w t, (pe (ev (Sum.inl k)) w).eval t = (pe (P k) w).eval t) ∧
      (∀ j w t, (pe (ev (Sum.inr (Sum.inl j))) w).eval t = cf j w - lo' j + b j * t) ∧
      (∀ j w t, (pe (ev (Sum.inr (Sum.inr j))) w).eval t = hi' j - cf j w - b j * t) := by
    have m1 : ∀ j, (fun w => cf j w - lo' j) ∈ AnB (p + m) r₁ := fun j w _ =>
      (hcfA j w).sub analyticAt_const
    have m2 : ∀ j, (fun w => hi' j - cf j w) ∈ AnB (p + m) r₁ := fun j w _ =>
      analyticAt_const.sub (hcfA j w)
    have m3 : ∀ j, (fun _ : Fin (p + m) → ℝ => b j) ∈ AnB (p + m) r₁ := fun j w _ =>
      analyticAt_const
    refine ⟨Sum.elim Q (Sum.elim (fun j => C ⟨_, m1 j⟩ + C ⟨_, m3 j⟩ * X)
      (fun j => C ⟨_, m2 j⟩ - C ⟨_, m3 j⟩ * X)), fun k w t => hQ k w t, fun j w t => ?_,
      fun j w t => ?_⟩
    · simp [pe, evR_apply]
    · simp [pe, evR_apply]
  let good : (Fin K ⊕ (Fin (m + 1) ⊕ Fin (m + 1)) → SignType) → Prop := fun ν =>
    (fun k => ε k * ν (Sum.inl k)) ∈ N ∧
      ∀ j, ν (Sum.inr (Sum.inl j)) ≠ -1 ∧ ν (Sum.inr (Sum.inr j)) ≠ -1
  let T : Set (Fin (p + m) → ℝ) := ⋃ ν ∈ Finset.univ.filter good,
    Rlz (A := Fin (p + m) → ℝ) (R := AnB (p + m) r₁) Finset.univ ev ν
  have hT : IsSA (AnB (p + m) r₁) T := IsSA.biUnion _ fun ν _ => ts_any _ _ _
  have hTmem0 : ∀ w, w ∈ T ↔ ∃ ν, good ν ∧ ∃ t : ℝ, ∀ i,
      SignType.sign ((pe (ev i) w).eval t) = ν i := by
    intro w
    simp only [T, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and, exists_prop]
    exact exists_congr fun ν => and_congr_right fun _ =>
      ⟨fun ⟨t, ht⟩ => ⟨t, fun i => ht i (Finset.mem_univ i)⟩, fun ⟨t, ht⟩ => ⟨t, fun i _ => ht i⟩⟩
  have hTmem : ∀ w, w ∈ T ↔ ∃ t : ℝ,
      (fun k => ε k * SignType.sign ((pe (P k) w).eval t)) ∈ N ∧
        y0 + Ly (Fin.snoc (clmR p m w) t) ∈ Set.Icc lo' hi' := by
    intro w
    rw [hTmem0]
    constructor
    · rintro ⟨ν, hν, t, ht⟩
      have hν' : ∀ i, SignType.sign ((pe (ev i) w).eval t) = ν i := ht
      refine ⟨t, ?_, ?_⟩
      · have e : (fun k => ε k * SignType.sign ((pe (P k) w).eval t)) =
            fun k => ε k * ν (Sum.inl k) := by
          funext k
          rw [← hν' (Sum.inl k), hev1]
        rw [e]
        exact hν.1
      · rw [hboxiff]
        intro j
        obtain ⟨h1, h2⟩ := hν.2 j
        rw [← hν' _, hev2, sign_ne_neg_one_iff'] at h1
        rw [← hν' _, hev3, sign_ne_neg_one_iff'] at h2
        exact ⟨h1, h2⟩
    · rintro ⟨t, hN, hB⟩
      refine ⟨fun i => SignType.sign ((pe (ev i) w).eval t), ⟨?_, fun j => ?_⟩, t, fun i => rfl⟩
      · have e : (fun k => ε k * SignType.sign ((pe (ev (Sum.inl k)) w).eval t)) =
            fun k => ε k * SignType.sign ((pe (P k) w).eval t) := by
          funext k
          rw [hev1]
        show (fun k => ε k * SignType.sign ((pe (ev (Sum.inl k)) w).eval t)) ∈ N
        rw [e]
        exact hN
      · rw [hboxiff] at hB
        show SignType.sign ((pe (ev (Sum.inr (Sum.inl j))) w).eval t) ≠ -1 ∧
          SignType.sign ((pe (ev (Sum.inr (Sum.inr j))) w).eval t) ≠ -1
        rw [hev2, hev3, sign_ne_neg_one_iff', sign_ne_neg_one_iff']
        exact hB j
  -- Step H: code form of `T` and (★_m) for the remaining `m` variables
  obtain ⟨n', f, hf, N', hTf⟩ := hT.codeForm
  set c : Fin m → ℝ := fun _ => r₁ / 4 with hc
  let g' : Fin n' → (Fin p → ℝ) × (Fin m → ℝ) → ℝ := fun i q => f i (Fin.append (q.1 - a) q.2)
  have hloc : LocLam p (projBox (codeIn g' N') (Set.Icc (-c) c)) (Metric.ball a (r₁ / 4)) := by
    intro a' ha'
    refine hS p n' g' a' (-c) c N' (fun i u hu => ?_) a' (Set.mem_singleton a')
    have hu' : ‖u‖ < r₁ := by
      have h1 : ‖u‖ ≤ r₁ / 4 := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨hu.1 j, hu.2 j⟩
      linarith
    have ha'' : ‖a' - a‖ < r₁ := by
      have := Metric.mem_ball.1 ha'
      rw [dist_eq_norm] at this
      linarith
    have hw : (Fin.append (a' - a) u : Fin (p + m) → ℝ) ∈ Metric.ball (0 : Fin (p + m) → ℝ) r₁ := by
      rw [mem_ball_zero_iff]
      exact norm_append_lt ha'' hu'
    have := AnalyticAt.comp_of_eq (hf i _ hw) (analyticAt_append_sub a (a', u)) rfl
    exact this
  -- Step I: the two projections agree on the ball
  refine LocLam.congr Metric.isOpen_ball hloc ?_
  ext x
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨⟨u, hu, huN⟩, hxb⟩
    refine ⟨?_, hxb⟩
    have hx : ‖x - a‖ < r₁ / 4 := by
      have := Metric.mem_ball.1 hxb
      rwa [dist_eq_norm] at this
    have hw : (Fin.append (x - a) u : Fin (p + m) → ℝ) ∈ T := by
      rw [hTf]
      exact huN
    obtain ⟨t, htN, htB⟩ := (hTmem _).1 hw
    rw [clmR_append] at htB
    refine ⟨y0 + Ly (Fin.snoc u t), htB, ?_⟩
    have hv : ‖(Fin.snoc u t : Fin (m + 1) → ℝ)‖ < r₁ / 4 := by
      apply hsmall
      have := hbox htB
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left] at this
      exact this
    show (fun k => SignType.sign (G k (x, y0 + Ly (Fin.snoc u t)))) ∈ N
    have e : (fun k => SignType.sign (G k (x, y0 + Ly (Fin.snoc u t)))) =
        fun k => ε k * SignType.sign ((pe (P k) (Fin.append (x - a) u)).eval t) := by
      funext k
      rw [KEY x hx _ hv k, Fin.init_snoc, Fin.snoc_last]
    rw [e]
    exact htN
  · rintro ⟨⟨y, hy, hyN⟩, hxb⟩
    refine ⟨?_, hxb⟩
    have hx : ‖x - a‖ < r₁ / 4 := by
      have := Metric.mem_ball.1 hxb
      rwa [dist_eq_norm] at this
    set v := Ly.symm (y - y0) with hvdef
    have hyv : y0 + Ly v = y := by
      rw [hvdef, ContinuousLinearEquiv.apply_symm_apply, add_sub_cancel]
    have hv : ‖v‖ < r₁ / 4 := by
      apply hsmall
      have := hbox hy
      rw [Metric.mem_closedBall, dist_eq_norm] at this
      rw [hvdef, ContinuousLinearEquiv.apply_symm_apply]
      exact this
    refine ⟨Fin.init v, ⟨fun j => ?_, fun j => ?_⟩, ?_⟩
    · have h1 := norm_le_pi_norm v (Fin.castSucc j)
      rw [Real.norm_eq_abs, abs_le] at h1
      show -(r₁ / 4) ≤ v (Fin.castSucc j)
      linarith [h1.1]
    · have h1 := norm_le_pi_norm v (Fin.castSucc j)
      rw [Real.norm_eq_abs, abs_le] at h1
      show v (Fin.castSucc j) ≤ r₁ / 4
      linarith [h1.2]
    · have hw : (Fin.append (x - a) (Fin.init v) : Fin (p + m) → ℝ) ∈ T := by
        refine (hTmem _).2 ⟨v (Fin.last m), ?_, ?_⟩
        · have e : (fun k => ε k * SignType.sign
              ((pe (P k) (Fin.append (x - a) (Fin.init v))).eval (v (Fin.last m)))) =
              fun k => SignType.sign (G k (x, y)) := by
            funext k
            rw [← KEY x hx v hv k, hyv]
          rw [e]
          exact hyN
        · rw [clmR_append, Fin.snoc_init_self, hyv]
          exact hy
      rw [hTf] at hw
      exact hw

end NEloc

end SubanalyticLib


/-! SubanalyticLib G6a (route G): Λ-balls, gluing local Λ-descriptions over a compact set,
substitution of Λ-functions into Λ-sets, the tube lemma for `Fin.append`, and their combination
`locLam_subst` (used for the `z`-variables of the D-trick in (★_{m+1})). -/

namespace SubanalyticLib

section Subst

open Filter Topology

set_option autoImplicit false

/-- sup-norm balls are Λ-sets. -/
theorem isSA_Lam_ball {p : ℕ} (b : Fin p → ℝ) {ε : ℝ} (hε : 0 < ε) :
    IsSA (Lam p) (Metric.ball b ε) := by
  have e : Metric.ball b ε =
      ⋂ i, ({x : Fin p → ℝ | 0 < x i - (b i - ε)} ∩ {x | 0 < (b i + ε) - x i}) := by
    ext x
    simp only [Metric.mem_ball, dist_pi_lt_iff hε, Real.dist_eq, abs_lt, Set.mem_iInter,
      Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro h i
      constructor <;> linarith [(h i).1, (h i).2]
    · intro h i
      constructor <;> linarith [(h i).1, (h i).2]
  rw [e]
  refine IsSA.iInter_fintype fun i => IsSA.inter ?_ ?_
  · exact IsSA.pos (Subring.sub_mem _ (InLam.coord i) (InLam.const (b i - ε)))
  · exact IsSA.pos (Subring.sub_mem _ (InLam.const (b i + ε)) (InLam.coord i))

/-- local Λ-descriptions glue to one Λ-description on an open neighbourhood of a compact set. -/
theorem LocLam.compact_cover {p : ℕ} {A V Kc : Set (Fin p → ℝ)} (h : LocLam p A V)
    (hK : IsCompact Kc) (hKV : Kc ⊆ V) :
    ∃ O : Set (Fin p → ℝ), IsOpen O ∧ Kc ⊆ O ∧ ∃ T, IsSA (Lam p) T ∧ A ∩ O = T ∩ O := by
  classical
  have hloc : ∀ b ∈ Kc, ∃ ε > 0, ∃ T, IsSA (Lam p) T ∧
      ∀ x ∈ Metric.ball b ε, (x ∈ A ↔ x ∈ T) := by
    intro b hb
    obtain ⟨U0, hU0, T, hT, hAT⟩ := h b (hKV hb)
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU0
    refine ⟨ε, hε, T, hT, fun x hx => ?_⟩
    have h1 := Set.ext_iff.1 hAT x
    simp only [Set.mem_inter_iff] at h1
    have hxU := hεU hx
    exact ⟨fun ha => (h1.1 ⟨ha, hxU⟩).1, fun ht => (h1.2 ⟨ht, hxU⟩).1⟩
  choose! ε hε T hT hAT using hloc
  obtain ⟨t, ht, hcov⟩ := hK.elim_nhds_subcover (fun b => Metric.ball b (ε b))
    (fun b hb => Metric.ball_mem_nhds b (hε b hb))
  refine ⟨⋃ b ∈ t, Metric.ball b (ε b), isOpen_biUnion fun b _ => Metric.isOpen_ball, hcov,
    ⋃ b ∈ t, (T b ∩ Metric.ball b (ε b)),
    IsSA.biUnion t fun b hb => IsSA.inter (hT b (ht b hb)) (isSA_Lam_ball b (hε b (ht b hb))), ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hxA, b, hbt, hxb⟩
    exact ⟨⟨b, hbt, (hAT b (ht b hbt) x hxb).1 hxA, hxb⟩, b, hbt, hxb⟩
  · rintro ⟨⟨b, hbt, hxT, hxb⟩, hO⟩
    exact ⟨(hAT b (ht b hbt) x hxb).2 hxT, hO⟩

/-- **substitution**: Λ-functions substituted into a Λ-set give a Λ-set. -/
theorem isSA_subst {p Z : ℕ} {T : Set (Fin (p + Z) → ℝ)} (hT : IsSA (Lam (p + Z)) T)
    (z : Fin Z → (Fin p → ℝ) → ℝ) (hz : ∀ j, InLam p (z j)) :
    IsSA (Lam p) {x | (Fin.append x (fun j => z j x) : Fin (p + Z) → ℝ) ∈ T} := by
  obtain ⟨n, h, hh, N, rfl⟩ := hT.codeForm
  have hzz : ∀ j : Fin (p + Z), InLam p (fun x => (Fin.append x (fun j => z j x) : Fin (p + Z) → ℝ) j) := by
    intro j
    induction j using Fin.addCases with
    | left i =>
      have e : (fun x : Fin p → ℝ => (Fin.append x (fun j => z j x) : Fin (p + Z) → ℝ) (Fin.castAdd Z i)) =
          fun x => x i := funext fun x => Fin.append_left _ _ _
      rw [e]
      exact InLam.coord i
    | right j =>
      have e : (fun x : Fin p → ℝ => (Fin.append x (fun j => z j x) : Fin (p + Z) → ℝ) (Fin.natAdd p j)) =
          z j := funext fun x => Fin.append_right _ _ _
      rw [e]
      exact hz j
  refine CodeForm.isSA ⟨n, fun i x => h i (Fin.append x (fun j => z j x)), fun i => ?_, N, rfl⟩
  exact InLam.subst (hh i) hzz

theorem continuous_append_pair (p Z : ℕ) :
    Continuous (fun q : (Fin p → ℝ) × (Fin Z → ℝ) => (Fin.append q.1 q.2 : Fin (p + Z) → ℝ)) := by
  refine continuous_pi fun i => ?_
  induction i using Fin.addCases with
  | left i =>
    simp only [Fin.append_left]
    exact (continuous_apply i).comp continuous_fst
  | right j =>
    simp only [Fin.append_right]
    exact (continuous_apply j).comp continuous_snd

/-- tube lemma for `Fin.append`. -/
theorem tube_append {p Z : ℕ} {O : Set (Fin (p + Z) → ℝ)} (hO : IsOpen O) {Zc : Set (Fin Z → ℝ)}
    (hZ : IsCompact Zc) (a : Fin p → ℝ) (h : ∀ z ∈ Zc, (Fin.append a z : Fin (p + Z) → ℝ) ∈ O) :
    ∃ η > 0, ∀ (x : Fin p → ℝ) (z : Fin Z → ℝ), ‖x - a‖ < η → z ∈ Zc →
      (Fin.append x z : Fin (p + Z) → ℝ) ∈ O := by
  have hn : IsOpen ((fun q : (Fin p → ℝ) × (Fin Z → ℝ) => (Fin.append q.1 q.2 : Fin (p + Z) → ℝ)) ⁻¹' O) :=
    hO.preimage (continuous_append_pair p Z)
  have hsub : ({a} : Set (Fin p → ℝ)) ×ˢ Zc ⊆
      (fun q : (Fin p → ℝ) × (Fin Z → ℝ) => (Fin.append q.1 q.2 : Fin (p + Z) → ℝ)) ⁻¹' O := by
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h z hz
  obtain ⟨u, v, hu, -, hau, hZv, huv⟩ := generalized_tube_lemma isCompact_singleton hZ hn hsub
  obtain ⟨η, hη, hηu⟩ := Metric.isOpen_iff.1 hu a (hau rfl)
  refine ⟨η, hη, fun x z hx hz => ?_⟩
  have hxu : x ∈ u := hηu (by rw [Metric.mem_ball, dist_eq_norm]; exact hx)
  exact huv (Set.mk_mem_prod hxu (hZv hz))

/-- **G6a**: a set that is locally Λ near `{a} × Zc` (`Zc` compact), pulled back along
`x ↦ (x, z x)` with Λ-functions `z` taking values in `Zc`, is Λ near `a`. -/
theorem locLam_subst {p Z : ℕ} {A V : Set (Fin (p + Z) → ℝ)} (hA : LocLam (p + Z) A V)
    {Zc : Set (Fin Z → ℝ)} (hZ : IsCompact Zc) (a : Fin p → ℝ)
    (haV : ∀ z ∈ Zc, (Fin.append a z : Fin (p + Z) → ℝ) ∈ V)
    (z : Fin Z → (Fin p → ℝ) → ℝ) (hz : ∀ j, InLam p (z j)) :
    ∃ η > 0, ∃ T', IsSA (Lam p) T' ∧ ∀ x : Fin p → ℝ, ‖x - a‖ < η → (fun j => z j x) ∈ Zc →
      ((Fin.append x (fun j => z j x) : Fin (p + Z) → ℝ) ∈ A ↔ x ∈ T') := by
  set Kc := (fun w : Fin Z → ℝ => (Fin.append a w : Fin (p + Z) → ℝ)) '' Zc with hKc
  have hcont : Continuous (fun w : Fin Z → ℝ => (Fin.append a w : Fin (p + Z) → ℝ)) :=
    (continuous_append_pair p Z).comp (continuous_const.prodMk continuous_id)
  have hK : IsCompact Kc := hZ.image hcont
  have hKV : Kc ⊆ V := by
    rintro _ ⟨w, hw, rfl⟩
    exact haV w hw
  obtain ⟨O, hO, hKO, T, hT, hAT⟩ := hA.compact_cover hK hKV
  obtain ⟨η, hη, htube⟩ := tube_append hO hZ a fun w hw => hKO ⟨w, hw, rfl⟩
  refine ⟨η, hη, _, isSA_subst hT z hz, fun x hx hzx => ?_⟩
  have hxO := htube x _ hx hzx
  have h1 := Set.ext_iff.1 hAT (Fin.append x (fun j => z j x))
  simp only [Set.mem_inter_iff] at h1
  simp only [Set.mem_setOf_eq]
  exact ⟨fun ha => (h1.1 ⟨ha, hxO⟩).1, fun ht => (h1.2 ⟨ht, hxO⟩).1⟩

end Subst

end SubanalyticLib


/-! SubanalyticLib G1 (Gabrielov route G, plan "L4 GABRIELOV ROUTE G"): the ring `CPS σ` of convergent
power series, uniqueness of convergent expansions, and the local-ring property. Appended to L2F. -/

namespace SubanalyticLib

section CPSRing

open MvPowerSeries Filter Topology

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem exists_pos_le_w {w : σ → ℝ} (hw : ∀ i, 0 < w i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ w i := by
  rcases isEmpty_or_nonempty σ with hσ | hσ
  · exact ⟨1, one_pos, fun i => (hσ.false i).elim⟩
  · obtain ⟨i0, hi0⟩ := Finite.exists_min w
    exact ⟨w i0, hw i0, hi0⟩

theorem Conv.minL {w w' : σ → ℝ} (hw : ∀ i, 0 < w i) (hw' : ∀ i, 0 < w' i)
    {f : MvPowerSeries σ ℝ} (hf : Conv w f) : Conv (fun i => min (w i) (w' i)) f :=
  hf.mono (fun i => le_min (hw i).le (hw' i).le) (fun i => min_le_left _ _)

theorem Conv.minR {w w' : σ → ℝ} (hw : ∀ i, 0 < w i) (hw' : ∀ i, 0 < w' i)
    {f : MvPowerSeries σ ℝ} (hf : Conv w' f) : Conv (fun i => min (w i) (w' i)) f :=
  hf.mono (fun i => le_min (hw i).le (hw' i).le) (fun i => min_le_right _ _)

variable (σ) in
/-- convergent power series: absolutely convergent on some closed polydisc. -/
def CPS : Subring (MvPowerSeries σ ℝ) where
  carrier := {f | ∃ w : σ → ℝ, (∀ i, 0 < w i) ∧ Conv w f}
  mul_mem' := by
    rintro a b ⟨w, hw, ha⟩ ⟨w', hw', hb⟩
    exact ⟨fun i => min (w i) (w' i), fun i => lt_min (hw i) (hw' i),
      Conv.mul (fun i => le_min (hw i).le (hw' i).le) (ha.minL hw hw') (hb.minR hw hw')⟩
  one_mem' := ⟨fun _ => 1, fun _ => one_pos, conv_one⟩
  add_mem' := by
    rintro a b ⟨w, hw, ha⟩ ⟨w', hw', hb⟩
    exact ⟨fun i => min (w i) (w' i), fun i => lt_min (hw i) (hw' i),
      Conv.add (fun i => le_min (hw i).le (hw' i).le) (ha.minL hw hw') (hb.minR hw hw')⟩
  zero_mem' := ⟨fun _ => 1, fun _ => one_pos, conv_zero⟩
  neg_mem' := by
    rintro a ⟨w, hw, ha⟩
    exact ⟨w, hw, ha.neg⟩

theorem X_mem_CPS (i : σ) : (X i : MvPowerSeries σ ℝ) ∈ CPS σ :=
  ⟨fun _ => 1, fun _ => one_pos, conv_X (fun _ => zero_le_one) i⟩

/-- **Uniqueness of convergent expansions**: a convergent series whose sum vanishes near `0` is `0`. -/
theorem eq_zero_of_ev_eventually_zero {w : σ → ℝ} (hw : ∀ i, 0 < w i) {f : MvPowerSeries σ ℝ}
    (hf : Conv w f) (h0 : ∀ᶠ x in 𝓝 (0 : σ → ℝ), ev f x = 0) : f = 0 := by
  obtain ⟨ε, hε, hεw⟩ := exists_pos_le_w hw
  have hb := hasFPowerSeriesOnBall_ev (fun i => (hw i).le) hf (r := ⟨ε, hε.le⟩) hε hεw
  have hz : HasFPowerSeriesAt (fun _ : σ → ℝ => (0 : ℝ)) (ps f) 0 :=
    hb.hasFPowerSeriesAt.congr h0
  have hdiag : ∀ n (y : σ → ℝ), ∑ α ∈ degs n, coeff α f * mon y α = 0 := by
    intro n y
    rw [← ps_diag]
    exact hz.apply_eq_zero n y
  ext α
  rw [map_zero]
  set n := Finsupp.degree α
  let P : MvPolynomial σ ℝ := ∑ β ∈ degs n, MvPolynomial.monomial β (coeff β f)
  have hP : P = 0 := by
    apply MvPolynomial.funext
    intro y
    simp only [P, map_zero, map_sum, MvPolynomial.eval_monomial]
    rw [← hdiag n y]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    rfl
  have hα : α ∈ degs n := mem_degs.2 rfl
  have hc := congrArg (MvPolynomial.coeff α) hP
  simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, MvPolynomial.coeff_zero] at hc
  rw [Finset.sum_ite_eq' (degs n) α (fun β => coeff β f), if_pos hα] at hc
  exact hc

theorem eq_of_ev_eventually_eq {w w' : σ → ℝ} (hw : ∀ i, 0 < w i) (hw' : ∀ i, 0 < w' i)
    {f g : MvPowerSeries σ ℝ} (hf : Conv w f) (hg : Conv w' g)
    (h : ∀ᶠ x in 𝓝 (0 : σ → ℝ), ev f x = ev g x) : f = g := by
  set v : σ → ℝ := fun i => min (w i) (w' i)
  have hv : ∀ i, 0 < v i := fun i => lt_min (hw i) (hw' i)
  have hf' : Conv v f := hf.minL hw hw'
  have hg' : Conv v g := hg.minR hw hw'
  obtain ⟨ε, hε, hεv⟩ := exists_pos_le_w hv
  have hball : ∀ᶠ x in 𝓝 (0 : σ → ℝ), ∀ i, |x i| ≤ v i := by
    filter_upwards [Metric.ball_mem_nhds (0 : σ → ℝ) hε] with x hx i
    have := (norm_le_pi_norm x i).trans (mem_ball_zero_iff.1 hx).le
    rw [Real.norm_eq_abs] at this
    exact this.trans (hεv i)
  have hsub := eq_zero_of_ev_eventually_zero hv (Conv.sub (fun i => (hv i).le) hf' hg') (by
    filter_upwards [hball, h] with x hx hxe
    rw [ev_sub hx hf' hg', hxe, sub_self])
  exact sub_eq_zero.1 hsub

/-- a convergent series with nonzero constant term is a unit of `CPS σ`. -/
theorem isUnit_CPS {a : CPS σ} (ha : constantCoeff (a : MvPowerSeries σ ℝ) ≠ 0) : IsUnit a := by
  obtain ⟨w, hw, hc⟩ := a.2
  set c := constantCoeff (a : MvPowerSeries σ ℝ) with hcdef
  set b := (a : MvPowerSeries σ ℝ) - C c with hbdef
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  have hb : Conv w b := Conv.sub hw0 hc (conv_C c)
  have hz : ∀ α, sdeg Finset.univ α = 0 → coeff α b = 0 := by
    intro α hα
    have h0 : α = 0 := by
      ext i
      have := (Finset.sum_eq_zero_iff.1 hα) i (Finset.mem_univ i)
      simpa using this
    subst h0
    simp [hbdef, hcdef]
  have hwb := wn_nonneg hw0 b
  have hcpos : 0 < |c| := abs_pos.2 ha
  set τ : ℝ := min 1 (|c| / (2 * (wn w b + 1))) with hτdef
  have hτ0 : 0 < τ := lt_min one_pos (div_pos hcpos (by positivity))
  obtain ⟨hcv, hwn⟩ := conv_scale hw0 Finset.univ hτ0.le (min_le_left _ _) hb hz
  set w' := scaleW Finset.univ τ w with hw'def
  have hw' : ∀ i, 0 < w' i := fun i => by
    simp only [hw'def, scaleW, Finset.mem_univ, if_true]
    exact mul_pos hτ0 (hw i)
  have hca : Conv w' (a : MvPowerSeries σ ℝ) := by
    have : (a : MvPowerSeries σ ℝ) = b + C c := by simp [hbdef]
    rw [this]
    exact Conv.add (fun i => (hw' i).le) hcv (conv_C c)
  have hq : wn w' ((a : MvPowerSeries σ ℝ) - C (constantCoeff (a : MvPowerSeries σ ℝ)))
      ≤ (1 / 2) * |constantCoeff (a : MvPowerSeries σ ℝ)| := by
    rw [← hcdef, ← hbdef]
    calc wn w' b ≤ τ * wn w b := hwn
      _ ≤ |c| / (2 * (wn w b + 1)) * wn w b :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hwb
      _ ≤ 1 / 2 * |c| := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  obtain ⟨hinv, -⟩ := conv_inv (fun i => (hw' i).le) hca (by norm_num : (0:ℝ) ≤ 1 / 2)
    (by norm_num) ha hq
  rw [isUnit_iff_exists_inv]
  exact ⟨⟨_, w', hw', hinv⟩, Subtype.ext (MvPowerSeries.mul_inv_cancel _ ha)⟩

theorem cps_nontrivial : Nontrivial (CPS σ) :=
  ⟨⟨0, 1, fun h => by
    have := congrArg (fun f : CPS σ => constantCoeff (f : MvPowerSeries σ ℝ)) h
    simp at this⟩⟩

theorem cps_isLocalRing : IsLocalRing (CPS σ) := by
  haveI := cps_nontrivial (σ := σ)
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self (fun a => ?_)
  by_cases ha : constantCoeff (a : MvPowerSeries σ ℝ) = 0
  · right
    apply isUnit_CPS
    simp [ha]
  · left
    exact isUnit_CPS ha

theorem isUnit_CPS_iff {a : CPS σ} : IsUnit a ↔ constantCoeff (a : MvPowerSeries σ ℝ) ≠ 0 := by
  refine ⟨fun h => ?_, isUnit_CPS⟩
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 h
  intro h0
  have := congrArg (fun f : CPS σ => constantCoeff (f : MvPowerSeries σ ℝ)) hb
  simp [h0] at this

end CPSRing

end SubanalyticLib


/-! SubanalyticLib G2: `CPS (Fin n)` is Noetherian (route G).  Germ calculus: `ser F` (the convergent
expansion of an analytic germ), ring maps `compHom Ψ` (composition with an analytic map fixing `0`),
linear changes `linEquiv L`, regularization, Weierstrass division into `CPS(Fin n)[X]`.
Needs L8a (CPS, uniqueness), L3g (`ev_single_axis`), L5g (`exists_regular_coord`). -/

namespace SubanalyticLib

section CPSNoeth

open MvPowerSeries Filter Topology

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem eventually_abs_le {w : σ → ℝ} (hw : ∀ i, 0 < w i) :
    ∀ᶠ x in 𝓝 (0 : σ → ℝ), ∀ i, |x i| ≤ w i := by
  obtain ⟨ε, hε, hεw⟩ := exists_pos_le_w hw
  filter_upwards [Metric.ball_mem_nhds (0 : σ → ℝ) hε] with x hx i
  have := (norm_le_pi_norm x i).trans (mem_ball_zero_iff.1 hx).le
  rw [Real.norm_eq_abs] at this
  exact this.trans (hεw i)

theorem analyticAt_ev_CPS {a : MvPowerSeries σ ℝ} (ha : a ∈ CPS σ) : AnalyticAt ℝ (ev a) 0 := by
  obtain ⟨w, hw, hc⟩ := ha
  obtain ⟨r, hr, h⟩ := analyticAt_ev_zero hw hc
  exact h 0 (by simpa using hr)

theorem ev_add_CPS {a b : MvPowerSeries σ ℝ} (ha : a ∈ CPS σ) (hb : b ∈ CPS σ) :
    ∀ᶠ x in 𝓝 (0 : σ → ℝ), ev (a + b) x = ev a x + ev b x := by
  obtain ⟨w, hw, hca⟩ := ha
  obtain ⟨w', hw', hcb⟩ := hb
  have hv : ∀ i, 0 < min (w i) (w' i) := fun i => lt_min (hw i) (hw' i)
  filter_upwards [eventually_abs_le hv] with x hx
  exact ev_add hx (hca.minL hw hw') (hcb.minR hw hw')

theorem ev_mul_CPS {a b : MvPowerSeries σ ℝ} (ha : a ∈ CPS σ) (hb : b ∈ CPS σ) :
    ∀ᶠ x in 𝓝 (0 : σ → ℝ), ev (a * b) x = ev a x * ev b x := by
  obtain ⟨w, hw, hca⟩ := ha
  obtain ⟨w', hw', hcb⟩ := hb
  have hv : ∀ i, 0 < min (w i) (w' i) := fun i => lt_min (hw i) (hw' i)
  filter_upwards [eventually_abs_le hv] with x hx
  exact ev_mul hx (fun i => (hv i).le) (hca.minL hw hw') (hcb.minR hw hw')

theorem ev_zero_series (x : σ → ℝ) : ev (0 : MvPowerSeries σ ℝ) x = 0 := by
  simp [ev]

open Classical in
/-- the convergent expansion at `0` of a germ (`0` if the germ is not analytic). -/
noncomputable def ser (F : (σ → ℝ) → ℝ) : MvPowerSeries σ ℝ :=
  if h : AnalyticAt ℝ F 0 then (exists_conv_of_analyticAt h).choose else 0

theorem ser_spec {F : (σ → ℝ) → ℝ} (hF : AnalyticAt ℝ F 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ Conv (fun _ => ρ) (ser F) ∧ ∀ x : σ → ℝ, ‖x‖ ≤ ρ → F x = ev (ser F) x := by
  rw [ser, dif_pos hF]
  obtain ⟨ρ, hρ, hc, h⟩ := (exists_conv_of_analyticAt hF).choose_spec
  exact ⟨ρ, hρ, hc, fun x hx => by simpa using h x hx⟩

theorem ser_mem (F : (σ → ℝ) → ℝ) : ser F ∈ CPS σ := by
  by_cases hF : AnalyticAt ℝ F 0
  · obtain ⟨ρ, hρ, hc, -⟩ := ser_spec hF
    exact ⟨fun _ => ρ, fun _ => hρ, hc⟩
  · rw [ser, dif_neg hF]
    exact (CPS σ).zero_mem

theorem ev_ser {F : (σ → ℝ) → ℝ} (hF : AnalyticAt ℝ F 0) :
    ∀ᶠ x in 𝓝 (0 : σ → ℝ), ev (ser F) x = F x := by
  obtain ⟨ρ, hρ, -, h⟩ := ser_spec hF
  filter_upwards [Metric.closedBall_mem_nhds (0 : σ → ℝ) hρ] with x hx
  exact (h x (by simpa using hx)).symm

theorem ser_eq_of {F : (σ → ℝ) → ℝ} {a : MvPowerSeries σ ℝ} (ha : a ∈ CPS σ)
    (hF : AnalyticAt ℝ F 0) (h : ∀ᶠ x in 𝓝 (0 : σ → ℝ), ev a x = F x) : ser F = a := by
  obtain ⟨w, hw, hc⟩ := ha
  obtain ⟨w', hw', hc'⟩ := ser_mem F
  exact eq_of_ev_eventually_eq hw' hw hc' hc (by
    filter_upwards [ev_ser hF, h] with x h1 h2
    rw [h1, h2])

theorem ser_congr {F G : (σ → ℝ) → ℝ} (hF : AnalyticAt ℝ F 0)
    (h : ∀ᶠ x in 𝓝 (0 : σ → ℝ), F x = G x) : ser F = ser G := by
  have hG : AnalyticAt ℝ G 0 := hF.congr h
  exact (ser_eq_of (ser_mem F) hG (by
    filter_upwards [ev_ser hF, h] with x h1 h2
    rw [h1, h2])).symm

theorem ser_ev {a : MvPowerSeries σ ℝ} (ha : a ∈ CPS σ) : ser (ev a) = a :=
  ser_eq_of ha (analyticAt_ev_CPS ha) (Eventually.of_forall fun _ => rfl)

variable {τ : Type*} [Fintype τ] [DecidableEq τ]

theorem tendsto_of_analytic {Ψ : (σ → ℝ) → (τ → ℝ)} (hΨ : AnalyticAt ℝ Ψ 0) (hΨ0 : Ψ 0 = 0) :
    Tendsto Ψ (𝓝 0) (𝓝 0) := by
  have := hΨ.continuousAt.tendsto
  rwa [hΨ0] at this

theorem analyticAt_ev_comp {Ψ : (σ → ℝ) → (τ → ℝ)} (hΨ : AnalyticAt ℝ Ψ 0) (hΨ0 : Ψ 0 = 0)
    {a : MvPowerSeries τ ℝ} (ha : a ∈ CPS τ) : AnalyticAt ℝ (fun x => ev a (Ψ x)) 0 := by
  have h := analyticAt_ev_CPS ha
  rw [← hΨ0] at h
  exact h.comp hΨ

/-- composition with an analytic map fixing `0`, as a ring map of convergent series. -/
noncomputable def compHom (Ψ : (σ → ℝ) → (τ → ℝ)) (hΨ : AnalyticAt ℝ Ψ 0) (hΨ0 : Ψ 0 = 0) :
    CPS τ →+* CPS σ where
  toFun a := ⟨ser (fun x => ev (a : MvPowerSeries τ ℝ) (Ψ x)), ser_mem _⟩
  map_one' := by
    apply Subtype.ext
    show ser (fun x => ev ((1 : CPS τ) : MvPowerSeries τ ℝ) (Ψ x)) = 1
    exact ser_eq_of (CPS σ).one_mem (analyticAt_ev_comp hΨ hΨ0 (1 : CPS τ).2)
      (Eventually.of_forall fun x => by simp [ev_one])
  map_mul' a b := by
    apply Subtype.ext
    show ser (fun x => ev ((a * b : CPS τ) : MvPowerSeries τ ℝ) (Ψ x)) =
      ser (fun x => ev (a : MvPowerSeries τ ℝ) (Ψ x)) * ser (fun x => ev (b : MvPowerSeries τ ℝ) (Ψ x))
    refine ser_eq_of (mul_mem (ser_mem _) (ser_mem _)) (analyticAt_ev_comp hΨ hΨ0 (a * b).2) ?_
    filter_upwards [ev_mul_CPS (ser_mem _) (ser_mem _), ev_ser (analyticAt_ev_comp hΨ hΨ0 a.2),
      ev_ser (analyticAt_ev_comp hΨ hΨ0 b.2),
      (tendsto_of_analytic hΨ hΨ0).eventually (ev_mul_CPS a.2 b.2)] with x h1 h2 h3 h4
    rw [h1, h2, h3]
    exact h4.symm
  map_zero' := by
    apply Subtype.ext
    show ser (fun x => ev ((0 : CPS τ) : MvPowerSeries τ ℝ) (Ψ x)) = 0
    exact ser_eq_of (CPS σ).zero_mem (analyticAt_ev_comp hΨ hΨ0 (0 : CPS τ).2)
      (Eventually.of_forall fun x => by simp [ev_zero_series])
  map_add' a b := by
    apply Subtype.ext
    show ser (fun x => ev ((a + b : CPS τ) : MvPowerSeries τ ℝ) (Ψ x)) =
      ser (fun x => ev (a : MvPowerSeries τ ℝ) (Ψ x)) + ser (fun x => ev (b : MvPowerSeries τ ℝ) (Ψ x))
    refine ser_eq_of (add_mem (ser_mem _) (ser_mem _)) (analyticAt_ev_comp hΨ hΨ0 (a + b).2) ?_
    filter_upwards [ev_add_CPS (ser_mem _) (ser_mem _), ev_ser (analyticAt_ev_comp hΨ hΨ0 a.2),
      ev_ser (analyticAt_ev_comp hΨ hΨ0 b.2),
      (tendsto_of_analytic hΨ hΨ0).eventually (ev_add_CPS a.2 b.2)] with x h1 h2 h3 h4
    rw [h1, h2, h3]
    exact h4.symm

theorem compHom_coe (Ψ : (σ → ℝ) → (τ → ℝ)) (hΨ : AnalyticAt ℝ Ψ 0) (hΨ0 : Ψ 0 = 0) (a : CPS τ) :
    ((compHom Ψ hΨ hΨ0 a : CPS σ) : MvPowerSeries σ ℝ) =
      ser (fun x => ev (a : MvPowerSeries τ ℝ) (Ψ x)) := rfl

theorem ev_compHom (Ψ : (σ → ℝ) → (τ → ℝ)) (hΨ : AnalyticAt ℝ Ψ 0) (hΨ0 : Ψ 0 = 0) (a : CPS τ) :
    ∀ᶠ x in 𝓝 (0 : σ → ℝ), ev ((compHom Ψ hΨ hΨ0 a : CPS σ) : MvPowerSeries σ ℝ) x =
      ev (a : MvPowerSeries τ ℝ) (Ψ x) :=
  ev_ser (analyticAt_ev_comp hΨ hΨ0 a.2)

theorem compHom_inv {Ψ₁ : (σ → ℝ) → (τ → ℝ)} {Ψ₂ : (τ → ℝ) → (σ → ℝ)} (h₁ : AnalyticAt ℝ Ψ₁ 0)
    (h₁0 : Ψ₁ 0 = 0) (h₂ : AnalyticAt ℝ Ψ₂ 0) (h₂0 : Ψ₂ 0 = 0) (hinv : ∀ x, Ψ₂ (Ψ₁ x) = x)
    (a : CPS σ) : compHom Ψ₁ h₁ h₁0 (compHom Ψ₂ h₂ h₂0 a) = a := by
  apply Subtype.ext
  rw [compHom_coe, compHom_coe]
  rw [ser_congr (analyticAt_ev_comp h₁ h₁0 (ser_mem _))
    ((tendsto_of_analytic h₁ h₁0).eventually (ev_ser (analyticAt_ev_comp h₂ h₂0 a.2)))]
  simp only [hinv]
  exact ser_ev a.2

/-- a linear change of coordinates as a ring automorphism of `CPS σ`. -/
noncomputable def linEquiv (L : (σ → ℝ) ≃L[ℝ] (σ → ℝ)) : CPS σ ≃+* CPS σ where
  toFun := compHom (fun x => L x) ((L : (σ → ℝ) →L[ℝ] (σ → ℝ)).analyticAt 0) (map_zero L)
  invFun := compHom (fun x => L.symm x) ((L.symm : (σ → ℝ) →L[ℝ] (σ → ℝ)).analyticAt 0)
      (map_zero L.symm)
  left_inv a := compHom_inv _ _ _ _ (fun x => L.apply_symm_apply x) a
  right_inv a := compHom_inv _ _ _ _ (fun x => L.symm_apply_apply x) a
  map_mul' := map_mul _
  map_add' := map_add _

theorem ev_linEquiv (L : (σ → ℝ) ≃L[ℝ] (σ → ℝ)) (a : CPS σ) :
    ∀ᶠ x in 𝓝 (0 : σ → ℝ), ev ((linEquiv L a : CPS σ) : MvPowerSeries σ ℝ) x =
      ev (a : MvPowerSeries σ ℝ) (L x) :=
  ev_compHom (fun x => L x) ((L : (σ → ℝ) →L[ℝ] (σ → ℝ)).analyticAt 0) (map_zero L) a

theorem continuous_single_last (n : ℕ) :
    Continuous (fun t : ℝ => (Pi.single (Fin.last n) t : Fin (n + 1) → ℝ)) := by
  refine continuous_pi fun i => ?_
  by_cases h : i = Fin.last n
  · subst h
    simp only [Pi.single_eq_same]
    exact continuous_id'
  · simpa [Pi.single_apply, h] using continuous_const

/-- **Regularization**: a nonzero convergent series becomes regular in the last variable after a
linear change of coordinates. -/
theorem exists_regular {n : ℕ} {a : CPS (Fin (n + 1))} (ha : a ≠ 0) :
    ∃ L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ), ∃ d : ℕ,
      (∀ j < d, coeff (Finsupp.single (Fin.last n) j)
        ((linEquiv L a : CPS _) : MvPowerSeries (Fin (n + 1)) ℝ) = 0) ∧
      coeff (Finsupp.single (Fin.last n) d)
        ((linEquiv L a : CPS _) : MvPowerSeries (Fin (n + 1)) ℝ) ≠ 0 := by
  have hnz : ¬ ∀ᶠ x in 𝓝 (0 : Fin (n + 1) → ℝ), ev (a : MvPowerSeries _ ℝ) x = 0 := by
    intro h
    obtain ⟨w, hw, hc⟩ := a.2
    exact ha (Subtype.ext (by simpa using eq_zero_of_ev_eventually_zero hw hc h))
  obtain ⟨k, L, hL⟩ := exists_regular_coord (analyticAt_ev_CPS a.2) hnz
  set L' := (coordSwap k (Fin.last n)).trans L with hL'
  refine ⟨L', ?_⟩
  set b := ((linEquiv L' a : CPS _) : MvPowerSeries (Fin (n + 1)) ℝ) with hb
  have hax : ∃ j, coeff (Finsupp.single (Fin.last n) j) b ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hL
    have hT : Tendsto (fun t : ℝ => (Pi.single (Fin.last n) t : Fin (n + 1) → ℝ)) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_single_last n).tendsto 0
    filter_upwards [hT.eventually (ev_linEquiv L' a)] with t ht
    have hsw : L' (Pi.single (Fin.last n) t) = L (Pi.single k t) := by
      rw [hL', ContinuousLinearEquiv.trans_apply, coordSwap_single]
    rw [← hsw, ← ht]
    exact ev_single_axis _ hcon t
  classical
  refine ⟨Nat.find hax, fun j hj => ?_, Nat.find_spec hax⟩
  by_contra h
  exact Nat.find_min hax hj h

theorem analyticAt_init (n : ℕ) :
    AnalyticAt ℝ (fun x : Fin (n + 1) → ℝ => (Fin.init x : Fin n → ℝ)) 0 :=
  analyticAt_pi_iff.2 fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => ℝ) (Fin.castSucc i)).analyticAt _

theorem init_zero (n : ℕ) : (Fin.init (0 : Fin (n + 1) → ℝ) : Fin n → ℝ) = 0 := by
  funext i
  rfl

/-- series of `CPS (Fin n)` seen in `CPS (Fin (n+1))` (not involving the last variable). -/
noncomputable def embInit (n : ℕ) : CPS (Fin n) →+* CPS (Fin (n + 1)) :=
  compHom (fun x => Fin.init x) (analyticAt_init n) (init_zero n)

noncomputable def Xlast (n : ℕ) : CPS (Fin (n + 1)) := ⟨X (Fin.last n), X_mem_CPS _⟩

theorem Xlast_coe (n : ℕ) : ((Xlast n : CPS (Fin (n + 1))) : MvPowerSeries (Fin (n + 1)) ℝ) =
    X (Fin.last n) := rfl

/-- `CPS(Fin n)[X] → CPS(Fin (n+1))`, `X ↦ x_last`. -/
noncomputable def iotaP (n : ℕ) : Polynomial (CPS (Fin n)) →+* CPS (Fin (n + 1)) :=
  Polynomial.eval₂RingHom (embInit n) (Xlast n)

lemma snoc_init_zero {n : ℕ} (x : Fin (n + 1) → ℝ) :
    (Fin.snoc (Fin.init x) (0 : ℝ) : Fin (n + 1) → ℝ) = Function.update x (Fin.last n) 0 := by
  conv_rhs => rw [← Fin.snoc_init_self x]
  rw [Fin.update_snoc_last]

theorem yslice_mem_range {n : ℕ} (j : ℕ) {r : MvPowerSeries (Fin (n + 1)) ℝ}
    {w : Fin (n + 1) → ℝ} (hw : ∀ i, 0 < w i) (hr : Conv w r) :
    ∃ s : CPS (Fin n), ((embInit n s : CPS _) : MvPowerSeries _ ℝ) = yslice (Fin.last n) j r := by
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  have hys : Conv w (yslice (Fin.last n) j r) := Conv.low (Fin.last n) hw0 1 (Conv.hat (Fin.last n) hw0 (hw _) j hr)
  have hysm : yslice (Fin.last n) j r ∈ CPS (Fin (n + 1)) := ⟨w, hw, hys⟩
  have hA : AnalyticAt ℝ
      (fun x' : Fin n → ℝ => ev (yslice (Fin.last n) j r) (Fin.snoc x' 0)) 0 := by
    exact (analyticAt_ev_CPS hysm).comp_of_eq (analyticAt_snoc0 n) (snoc_zero_zero n)
  refine ⟨⟨ser (fun x' : Fin n → ℝ => ev (yslice (Fin.last n) j r) (Fin.snoc x' 0)), ser_mem _⟩, ?_⟩
  unfold embInit
  rw [compHom_coe]
  refine ser_eq_of hysm (analyticAt_ev_comp (analyticAt_init n) (init_zero n) (ser_mem _)) ?_
  filter_upwards [(tendsto_of_analytic (analyticAt_init n) (init_zero n)).eventually (ev_ser hA)]
    with x hx
  rw [hx, snoc_init_zero, ev_yslice_update]

/-- **Weierstrass division in `CPS`**: modulo a series regular in the last variable, every series
is a polynomial in the last variable with coefficients in `CPS (Fin n)`. -/
theorem wd_CPS {n : ℕ} (a : CPS (Fin (n + 1))) {d : ℕ}
    (hreg : ∀ j < d, coeff (Finsupp.single (Fin.last n) j) (a : MvPowerSeries _ ℝ) = 0)
    (hd : coeff (Finsupp.single (Fin.last n) d) (a : MvPowerSeries _ ℝ) ≠ 0)
    (g : CPS (Fin (n + 1))) :
    ∃ q : CPS (Fin (n + 1)), ∃ p : Polynomial (CPS (Fin n)), g = q * a + iotaP n p := by
  obtain ⟨wa, hwa, hca⟩ := a.2
  obtain ⟨wg, hwg, hcg⟩ := g.2
  have hw0 : ∀ i, 0 < min (wa i) (wg i) := fun i => lt_min (hwa i) (hwg i)
  obtain ⟨w, hw, hwle, hdiv⟩ :=
    weierstrass_division (Fin.last n) hw0 d (hca.minL hwa hwg) hreg hd
  have hgw : Conv w (g : MvPowerSeries _ ℝ) :=
    hcg.mono (fun i => (hw i).le) (fun i => (hwle i).trans (min_le_right _ _))
  obtain ⟨q, r, hq, hr, hhat, hg⟩ := hdiv _ hgw
  choose s hs using fun j => yslice_mem_range (n := n) j hw hr
  refine ⟨⟨q, w, hw, hq⟩, ∑ j ∈ Finset.range d, Polynomial.monomial j (s j), ?_⟩
  have hι : iotaP n (∑ j ∈ Finset.range d, Polynomial.monomial j (s j)) =
      ∑ j ∈ Finset.range d, embInit n (s j) * Xlast n ^ j := by
    simp [iotaP, Polynomial.eval₂_monomial]
  apply Subtype.ext
  rw [hι]
  push_cast
  rw [hg, eq_sum_yslice (Fin.last n) d r hhat]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hs j, Xlast_coe, mul_comm]

theorem cps_noetherian_zero : IsNoetherianRing (CPS (Fin 0)) := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  by_cases h : I = ⊥
  · rw [h]
    exact Submodule.fg_bot
  · obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    have hu : IsUnit a := by
      apply isUnit_CPS
      intro hc
      apply ha0
      apply Subtype.ext
      ext α
      have : α = 0 := Finsupp.ext (fun i => Fin.elim0 i)
      subst this
      simpa using hc
    rw [Ideal.eq_top_of_isUnit_mem I haI hu]
    exact ⟨{1}, by rw [Finset.coe_singleton]; exact Ideal.span_singleton_one⟩

theorem cps_noetherian_succ {n : ℕ} (ih : IsNoetherianRing (CPS (Fin n))) :
    IsNoetherianRing (CPS (Fin (n + 1))) := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  by_cases h : I = ⊥
  · rw [h]
    exact Submodule.fg_bot
  obtain ⟨a0, ha0I, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨L, d, hreg, hd⟩ := exists_regular ha0
  set φ := linEquiv L with hφ
  suffices hJ : (I.map (φ : CPS (Fin (n + 1)) →+* CPS (Fin (n + 1)))).FG by
    have hI : I = (I.map (φ : CPS (Fin (n + 1)) →+* CPS (Fin (n + 1)))).map
        (φ.symm : CPS (Fin (n + 1)) →+* CPS (Fin (n + 1))) := by
      rw [Ideal.map_map]
      have : (φ.symm : CPS (Fin (n + 1)) →+* CPS (Fin (n + 1))).comp
          (φ : CPS (Fin (n + 1)) →+* CPS (Fin (n + 1))) = RingHom.id _ := by
        ext x
        simp
      rw [this, Ideal.map_id]
    rw [hI]
    exact hJ.map _
  set J := I.map (φ : CPS (Fin (n + 1)) →+* CPS (Fin (n + 1))) with hJdef
  have haJ : φ a0 ∈ J := Ideal.mem_map_of_mem _ ha0I
  haveI := ih
  have hfg : (J.comap (iotaP n)).FG := (isNoetherianRing_iff_ideal_fg _).1 inferInstance _
  have hJeq : J = Ideal.span {φ a0} ⊔ (J.comap (iotaP n)).map (iotaP n) := by
    apply le_antisymm
    · intro g hg
      obtain ⟨q, p, hgp⟩ := wd_CPS (φ a0) hreg hd g
      have hp : iotaP n p ∈ J := by
        have : iotaP n p = g - q * φ a0 := by rw [hgp]; ring
        rw [this]
        exact J.sub_mem hg (J.mul_mem_left q haJ)
      rw [hgp]
      exact Submodule.add_mem_sup (Ideal.mul_mem_left _ q (Ideal.mem_span_singleton_self _))
        (Ideal.mem_map_of_mem _ hp)
    · exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 haJ) Ideal.map_comap_le
  rw [hJeq]
  exact (Submodule.fg_span_singleton _).sup (hfg.map _)

/-- **The ring of convergent power series in `n` variables is Noetherian.** -/
theorem cps_noetherian : ∀ n : ℕ, IsNoetherianRing (CPS (Fin n))
  | 0 => cps_noetherian_zero
  | n + 1 => cps_noetherian_succ (cps_noetherian n)

end CPSNoeth

end SubanalyticLib


/-! SubanalyticLib G3 part 1 (route G): Krull closedness wrapper, y-coefficients `yCoeff Y γ h` of a
series in the variables `Y` (an `x`-series), and their behaviour under `lowPart`/`hatPart`. -/

namespace SubanalyticLib

section KrullWrap

open IsLocalRing

/-- **Krull**: in a Noetherian local ring, an element in `J + 𝔪^k` for every `k` lies in `J`. -/
theorem mem_of_forall_mem_sup_pow {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (J : Ideal R) (g : R) (h : ∀ k : ℕ, g ∈ J ⊔ (maximalIdeal R) ^ k) : g ∈ J := by
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := R ⧸ J) (maximalIdeal R)
    (maximalIdeal.isMaximal R).ne_top
  have hx : Ideal.Quotient.mk J g ∈ (⨅ i : ℕ, (maximalIdeal R) ^ i • ⊤ : Submodule R (R ⧸ J)) := by
    refine Submodule.mem_iInf _ |>.2 (fun k => ?_)
    obtain ⟨j, hj, m, hm, rfl⟩ := Submodule.mem_sup.1 (h k)
    have : Ideal.Quotient.mk J (j + m) = m • Ideal.Quotient.mk J 1 := by
      rw [map_add, Ideal.Quotient.eq_zero_iff_mem.2 hj, zero_add, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, map_one, mul_one]
    rw [this]
    exact Submodule.smul_mem_smul hm Submodule.mem_top
  rw [hK, Submodule.mem_bot] at hx
  exact Ideal.Quotient.eq_zero_iff_mem.1 hx

end KrullWrap

section YCoeff

open MvPowerSeries

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- the `y^γ`-coefficient (an `x`-series) of `h`, `Y` = the `y`-variables. -/
noncomputable def yCoeff (Y : Finset σ) (γ : σ →₀ ℕ) (h : MvPowerSeries σ ℝ) : MvPowerSeries σ ℝ :=
  fun α => if ∀ i ∈ Y, α i = 0 then coeff (α + γ) h else 0

theorem coeff_yCoeff (Y : Finset σ) (γ : σ →₀ ℕ) (h : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) :
    coeff α (yCoeff Y γ h) = if ∀ i ∈ Y, α i = 0 then coeff (α + γ) h else 0 := rfl

/-- the part of `h` not involving the variables of `S`. -/
noncomputable def lowS (S : Finset σ) (h : MvPowerSeries σ ℝ) : MvPowerSeries σ ℝ :=
  fun α => if ∀ i ∈ S, α i = 0 then coeff α h else 0

theorem coeff_lowS (S : Finset σ) (h : MvPowerSeries σ ℝ) (α : σ →₀ ℕ) :
    coeff α (lowS S h) = if ∀ i ∈ S, α i = 0 then coeff α h else 0 := rfl

theorem Conv.yCoeff {w : σ → ℝ} (hw : ∀ i, 0 < w i) (Y : Finset σ) (γ : σ →₀ ℕ)
    {h : MvPowerSeries σ ℝ} (hh : Conv w h) : Conv w (yCoeff Y γ h) := by
  have hγ : 0 < mw w γ := mw_pos hw γ
  have hs : Summable (fun α => wt w h (α + γ) / mw w γ) :=
    (hh.comp_injective (add_left_injective γ)).div_const _
  refine Summable.of_nonneg_of_le (wt_nonneg (fun i => (hw i).le) _) (fun α => ?_) hs
  unfold wt
  rw [coeff_yCoeff]
  split_ifs
  · rw [mw_add, le_div_iff₀ hγ, mul_assoc]
  · simp only [abs_zero, zero_mul]
    exact div_nonneg (mul_nonneg (abs_nonneg _) (mw_nonneg (fun i => (hw i).le) _)) hγ.le

theorem Conv.lowS {w : σ → ℝ} (hw : ∀ i, 0 ≤ w i) (S : Finset σ) {h : MvPowerSeries σ ℝ}
    (hh : Conv w h) : Conv w (lowS S h) := by
  refine Summable.of_nonneg_of_le (wt_nonneg hw _) (fun α => ?_) hh
  unfold wt
  rw [coeff_lowS]
  split_ifs
  · exact le_rfl
  · simp only [abs_zero, zero_mul]
    exact mul_nonneg (abs_nonneg _) (mw_nonneg hw _)

theorem yCoeff_mem (Y : Finset σ) (γ : σ →₀ ℕ) {h : MvPowerSeries σ ℝ} (hh : h ∈ CPS σ) :
    yCoeff Y γ h ∈ CPS σ := by
  obtain ⟨w, hw, hc⟩ := hh
  exact ⟨w, hw, hc.yCoeff hw Y γ⟩

theorem lowS_mem (S : Finset σ) {h : MvPowerSeries σ ℝ} (hh : h ∈ CPS σ) : lowS S h ∈ CPS σ := by
  obtain ⟨w, hw, hc⟩ := hh
  exact ⟨w, hw, hc.lowS (fun i => (hw i).le) S⟩

theorem lowS_empty (h : MvPowerSeries σ ℝ) : lowS ∅ h = h := by
  ext α
  simp [coeff_lowS]

theorem lowS_insert (y : σ) (S : Finset σ) (h : MvPowerSeries σ ℝ) :
    lowS (insert y S) h = lowPart y 1 (lowS S h) := by
  ext α
  simp only [coeff_lowS, coeff_lowPart, Finset.mem_insert, forall_eq_or_imp, Nat.lt_one_iff]
  by_cases h1 : α y = 0 <;> simp [h1]

theorem lowS_eq_yCoeff_zero (Y : Finset σ) (h : MvPowerSeries σ ℝ) : lowS Y h = yCoeff Y 0 h := by
  ext α
  simp [coeff_lowS, coeff_yCoeff]

theorem yCoeff_lowS {Y S : Finset σ} (hS : S ⊆ Y) (γ : σ →₀ ℕ) (h : MvPowerSeries σ ℝ) :
    yCoeff Y γ (lowS S h) = if ∀ i ∈ S, γ i = 0 then yCoeff Y γ h else 0 := by
  ext α
  simp only [coeff_yCoeff, coeff_lowS]
  by_cases hα : ∀ i ∈ Y, α i = 0
  · have key : (∀ i ∈ S, (α + γ) i = 0) ↔ ∀ i ∈ S, γ i = 0 := by
      refine forall₂_congr fun i hi => ?_
      simp [hα i (hS hi)]
    by_cases hγ : ∀ i ∈ S, γ i = 0
    · rw [if_pos hα, if_pos (key.2 hγ), if_pos hγ, coeff_yCoeff, if_pos hα]
    · rw [if_pos hα, if_neg (fun h' => hγ (key.1 h')), if_neg hγ, map_zero]
  · rw [if_neg hα]
    split_ifs <;> simp [coeff_yCoeff, hα]

theorem yCoeff_hatPart {Y : Finset σ} {y : σ} (hy : y ∈ Y) (γ : σ →₀ ℕ) (h : MvPowerSeries σ ℝ) :
    yCoeff Y γ (hatPart y 1 h) = yCoeff Y (γ + Finsupp.single y 1) h := by
  ext α
  simp only [coeff_yCoeff, coeff_hatPart, add_assoc]

end YCoeff

end SubanalyticLib


/-! SubanalyticLib G3 part 2 (route G): the `y`-tail lemma and Krull: a convergent series lies in the
ideal generated by its (pure-`y`) `y`-coefficients, and finitely many of them suffice. -/

namespace SubanalyticLib

section DTrick

open MvPowerSeries IsLocalRing

attribute [local instance] cps_isLocalRing cps_noetherian

variable {N : ℕ}

/-- `γ` involves only the `y`-variables `Y`. -/
def PureY (Y : Finset (Fin N)) (γ : Fin N →₀ ℕ) : Prop := ∀ i, i ∉ Y → γ i = 0

/-- the `y^γ`-coefficient as an element of `CPS`. -/
noncomputable def yc (Y : Finset (Fin N)) (γ : Fin N →₀ ℕ) (h : CPS (Fin N)) : CPS (Fin N) :=
  ⟨yCoeff Y γ h, yCoeff_mem Y γ h.2⟩

theorem hatPart_mem (y : Fin N) (d : ℕ) {h : MvPowerSeries (Fin N) ℝ} (hh : h ∈ CPS (Fin N)) :
    hatPart y d h ∈ CPS (Fin N) := by
  obtain ⟨w, hw, hc⟩ := hh
  exact ⟨w, hw, Conv.hat y (fun i => (hw i).le) (hw y) d hc⟩

theorem X_mem_maximalIdeal (i : Fin N) :
    (⟨X i, X_mem_CPS i⟩ : CPS (Fin N)) ∈ maximalIdeal (CPS (Fin N)) := by
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_CPS_iff]
  simp [constantCoeff_X]

/-- **y-tail lemma**: if all pure-`y` coefficients of `h` lie in `J`, then `h ∈ J + 𝔪^k`. -/
theorem tail_mem (Y : Finset (Fin N)) (J : Ideal (CPS (Fin N))) :
    ∀ k : ℕ, ∀ h : CPS (Fin N), (∀ γ, PureY Y γ → yc Y γ h ∈ J) →
      h ∈ J ⊔ (maximalIdeal (CPS (Fin N))) ^ k := by
  intro k
  induction k with
  | zero =>
    intro h _
    simp
  | succ k ih =>
    intro h hJ
    have key : ∀ S : Finset (Fin N), S ⊆ Y →
        h - (⟨lowS S h, lowS_mem S h.2⟩ : CPS (Fin N)) ∈
          J ⊔ (maximalIdeal (CPS (Fin N))) ^ (k + 1) := by
      intro S
      induction S using Finset.induction_on with
      | empty =>
        intro _
        have : h - (⟨lowS ∅ h, lowS_mem ∅ h.2⟩ : CPS (Fin N)) = 0 := by
          apply Subtype.ext
          simp [lowS_empty]
        rw [this]
        exact Submodule.zero_mem _
      | insert y S hyS ihS =>
        intro hS
        have hSY : S ⊆ Y := (Finset.subset_insert y S).trans hS
        have hyY : y ∈ Y := hS (Finset.mem_insert_self y S)
        have hmem := hatPart_mem y 1 (lowS_mem S h.2)
        set H : CPS (Fin N) := ⟨hatPart y 1 (lowS S h), hmem⟩ with hHdef
        have heq : h - (⟨lowS (insert y S) h, lowS_mem _ h.2⟩ : CPS (Fin N)) =
            (h - ⟨lowS S h, lowS_mem S h.2⟩) + ⟨X y, X_mem_CPS y⟩ * H := by
          apply Subtype.ext
          have e := low_add_hat y 1 (lowS S h)
          rw [pow_one] at e
          show (h : MvPowerSeries (Fin N) ℝ) - lowS (insert y S) h =
            ((h : MvPowerSeries (Fin N) ℝ) - lowS S h) + X y * hatPart y 1 (lowS S h)
          rw [lowS_insert]
          linear_combination e
        rw [heq]
        refine Submodule.add_mem _ (ihS hSY) ?_
        have hH : H ∈ J ⊔ (maximalIdeal (CPS (Fin N))) ^ k := by
          refine ih H (fun γ hγ => ?_)
          have hγ' : PureY Y (γ + Finsupp.single y 1) := by
            intro i hi
            have hiy : i ≠ y := fun h' => hi (h' ▸ hyY)
            simp [hγ i hi, Finsupp.single_apply, Ne.symm hiy]
          by_cases hc : ∀ i ∈ S, ((γ + Finsupp.single y 1 : Fin N →₀ ℕ) i) = 0
          · have : yc Y γ H = yc Y (γ + Finsupp.single y 1) h := by
              apply Subtype.ext
              show yCoeff Y γ (hatPart y 1 (lowS S h)) = yCoeff Y (γ + Finsupp.single y 1) h
              rw [yCoeff_hatPart hyY, yCoeff_lowS hSY, if_pos hc]
            rw [this]
            exact hJ _ hγ'
          · have : yc Y γ H = 0 := by
              apply Subtype.ext
              show yCoeff Y γ (hatPart y 1 (lowS S h)) = 0
              rw [yCoeff_hatPart hyY, yCoeff_lowS hSY, if_neg hc]
            rw [this]
            exact J.zero_mem
        obtain ⟨j, hj, m, hm, hjm⟩ := Submodule.mem_sup.1 hH
        rw [← hjm, mul_add]
        refine Submodule.add_mem_sup (J.mul_mem_left _ hj) ?_
        rw [pow_succ']
        exact Ideal.mul_mem_mul (X_mem_maximalIdeal y) hm
    have h1 := key Y le_rfl
    have h2 : (⟨lowS Y h, lowS_mem Y h.2⟩ : CPS (Fin N)) ∈ J := by
      have : (⟨lowS Y h, lowS_mem Y h.2⟩ : CPS (Fin N)) = yc Y 0 h :=
        Subtype.ext (lowS_eq_yCoeff_zero Y h)
      rw [this]
      exact hJ 0 (fun i _ => rfl)
    have : h = (h - ⟨lowS Y h, lowS_mem Y h.2⟩) + ⟨lowS Y h, lowS_mem Y h.2⟩ := by ring
    rw [this]
    exact Submodule.add_mem _ h1 (Submodule.mem_sup_left h2)

/-- **Krull + Noether**: `g` lies in the ideal of its pure-`y` coefficients, generated by finitely
many of them; the chosen indices `F` give distinct coefficients. -/
theorem dtrick_span (Y : Finset (Fin N)) (g : CPS (Fin N)) :
    ∃ F : Finset (Fin N →₀ ℕ), (∀ β ∈ F, PureY Y β) ∧ Set.InjOn (fun β => yc Y β g) F ∧
      g ∈ Ideal.span ((fun β => yc Y β g) '' (F : Set (Fin N →₀ ℕ))) ∧
      ∀ γ, PureY Y γ → yc Y γ g ∈ Ideal.span ((fun β => yc Y β g) '' (F : Set (Fin N →₀ ℕ))) := by
  classical
  set S : Set (CPS (Fin N)) := {x | ∃ γ, PureY Y γ ∧ yc Y γ g = x} with hSdef
  set J := Ideal.span S with hJdef
  obtain ⟨t, ht⟩ := (isNoetherianRing_iff_ideal_fg _).1 inferInstance J
  have hT : ∀ u ∈ t, ∃ T : Finset (CPS (Fin N)), ↑T ⊆ S ∧ u ∈ Submodule.span (CPS (Fin N)) ↑T := by
    intro u hu
    have : u ∈ J := ht ▸ Submodule.subset_span hu
    exact Submodule.mem_span_finite_of_mem_span this
  choose! T hTS hTu using hT
  set U := t.biUnion T with hUdef
  have hUS : (U : Set (CPS (Fin N))) ⊆ S := by
    intro x hx
    obtain ⟨u, hu, hx'⟩ := Finset.mem_biUnion.1 hx
    exact hTS u hu hx'
  have hJU : J = Ideal.span (U : Set (CPS (Fin N))) := by
    apply le_antisymm
    · rw [← ht]
      refine Submodule.span_le.2 (fun u hu => ?_)
      refine Submodule.span_mono (fun x hx => ?_) (hTu u hu)
      exact Finset.mem_biUnion.2 ⟨u, hu, hx⟩
    · exact Ideal.span_mono hUS
  have hpick : ∀ x ∈ U, ∃ γ, PureY Y γ ∧ yc Y γ g = x := fun x hx => hUS hx
  choose! β hβY hβ using hpick
  refine ⟨U.image β, ?_, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hb
    exact hβY x hx
  · intro b1 hb1 b2 hb2 heq
    obtain ⟨x1, hx1, rfl⟩ := Finset.mem_image.1 hb1
    obtain ⟨x2, hx2, rfl⟩ := Finset.mem_image.1 hb2
    have : x1 = x2 := by
      have h1 := hβ x1 hx1
      have h2 := hβ x2 hx2
      simp only at heq
      rw [← h1, ← h2, heq]
    rw [this]
  · have himg : (fun b => yc Y b g) '' ((U.image β : Finset _) : Set (Fin N →₀ ℕ)) = U := by
      ext x
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      constructor
      · rintro ⟨b, ⟨x', hx', rfl⟩, rfl⟩
        rw [hβ x' hx']
        exact hx'
      · intro hx
        exact ⟨β x, ⟨x, hx, rfl⟩, hβ x hx⟩
    rw [himg, ← hJU]
    exact mem_of_forall_mem_sup_pow J g (fun k =>
      tail_mem Y J k g (fun γ hγ => Ideal.subset_span ⟨γ, hγ, rfl⟩))
  · intro γ hγ
    have himg : (fun b => yc Y b g) '' ((U.image β : Finset _) : Set (Fin N →₀ ℕ)) = U := by
      ext x
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      constructor
      · rintro ⟨b, ⟨x', hx', rfl⟩, rfl⟩
        rw [hβ x' hx']
        exact hx'
      · intro hx
        exact ⟨β x, ⟨x, hx, rfl⟩, hβ x hx⟩
    rw [himg, ← hJU]
    exact Ideal.subset_span ⟨γ, hγ, rfl⟩

end DTrick

end SubanalyticLib


/-! SubanalyticLib G3c (route G): normalization of the D-trick expansion:
`g = Σ_{β∈F} yc β g * c β` with `yc β' (c β) = δ_{β β'}` for `β, β' ∈ F`. -/

namespace SubanalyticLib

section DNorm

open MvPowerSeries

variable {N : ℕ}

/-- `a` involves no `y`-variable. -/
def YFree (Y : Finset (Fin N)) (a : MvPowerSeries (Fin N) ℝ) : Prop :=
  ∀ α, coeff α a ≠ 0 → ∀ i ∈ Y, α i = 0

theorem yFree_yCoeff (Y : Finset (Fin N)) (γ : Fin N →₀ ℕ) (h : MvPowerSeries (Fin N) ℝ) :
    YFree Y (yCoeff Y γ h) := by
  intro α hα
  rw [coeff_yCoeff] at hα
  by_contra hc
  exact hα (if_neg hc)

theorem yFree_one (Y : Finset (Fin N)) : YFree Y (1 : MvPowerSeries (Fin N) ℝ) := by
  intro α hα i _
  rw [coeff_one] at hα
  by_cases h0 : α = 0
  · simp [h0]
  · exact absurd (if_neg h0) hα

theorem yCoeff_add (Y : Finset (Fin N)) (γ : Fin N →₀ ℕ) (a b : MvPowerSeries (Fin N) ℝ) :
    yCoeff Y γ (a + b) = yCoeff Y γ a + yCoeff Y γ b := by
  ext α
  simp only [coeff_yCoeff, map_add]
  split_ifs <;> simp

theorem yCoeff_sub (Y : Finset (Fin N)) (γ : Fin N →₀ ℕ) (a b : MvPowerSeries (Fin N) ℝ) :
    yCoeff Y γ (a - b) = yCoeff Y γ a - yCoeff Y γ b := by
  ext α
  simp only [coeff_yCoeff, map_sub]
  split_ifs <;> simp

theorem yCoeff_sum {ι : Type*} (s : Finset ι) (Y : Finset (Fin N)) (γ : Fin N →₀ ℕ)
    (f : ι → MvPowerSeries (Fin N) ℝ) :
    yCoeff Y γ (∑ i ∈ s, f i) = ∑ i ∈ s, yCoeff Y γ (f i) := by
  ext α
  simp only [coeff_yCoeff, map_sum]
  split_ifs <;> simp

/-- multiplying by a `y`-free series commutes with taking a pure-`y` coefficient. -/
theorem yCoeff_mul_left {Y : Finset (Fin N)} {γ : Fin N →₀ ℕ} (hγ : PureY Y γ)
    {a : MvPowerSeries (Fin N) ℝ} (ha : YFree Y a) (h : MvPowerSeries (Fin N) ℝ) :
    yCoeff Y γ (a * h) = a * yCoeff Y γ h := by
  classical
  ext α
  rw [coeff_yCoeff, coeff_mul, coeff_mul]
  by_cases hα : ∀ i ∈ Y, α i = 0
  · rw [if_pos hα]
    have hR : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal α, coeff q.1 a * coeff q.2 (yCoeff Y γ h)
        = coeff q.1 a * coeff (q.2 + γ) h := by
      intro q hq
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
      rw [coeff_yCoeff, if_pos]
      intro i hi
      have h1 := congrArg (fun f => f i) hq
      simp only [Finsupp.add_apply] at h1
      have h2 := hα i hi
      omega
    rw [Finset.sum_congr rfl hR]
    symm
    let e : (Fin N →₀ ℕ) × (Fin N →₀ ℕ) ↪ (Fin N →₀ ℕ) × (Fin N →₀ ℕ) :=
      ⟨fun q => (q.1, q.2 + γ), fun q r hqr => by
        simp only [Prod.mk.injEq] at hqr
        exact Prod.ext hqr.1 (add_right_cancel hqr.2)⟩
    have hmap : ∑ q ∈ Finset.HasAntidiagonal.antidiagonal α, coeff q.1 a * coeff (q.2 + γ) h
        = ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal α).map e, coeff p.1 a * coeff p.2 h := by
      rw [Finset.sum_map]
      rfl
    rw [hmap]
    apply Finset.sum_subset
    · intro p hp
      rw [Finset.mem_map] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq ⊢
      show q.1 + (q.2 + γ) = α + γ
      rw [← add_assoc, hq]
    · intro p hp hpn
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      by_contra hne
      have h1 : coeff p.1 a ≠ 0 := left_ne_zero_of_mul hne
      have hY := ha _ h1
      apply hpn
      rw [Finset.mem_map]
      refine ⟨(p.1, α - p.1), ?_, ?_⟩
      · rw [Finset.HasAntidiagonal.mem_antidiagonal]
        ext i
        have h2 := congrArg (fun f => f i) hp
        simp only [Finsupp.add_apply, Finsupp.tsub_apply] at h2 ⊢
        by_cases hi : i ∈ Y
        · have := hY i hi
          omega
        · have := hγ i hi
          omega
      · show (p.1, α - p.1 + γ) = p
        refine Prod.ext rfl ?_
        ext i
        have h2 := congrArg (fun f => f i) hp
        simp only [Finsupp.add_apply, Finsupp.tsub_apply] at h2 ⊢
        by_cases hi : i ∈ Y
        · have := hY i hi
          have := hα i hi
          omega
        · have := hγ i hi
          omega
  · rw [if_neg hα]
    symm
    apply Finset.sum_eq_zero
    intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    rw [coeff_yCoeff]
    split_ifs with h2
    · by_cases h1 : coeff q.1 a = 0
      · rw [h1, zero_mul]
      · exfalso
        apply hα
        intro i hi
        rw [← hq, Finsupp.add_apply, ha _ h1 i hi, h2 i hi]
    · rw [mul_zero]

/-- the pure-`y` coefficients of `y^β * a` (`a` y-free). -/
theorem yCoeff_monomial_mul {Y : Finset (Fin N)} {β γ : Fin N →₀ ℕ} (hβ : PureY Y β)
    (hγ : PureY Y γ) {a : MvPowerSeries (Fin N) ℝ} (ha : YFree Y a) :
    yCoeff Y γ (monomial β (1 : ℝ) * a) = if γ = β then a else 0 := by
  classical
  ext α
  rw [coeff_yCoeff, coeff_monomial_mul, one_mul]
  by_cases hα : ∀ i ∈ Y, α i = 0
  · rw [if_pos hα]
    split_ifs with hle hgb hgb
    · subst hgb
      rw [add_tsub_cancel_right]
    · rw [map_zero]
      by_contra hne
      have hY := ha _ hne
      apply hgb
      ext i
      by_cases hi : i ∈ Y
      · have h1 := hY i hi
        have h2 := hα i hi
        have h3 := Finsupp.le_def.1 hle i
        simp only [Finsupp.tsub_apply, Finsupp.add_apply] at h1 h3
        omega
      · rw [hγ i hi, hβ i hi]
    · subst hgb
      exact absurd le_add_self hle
    · rw [map_zero]
  · rw [if_neg hα]
    split_ifs with hgb
    · by_contra hne
      exact hα (ha α (fun h0 => hne h0.symm))
    · simp

theorem monomial_mem_CPS (β : Fin N →₀ ℕ) :
    (monomial β (1 : ℝ) : MvPowerSeries (Fin N) ℝ) ∈ CPS (Fin N) := by
  classical
  refine ⟨fun _ => 1, fun _ => one_pos, ?_⟩
  unfold Conv
  apply summable_of_ne_finset_zero (s := {β})
  intro α hα
  rw [Finset.mem_singleton] at hα
  simp [wt, coeff_monomial, hα]

/-- the monomial `y^β` as an element of `CPS`. -/
noncomputable def ymon (β : Fin N →₀ ℕ) : CPS (Fin N) := ⟨monomial β 1, monomial_mem_CPS β⟩

theorem coe_yc (Y : Finset (Fin N)) (γ : Fin N →₀ ℕ) (h : CPS (Fin N)) :
    ((yc Y γ h : CPS (Fin N)) : MvPowerSeries (Fin N) ℝ) = yCoeff Y γ h := rfl

theorem yc_add (Y : Finset (Fin N)) (γ : Fin N →₀ ℕ) (a b : CPS (Fin N)) :
    yc Y γ (a + b) = yc Y γ a + yc Y γ b :=
  Subtype.ext (yCoeff_add Y γ a b)

theorem yc_sub (Y : Finset (Fin N)) (γ : Fin N →₀ ℕ) (a b : CPS (Fin N)) :
    yc Y γ (a - b) = yc Y γ a - yc Y γ b :=
  Subtype.ext (yCoeff_sub Y γ a b)

theorem yc_sum {ι : Type*} (s : Finset ι) (Y : Finset (Fin N)) (γ : Fin N →₀ ℕ)
    (f : ι → CPS (Fin N)) : yc Y γ (∑ i ∈ s, f i) = ∑ i ∈ s, yc Y γ (f i) := by
  apply Subtype.ext
  rw [coe_yc]
  push_cast
  rw [yCoeff_sum]
  rfl

theorem yc_mul_left {Y : Finset (Fin N)} {γ : Fin N →₀ ℕ} (hγ : PureY Y γ) {a : CPS (Fin N)}
    (ha : YFree Y a) (h : CPS (Fin N)) : yc Y γ (a * h) = a * yc Y γ h :=
  Subtype.ext (yCoeff_mul_left hγ ha h)

theorem yc_mon_mul {Y : Finset (Fin N)} {β γ : Fin N →₀ ℕ} (hβ : PureY Y β) (hγ : PureY Y γ)
    {a : CPS (Fin N)} (ha : YFree Y a) : yc Y γ (ymon β * a) = if γ = β then a else 0 := by
  apply Subtype.ext
  have := yCoeff_monomial_mul hβ hγ ha
  split_ifs with hgb
  · rw [if_pos hgb] at this
    exact this
  · rw [if_neg hgb] at this
    exact this

theorem yc_mon {Y : Finset (Fin N)} {β γ : Fin N →₀ ℕ} (hβ : PureY Y β) (hγ : PureY Y γ) :
    yc Y γ (ymon β) = if γ = β then 1 else 0 := by
  have := yc_mon_mul hβ hγ (a := 1) (yFree_one Y)
  rwa [mul_one] at this

/-- **Normalized D-trick** (G3c): `g = Σ_{β∈F} g_β c_β` with finitely many pure-`y` indices and
`y^{β'}`-coefficient of `c_β` equal to `δ_{ββ'}` for `β, β' ∈ F`. -/
theorem dtrick_normalized (Y : Finset (Fin N)) (g : CPS (Fin N)) :
    ∃ F : Finset (Fin N →₀ ℕ), (∀ β ∈ F, PureY Y β) ∧ ∃ c : (Fin N →₀ ℕ) → CPS (Fin N),
      g = ∑ β ∈ F, yc Y β g * c β ∧
      ∀ β ∈ F, ∀ β' ∈ F, yc Y β' (c β) = if β' = β then 1 else 0 := by
  classical
  obtain ⟨F, hF, -, hg, -⟩ := dtrick_span Y g
  refine ⟨F, hF, ?_⟩
  have hg' : g ∈ Ideal.span (Set.range (fun β : F => yc Y β g)) := by
    have h0 := hg
    rwa [Set.image_eq_range] at h0
  obtain ⟨k0, hk0⟩ := (Ideal.mem_span_range_iff_exists_fun).1 hg'
  let k : (Fin N →₀ ℕ) → CPS (Fin N) := fun β => if h : β ∈ F then k0 ⟨β, h⟩ else 0
  have hk : g = ∑ β ∈ F, yc Y β g * k β := by
    conv_lhs => rw [← hk0]
    rw [← Finset.sum_coe_sort F]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp [k, mul_comm]
  have hfree : ∀ β, YFree Y (yc Y β g : MvPowerSeries (Fin N) ℝ) := fun β =>
    yFree_yCoeff Y β g
  have key : ∀ β' ∈ F, yc Y β' g = ∑ β ∈ F, yc Y β g * yc Y β' (k β) := by
    intro β' hβ'
    conv_lhs => rw [hk]
    rw [yc_sum]
    exact Finset.sum_congr rfl (fun β _ => yc_mul_left (hF β' hβ') (hfree β) (k β))
  let c : (Fin N →₀ ℕ) → CPS (Fin N) := fun β =>
    ymon β + k β - ∑ β' ∈ F, ymon β' * yc Y β' (k β)
  refine ⟨c, ?_, ?_⟩
  · have e1 : ∑ β ∈ F, yc Y β g * c β = ∑ β ∈ F, yc Y β g * ymon β + ∑ β ∈ F, yc Y β g * k β
        - ∑ β ∈ F, ∑ β' ∈ F, yc Y β g * (ymon β' * yc Y β' (k β)) := by
      simp only [c, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.mul_sum]
    have e2 : ∑ β ∈ F, ∑ β' ∈ F, yc Y β g * (ymon β' * yc Y β' (k β))
        = ∑ β ∈ F, yc Y β g * ymon β := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun β' hβ' => ?_)
      rw [key β' hβ', Finset.sum_mul]
      exact Finset.sum_congr rfl (fun β _ => by ring)
    rw [e1, e2, ← hk]
    ring
  · intro β hβ β'' hβ''
    simp only [c]
    rw [yc_sub, yc_add, yc_sum,
      Finset.sum_congr rfl (fun β' hβ' => yc_mon_mul (hF β' hβ') (hF β'' hβ'')
        (yFree_yCoeff Y β' (k β))),
      Finset.sum_ite_eq, if_pos hβ'', yc_mon (hF β hβ) (hF β'' hβ'')]
    abel

end DNorm

end SubanalyticLib


/-! SubanalyticLib G4a (route G): partial evaluation in the `y`-variables (slices): the `y`-expansion
`sliceSer Y h x` of a convergent series at an `x`-point, its convergence, and the identity theorem
"a slice vanishing near `0` has all pure-`y` coefficients `0`". -/

namespace SubanalyticLib

section Slice

open MvPowerSeries Filter Topology

variable {N : ℕ}

/-- the `Y`-coordinates of a point (other coordinates set to `0`). -/
def yproj (Y : Finset (Fin N)) (u : Fin N → ℝ) : Fin N → ℝ := fun i => if i ∈ Y then u i else 0

/-- the series with absolute-value coefficients. -/
noncomputable def absSer (h : MvPowerSeries (Fin N) ℝ) : MvPowerSeries (Fin N) ℝ :=
  fun μ => |coeff μ h|

theorem coeff_absSer (h : MvPowerSeries (Fin N) ℝ) (μ : Fin N →₀ ℕ) :
    coeff μ (absSer h) = |coeff μ h| := rfl

theorem conv_absSer {w : Fin N → ℝ} {h : MvPowerSeries (Fin N) ℝ} (hh : Conv w h) :
    Conv w (absSer h) := by
  unfold Conv at hh ⊢
  convert hh using 1
  funext μ
  simp [wt, coeff_absSer]

open Classical in
/-- the `y`-expansion of `h` at the `x`-point `x`: the coefficient of `y^δ` is `ev (yCoeff Y δ h) x`. -/
noncomputable def sliceSer (Y : Finset (Fin N)) (h : MvPowerSeries (Fin N) ℝ) (x : Fin N → ℝ) :
    MvPowerSeries (Fin N) ℝ := fun δ => if PureY Y δ then ev (yCoeff Y δ h) x else 0

open Classical in
theorem coeff_sliceSer (Y : Finset (Fin N)) (h : MvPowerSeries (Fin N) ℝ) (x : Fin N → ℝ)
    (δ : Fin N →₀ ℕ) :
    coeff δ (sliceSer Y h x) = if PureY Y δ then ev (yCoeff Y δ h) x else 0 := rfl

/-- **Slice expansion**: `h(x + v) = Σ_δ (Σ_α h_{α+δ} x^α) v^δ` for an `x`-point `x` and a
`y`-point `v`. -/
theorem hasSum_slice {Y : Finset (Fin N)} {w : Fin N → ℝ} {h : MvPowerSeries (Fin N) ℝ}
    (hh : Conv w h) {x v : Fin N → ℝ} (hxY : ∀ i ∈ Y, x i = 0) (hvY : ∀ i, i ∉ Y → v i = 0)
    (hx : ∀ i, |x i| ≤ w i) (hv : ∀ i, |v i| ≤ w i) :
    HasSum (fun δ => coeff δ (sliceSer Y h x) * mon v δ) (ev h (x + v)) := by
  classical
  have hxv : ∀ i, |(x + v) i| ≤ w i := by
    intro i
    by_cases hi : i ∈ Y
    · simp [hxY i hi, hv i]
    · simp [hvY i hi, hx i]
  have h1 : HasSum (fun μ => coeff μ h * mon (x + v) μ) (ev h (x + v)) :=
    (summable_term hxv hh).hasSum
  let f : (Fin N →₀ ℕ) × (Fin N →₀ ℕ) → ℝ := fun p =>
    if PureY Y p.1 ∧ (∀ i ∈ Y, p.2 i = 0) then coeff (p.2 + p.1) h * mon x p.2 * mon v p.1
    else 0
  let sp : (Fin N →₀ ℕ) → (Fin N →₀ ℕ) × (Fin N →₀ ℕ) := fun μ =>
    (μ.filter (· ∈ Y), μ.filter (· ∉ Y))
  have hsp : Function.Injective sp := by
    intro μ ν hμν
    simp only [sp, Prod.mk.injEq] at hμν
    ext i
    by_cases hi : i ∈ Y
    · have := congrArg (fun f => f i) hμν.1
      simpa [Finsupp.filter_apply, hi] using this
    · have := congrArg (fun f => f i) hμν.2
      simpa [Finsupp.filter_apply, hi] using this
  have hadd : ∀ μ : Fin N →₀ ℕ, μ.filter (· ∉ Y) + μ.filter (· ∈ Y) = μ := by
    intro μ
    ext i
    by_cases hi : i ∈ Y <;> simp [Finsupp.filter_apply, hi]
  have hmon : ∀ μ : Fin N →₀ ℕ,
      mon x (μ.filter (· ∉ Y)) * mon v (μ.filter (· ∈ Y)) = mon (x + v) μ := by
    intro μ
    unfold mon
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    by_cases hi : i ∈ Y
    · simp [Finsupp.filter_apply, hi, hxY i hi]
    · simp [Finsupp.filter_apply, hi, hvY i hi]
  have hfsp : f ∘ sp = fun μ => coeff μ h * mon (x + v) μ := by
    funext μ
    simp only [Function.comp, f, sp]
    rw [if_pos ⟨fun i hi => by simp [Finsupp.filter_apply, hi],
      fun i hi => by simp [Finsupp.filter_apply, hi]⟩, hadd μ, mul_assoc, hmon μ]
  have h2 : HasSum f (ev h (x + v)) := by
    rw [← hsp.hasSum_iff]
    · rw [hfsp]
      exact h1
    · intro p hp
      simp only [f]
      rw [if_neg]
      rintro ⟨hp1, hp2⟩
      apply hp
      refine ⟨p.2 + p.1, ?_⟩
      refine Prod.ext ?_ ?_
      · ext i
        by_cases hi : i ∈ Y
        · simp [sp, Finsupp.filter_apply, hi, hp2 i hi]
        · simp [sp, Finsupp.filter_apply, hi, hp1 i hi]
      · ext i
        by_cases hi : i ∈ Y
        · simp [sp, Finsupp.filter_apply, hi, hp2 i hi]
        · simp [sp, Finsupp.filter_apply, hi, hp1 i hi]
  have h3 := h2.prod_fiberwise (fun δ => (h2.summable.prod_factor δ).hasSum)
  convert h3 using 1
  funext δ
  rw [coeff_sliceSer]
  by_cases hδ : PureY Y δ
  · rw [if_pos hδ, ev, ← tsum_mul_right]
    refine tsum_congr (fun α => ?_)
    simp only [f, coeff_yCoeff]
    by_cases hα : ∀ i ∈ Y, α i = 0
    · rw [if_pos hα, if_pos ⟨hδ, hα⟩]
    · rw [if_neg hα, if_neg (fun hh' => hα hh'.2)]
      ring
  · rw [if_neg hδ, zero_mul]
    symm
    refine (tsum_congr (fun α => ?_)).trans tsum_zero
    simp only [f]
    rw [if_neg (fun hh' => hδ hh'.1)]

theorem conv_sliceSer {Y : Finset (Fin N)} {w : Fin N → ℝ} (hw : ∀ i, 0 < w i)
    {h : MvPowerSeries (Fin N) ℝ} (hh : Conv w h) {x : Fin N → ℝ} (hx : ∀ i, |x i| ≤ w i) :
    Conv w (sliceSer Y h x) := by
  classical
  set xw : Fin N → ℝ := fun i => if i ∈ Y then 0 else w i with hxw
  set vw : Fin N → ℝ := fun i => if i ∈ Y then w i else 0 with hvw
  have hS := (hasSum_slice (Y := Y) (conv_absSer hh) (x := xw) (v := vw)
    (fun i hi => by simp [xw, hi]) (fun i hi => by simp [vw, hi])
    (fun i => by by_cases hi : i ∈ Y <;> simp [xw, hi, abs_of_pos (hw i), (hw i).le])
    (fun i => by by_cases hi : i ∈ Y <;> simp [vw, hi, abs_of_pos (hw i), (hw i).le])).summable
  refine Summable.of_nonneg_of_le (wt_nonneg (fun i => (hw i).le) _) (fun δ => ?_) hS
  unfold wt
  rw [coeff_sliceSer, coeff_sliceSer]
  by_cases hδ : PureY Y δ
  · rw [if_pos hδ, if_pos hδ]
    have hmw : mon vw δ = mw w δ := by
      unfold mon mw
      refine Finset.prod_congr rfl (fun i _ => ?_)
      by_cases hi : i ∈ Y
      · simp [vw, hi]
      · simp [vw, hi, hδ i hi]
    have hwn : ev (yCoeff Y δ (absSer h)) xw = wn w (yCoeff Y δ h) := by
      unfold ev wn
      refine tsum_congr (fun α => ?_)
      unfold wt
      rw [coeff_yCoeff, coeff_yCoeff]
      by_cases hα : ∀ i ∈ Y, α i = 0
      · rw [if_pos hα, if_pos hα, coeff_absSer]
        congr 1
        unfold mon mw
        refine Finset.prod_congr rfl (fun i _ => ?_)
        by_cases hi : i ∈ Y
        · simp [hα i hi]
        · simp [xw, hi]
      · rw [if_neg hα, if_neg hα]
        simp
    rw [hmw, hwn]
    exact mul_le_mul_of_nonneg_right (abs_ev_le hx (hh.yCoeff hw Y δ))
      (mw_nonneg (fun i => (hw i).le) _)
  · rw [if_neg hδ, if_neg hδ]
    simp

theorem ev_sliceSer {Y : Finset (Fin N)} {w : Fin N → ℝ} {h : MvPowerSeries (Fin N) ℝ}
    (hh : Conv w h) {x : Fin N → ℝ} (hxY : ∀ i ∈ Y, x i = 0) (hx : ∀ i, |x i| ≤ w i)
    {u : Fin N → ℝ} (hu : ∀ i, |u i| ≤ w i) (hw : ∀ i, 0 ≤ w i) :
    ev (sliceSer Y h x) u = ev h (x + yproj Y u) := by
  classical
  have hv : ∀ i, i ∉ Y → yproj Y u i = 0 := fun i hi => by simp [yproj, hi]
  have hv' : ∀ i, |yproj Y u i| ≤ w i := fun i => by
    by_cases hi : i ∈ Y
    · simp [yproj, hi, hu i]
    · simp [yproj, hi, hw i]
  rw [← (hasSum_slice hh hxY hv hx hv').tsum_eq, ev]
  refine tsum_congr (fun δ => ?_)
  rw [coeff_sliceSer]
  by_cases hδ : PureY Y δ
  · rw [if_pos hδ]
    congr 1
    unfold mon
    refine Finset.prod_congr rfl (fun i _ => ?_)
    by_cases hi : i ∈ Y
    · simp [yproj, hi]
    · simp [yproj, hi, hδ i hi]
  · rw [if_neg hδ]
    simp

/-- **Slice identity theorem**: if `h(x + y) = 0` for all small `y`-points `y`, every pure-`y`
coefficient of `h` vanishes at `x`. -/
theorem ev_yCoeff_eq_zero_of_slice {Y : Finset (Fin N)} {w : Fin N → ℝ} (hw : ∀ i, 0 < w i)
    {h : MvPowerSeries (Fin N) ℝ} (hh : Conv w h) {x : Fin N → ℝ} (hxY : ∀ i ∈ Y, x i = 0)
    (hx : ∀ i, |x i| ≤ w i) (h0 : ∀ᶠ u in 𝓝 (0 : Fin N → ℝ), ev h (x + yproj Y u) = 0)
    {γ : Fin N →₀ ℕ} (hγ : PureY Y γ) : ev (yCoeff Y γ h) x = 0 := by
  classical
  have hH : sliceSer Y h x = 0 := by
    refine eq_zero_of_ev_eventually_zero hw (conv_sliceSer hw hh hx) ?_
    filter_upwards [h0, eventually_abs_le hw] with u hu hu'
    rw [ev_sliceSer hh hxY hx hu' (fun i => (hw i).le), hu]
  have := congrArg (coeff γ) hH
  rwa [coeff_sliceSer, if_pos hγ, map_zero] at this

/-- a `y`-free series does not see the `y`-coordinates. -/
theorem ev_add_yproj_of_yFree {Y : Finset (Fin N)} {a : MvPowerSeries (Fin N) ℝ} (ha : YFree Y a)
    (x u : Fin N → ℝ) : ev a (x + yproj Y u) = ev a x := by
  unfold ev
  refine tsum_congr (fun α => ?_)
  by_cases hα : coeff α a = 0
  · simp [hα]
  · congr 1
    unfold mon
    refine Finset.prod_congr rfl (fun i _ => ?_)
    by_cases hi : i ∈ Y
    · simp [ha α hα i hi]
    · simp [yproj, hi]

end Slice

end SubanalyticLib


/-! SubanalyticLib G4b (route G): value form of the normalized D-trick and nondegeneracy:
`g(x,y) = Σ_β g_β(x) c_β(x,y)`, and `Σ_β z_β c_β(x,·) ≡ 0` near `0` forces `z = 0` on `F`. -/

namespace SubanalyticLib

section Nondeg

open MvPowerSeries Filter Topology

variable {N : ℕ}

theorem yCoeff_smul (Y : Finset (Fin N)) (γ : Fin N →₀ ℕ) (r : ℝ) (h : MvPowerSeries (Fin N) ℝ) :
    yCoeff Y γ (r • h) = r • yCoeff Y γ h := by
  ext α
  simp only [coeff_yCoeff, map_smul]
  split_ifs <;> simp

theorem conv_zero' (w : Fin N → ℝ) : Conv w (0 : MvPowerSeries (Fin N) ℝ) := by
  have h0 : wt w (0 : MvPowerSeries (Fin N) ℝ) = fun _ => 0 := by
    funext α
    simp [wt]
  show Summable (wt w 0)
  rw [h0]
  exact summable_zero

theorem conv_sum {ι : Type*} (s : Finset ι) {w : Fin N → ℝ} (hw : ∀ i, 0 ≤ w i)
    (f : ι → MvPowerSeries (Fin N) ℝ) (hf : ∀ i ∈ s, Conv w (f i)) : Conv w (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using conv_zero' w
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add hw
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem ev_sum {ι : Type*} (s : Finset ι) {w : Fin N → ℝ} (hw : ∀ i, 0 ≤ w i) {x : Fin N → ℝ}
    (hx : ∀ i, |x i| ≤ w i) (f : ι → MvPowerSeries (Fin N) ℝ) (hf : ∀ i ∈ s, Conv w (f i)) :
    ev (∑ i ∈ s, f i) x = ∑ i ∈ s, ev (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ev_zero_series]
  | @insert a s ha ih =>
    have hs : ∀ i ∈ s, Conv w (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      ev_add hx (hf a (Finset.mem_insert_self a s)) (conv_sum s hw f hs), ih hs]

/-- finitely many convergent series converge on a common polydisc. -/
theorem exists_common_weight {ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries (Fin N) ℝ)
    (hf : ∀ i ∈ s, f i ∈ CPS (Fin N)) :
    ∃ w : Fin N → ℝ, (∀ i, 0 < w i) ∧ ∀ i ∈ s, Conv w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 1, fun _ => one_pos, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨w, hw, hws⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    obtain ⟨w', hw', hwa⟩ := hf a (Finset.mem_insert_self a s)
    refine ⟨fun i => min (w i) (w' i), fun i => lt_min (hw i) (hw' i), ?_⟩
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hwa.mono (fun j => (lt_min (hw j) (hw' j)).le) (fun j => min_le_right _ _)
    · exact (hws i hi).mono (fun j => (lt_min (hw j) (hw' j)).le) (fun j => min_le_left _ _)

/-- **value D-trick**: `g(x + y) = Σ_β g_β(x) · c_β(x + y)` on a common polydisc. -/
theorem dtrick_value {Y : Finset (Fin N)} {F : Finset (Fin N →₀ ℕ)} (g : CPS (Fin N))
    (c : (Fin N →₀ ℕ) → CPS (Fin N)) (hg : g = ∑ β ∈ F, yc Y β g * c β) {w : Fin N → ℝ}
    (hw : ∀ i, 0 < w i)
    (hcw : ∀ β ∈ F, Conv w ((yc Y β g : CPS (Fin N)) : MvPowerSeries (Fin N) ℝ) ∧
      Conv w ((c β : CPS (Fin N)) : MvPowerSeries (Fin N) ℝ))
    (x u : Fin N → ℝ) (hp : ∀ i, |(x + yproj Y u) i| ≤ w i) :
    ev (g : MvPowerSeries (Fin N) ℝ) (x + yproj Y u) =
      ∑ β ∈ F, ev ((yc Y β g : CPS (Fin N)) : MvPowerSeries (Fin N) ℝ) x *
        ev ((c β : CPS (Fin N)) : MvPowerSeries (Fin N) ℝ) (x + yproj Y u) := by
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  have hcoe : (g : MvPowerSeries (Fin N) ℝ) =
      ∑ β ∈ F, ((yc Y β g : CPS (Fin N)) : MvPowerSeries (Fin N) ℝ) *
        ((c β : CPS (Fin N)) : MvPowerSeries (Fin N) ℝ) := by
    conv_lhs => rw [hg]
    push_cast
    rfl
  rw [hcoe, ev_sum F hw0 hp _ (fun β hβ => (hcw β hβ).1.mul hw0 (hcw β hβ).2)]
  refine Finset.sum_congr rfl (fun β hβ => ?_)
  rw [ev_mul hp hw0 (hcw β hβ).1 (hcw β hβ).2,
    ev_add_yproj_of_yFree (a := ((yc Y β g : CPS (Fin N)) : MvPowerSeries (Fin N) ℝ))
      (yFree_yCoeff Y β g) x u]

/-- **Nondegeneracy** of a normalized expansion: if `Σ_{β∈F} z_β c_β(x + y)` vanishes for all
small `y`-points `y`, then `z_β = 0` for every `β ∈ F`. -/
theorem normalized_nondeg {Y : Finset (Fin N)} {F : Finset (Fin N →₀ ℕ)}
    (hF : ∀ β ∈ F, PureY Y β) {c : (Fin N →₀ ℕ) → MvPowerSeries (Fin N) ℝ}
    (hn : ∀ β ∈ F, ∀ β' ∈ F, yCoeff Y β' (c β) = if β' = β then 1 else 0)
    {w : Fin N → ℝ} (hw : ∀ i, 0 < w i) (hc : ∀ β ∈ F, Conv w (c β))
    {x : Fin N → ℝ} (hxY : ∀ i ∈ Y, x i = 0) (hx : ∀ i, |x i| ≤ w i) (z : (Fin N →₀ ℕ) → ℝ)
    (h0 : ∀ᶠ u in 𝓝 (0 : Fin N → ℝ), ∑ β ∈ F, z β * ev (c β) (x + yproj Y u) = 0) :
    ∀ β ∈ F, z β = 0 := by
  classical
  have hw0 : ∀ i, 0 ≤ w i := fun i => (hw i).le
  set h := ∑ β ∈ F, z β • c β with hh
  have hcz : ∀ β ∈ F, Conv w (z β • c β) := fun β hβ => (hc β hβ).smul (z β)
  have hconv : Conv w h := conv_sum F hw0 _ hcz
  have h0' : ∀ᶠ u in 𝓝 (0 : Fin N → ℝ), ev h (x + yproj Y u) = 0 := by
    filter_upwards [h0, eventually_abs_le hw] with u hu hu'
    have hxu : ∀ i, |(x + yproj Y u) i| ≤ w i := by
      intro i
      by_cases hi : i ∈ Y
      · simp [yproj, hi, hxY i hi, hu' i]
      · simp [yproj, hi, hx i]
    rw [hh, ev_sum F hw0 hxu _ hcz, ← hu]
    exact Finset.sum_congr rfl (fun β _ => ev_smul _ _ _)
  intro β' hβ'
  have hcy : ∀ β ∈ F, Conv w (yCoeff Y β' (z β • c β)) := fun β hβ => by
    rw [yCoeff_smul]
    exact ((hc β hβ).yCoeff hw Y β').smul _
  have hterm : ∀ β ∈ F, ev (yCoeff Y β' (z β • c β)) x = if β' = β then z β else 0 := by
    intro β hβ
    rw [yCoeff_smul, hn β hβ β' hβ', ev_smul]
    split_ifs <;> simp [ev_one, ev_zero_series]
  have := ev_yCoeff_eq_zero_of_slice hw hconv hxY hx h0' (hF β' hβ')
  rw [hh, yCoeff_sum, ev_sum F hw0 hx _ hcy, Finset.sum_congr rfl hterm, Finset.sum_ite_eq,
    if_pos hβ'] at this
  exact this

end Nondeg

end SubanalyticLib


/-! SubanalyticLib G6b (route G): the D-trick at a point `(a, y0)` in function form (`dtrick_at`):
`g_k(x,y) = Σ_{β∈F_k} gc_kβ(x) · C_kβ(x,y)` near `(a, y0)`, with `gc` analytic at `a`, `C` analytic at
`(a, y0)` and the `C_k·(a, ·)` linearly independent as germs at `y0` (normalized nondegeneracy).
Needs L8g (dtrick_normalized, dtrick_value, normalized_nondeg) and L9e (clmL, clmR, analyticAt_append_sub). -/

namespace SubanalyticLib

section DTat

open Filter Topology

set_option autoImplicit false

/-- the `y`-coordinates (the last `q`) of `ℝ^(p+q)`. -/
def Ycoords (p q : ℕ) : Finset (Fin (p + q)) := Finset.univ.image (Fin.natAdd p)

theorem not_mem_Ycoords_castAdd {p q : ℕ} (i : Fin p) : Fin.castAdd q i ∉ Ycoords p q := by
  simp only [Ycoords, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
  intro j h
  rw [Fin.ext_iff] at h
  simp only [Fin.coe_natAdd, Fin.coe_castAdd] at h
  have := i.isLt
  omega

theorem mem_Ycoords_natAdd {p q : ℕ} (j : Fin q) : Fin.natAdd p j ∈ Ycoords p q :=
  Finset.mem_image_of_mem _ (Finset.mem_univ j)

theorem yproj_append {p q : ℕ} (u : Fin p → ℝ) (v : Fin q → ℝ) :
    yproj (Ycoords p q) (Fin.append u v) = Fin.append 0 v := by
  funext i
  induction i using Fin.addCases with
  | left i => simp [yproj, not_mem_Ycoords_castAdd i]
  | right j => simp [yproj, mem_Ycoords_natAdd j]

theorem append_add_append {p q : ℕ} (u u' : Fin p → ℝ) (v v' : Fin q → ℝ) :
    (Fin.append u v + Fin.append u' v' : Fin (p + q) → ℝ) = Fin.append (u + u') (v + v') := by
  funext i
  induction i using Fin.addCases with
  | left i => simp
  | right j => simp

theorem norm_append_le {p q : ℕ} {u : Fin p → ℝ} {v : Fin q → ℝ} {s : ℝ} (hs : 0 ≤ s)
    (hu : ‖u‖ ≤ s) (hv : ‖v‖ ≤ s) : ‖(Fin.append u v : Fin (p + q) → ℝ)‖ ≤ s := by
  refine (pi_norm_le_iff_of_nonneg hs).2 fun i => ?_
  induction i using Fin.addCases with
  | left i =>
    rw [Fin.append_left]
    exact (norm_le_pi_norm u i).trans hu
  | right j =>
    rw [Fin.append_right]
    exact (norm_le_pi_norm v j).trans hv

/-- **G6b: the D-trick at `(a, y0)`, function form.** -/
theorem dtrick_at {p m r : ℕ} (g : Fin r → (Fin p → ℝ) × (Fin (m + 1) → ℝ) → ℝ)
    (a : Fin p → ℝ) (y0 : Fin (m + 1) → ℝ) (hg : ∀ k, AnalyticAt ℝ (g k) (a, y0)) :
    ∃ (F : Fin r → Finset (Fin (p + (m + 1)) →₀ ℕ))
      (gc : Fin r → (Fin (p + (m + 1)) →₀ ℕ) → (Fin p → ℝ) → ℝ)
      (C : Fin r → (Fin (p + (m + 1)) →₀ ℕ) → (Fin p → ℝ) × (Fin (m + 1) → ℝ) → ℝ), ∃ ρ > 0,
      (∀ k β, AnalyticAt ℝ (gc k β) a) ∧ (∀ k β, AnalyticAt ℝ (C k β) (a, y0)) ∧
      (∀ x y, ‖x - a‖ ≤ ρ → ‖y - y0‖ ≤ ρ → ∀ k,
        g k (x, y) = ∑ β ∈ F k, gc k β x * C k β (x, y)) ∧
      (∀ k (z : (Fin (p + (m + 1)) →₀ ℕ) → ℝ),
        (∀ᶠ y in 𝓝 y0, ∑ β ∈ F k, z β * C k β (a, y) = 0) → ∀ β ∈ F k, z β = 0) := by
  classical
  set Y := Ycoords p (m + 1) with hY
  obtain ⟨H, hH⟩ : ∃ H : Fin r → (Fin (p + (m + 1)) → ℝ) → ℝ, ∀ k X,
      H k X = g k (a + clmL p (m + 1) X, y0 + clmR p (m + 1) X) := ⟨_, fun _ _ => rfl⟩
  have hHA : ∀ k, AnalyticAt ℝ (H k) 0 := by
    intro k
    have hφ : AnalyticAt ℝ (fun X : Fin (p + (m + 1)) → ℝ =>
        (a + clmL p (m + 1) X, y0 + clmR p (m + 1) X)) 0 :=
      (analyticAt_const.add ((clmL p (m + 1)).analyticAt 0)).prod
        (analyticAt_const.add ((clmR p (m + 1)).analyticAt 0))
    have e : H k = g k ∘ (fun X : Fin (p + (m + 1)) → ℝ =>
        (a + clmL p (m + 1) X, y0 + clmR p (m + 1) X)) := by
      funext X
      rw [hH]
      rfl
    rw [e]
    exact (hg k).comp_of_eq hφ (by simp)
  let S : Fin r → CPS (Fin (p + (m + 1))) := fun k => ⟨ser (H k), ser_mem (H k)⟩
  choose F hFY c hexp hnorm using fun k => dtrick_normalized Y (S k)
  choose ρs hρs hρconv hρeq using fun k => ser_spec (hHA k)
  obtain ⟨w1, hw1, hc1⟩ := exists_common_weight (Finset.univ.sigma F)
    (fun kb => ((yc Y kb.2 (S kb.1) : CPS (Fin (p + (m + 1)))) : MvPowerSeries (Fin (p + (m + 1))) ℝ))
    (fun kb _ => (yc Y kb.2 (S kb.1)).2)
  obtain ⟨w2, hw2, hc2⟩ := exists_common_weight (Finset.univ.sigma F)
    (fun kb => ((c kb.1 kb.2 : CPS (Fin (p + (m + 1)))) : MvPowerSeries (Fin (p + (m + 1))) ℝ))
    (fun kb _ => (c kb.1 kb.2).2)
  obtain ⟨ε1, hε1, hε1w⟩ := exists_pos_le_w hw1
  obtain ⟨ε2, hε2, hε2w⟩ := exists_pos_le_w hw2
  obtain ⟨ρ0, hρ0, hρ0le⟩ := exists_pos_le_all ρs hρs
  set ρ := min (min ε1 ε2) ρ0 with hρ
  have hρpos : 0 < ρ := lt_min (lt_min hε1 hε2) hρ0
  have hρ1 : ρ ≤ ε1 := (min_le_left _ _).trans (min_le_left _ _)
  have hρ2 : ρ ≤ ε2 := (min_le_left _ _).trans (min_le_right _ _)
  have hρ3 : ∀ k, ρ ≤ ρs k := fun k => (min_le_right _ _).trans (hρ0le k)
  have hC1 : ∀ k, ∀ β ∈ F k, Conv (fun _ => ρ)
      ((yc Y β (S k) : CPS (Fin (p + (m + 1)))) : MvPowerSeries (Fin (p + (m + 1))) ℝ) :=
    fun k β hβ => Conv.mono (fun _ => hρpos.le) (fun i => hρ1.trans (hε1w i))
      (hc1 ⟨k, β⟩ (Finset.mem_sigma.2 ⟨Finset.mem_univ _, hβ⟩))
  have hC2 : ∀ k, ∀ β ∈ F k, Conv (fun _ => ρ)
      ((c k β : CPS (Fin (p + (m + 1)))) : MvPowerSeries (Fin (p + (m + 1))) ℝ) :=
    fun k β hβ => Conv.mono (fun _ => hρpos.le) (fun i => hρ2.trans (hε2w i))
      (hc2 ⟨k, β⟩ (Finset.mem_sigma.2 ⟨Finset.mem_univ _, hβ⟩))
  have hφ1 : AnalyticAt ℝ (fun x : Fin p → ℝ =>
      (Fin.append (x - a) (0 : Fin (m + 1) → ℝ) : Fin (p + (m + 1)) → ℝ)) a := by
    have h1 := analyticAt_append_sub (m := m + 1) a (a, 0)
    have h2 : AnalyticAt ℝ (fun x : Fin p → ℝ => (x, (0 : Fin (m + 1) → ℝ))) a :=
      analyticAt_id.prod analyticAt_const
    exact h1.comp_of_eq h2 rfl
  have hφ2 : AnalyticAt ℝ (fun q : (Fin p → ℝ) × (Fin (m + 1) → ℝ) =>
      (Fin.append (q.1 - a) (q.2 - y0) : Fin (p + (m + 1)) → ℝ)) (a, y0) := by
    have h1 := analyticAt_append_sub (m := m + 1) a (a, y0 - y0)
    have h2 : AnalyticAt ℝ (fun q : (Fin p → ℝ) × (Fin (m + 1) → ℝ) => (q.1, q.2 - y0)) (a, y0) :=
      analyticAt_fst.prod (analyticAt_snd.sub analyticAt_const)
    exact h1.comp_of_eq h2 rfl
  have h00 : (Fin.append (a - a) (0 : Fin (m + 1) → ℝ) : Fin (p + (m + 1)) → ℝ) = 0 := by
    rw [sub_self]
    funext i
    induction i using Fin.addCases with
    | left i => simp
    | right j => simp
  have h00' : (Fin.append (a - a) (y0 - y0) : Fin (p + (m + 1)) → ℝ) = 0 := by
    simp only [sub_self]
    funext i
    induction i using Fin.addCases with
    | left i => simp
    | right j => simp
  refine ⟨F, fun k β x => ev ((yc Y β (S k) : CPS (Fin (p + (m + 1)))) :
      MvPowerSeries (Fin (p + (m + 1))) ℝ) (Fin.append (x - a) 0),
    fun k β q => ev ((c k β : CPS (Fin (p + (m + 1)))) : MvPowerSeries (Fin (p + (m + 1))) ℝ)
      (Fin.append (q.1 - a) (q.2 - y0)), ρ, hρpos, ?_, ?_, ?_, ?_⟩
  · intro k β
    exact (analyticAt_ev_CPS (yc Y β (S k)).2).comp_of_eq hφ1 h00
  · intro k β
    exact (analyticAt_ev_CPS (c k β).2).comp_of_eq hφ2 h00'
  · intro x y hx hy k
    have hX : ‖(Fin.append (x - a) (y - y0) : Fin (p + (m + 1)) → ℝ)‖ ≤ ρ :=
      norm_append_le hρpos.le hx hy
    have e1 : g k (x, y) = H k (Fin.append (x - a) (y - y0)) := by
      rw [hH, clmL_append, clmR_append]
      simp
    have e2 : H k (Fin.append (x - a) (y - y0)) =
        ev (ser (H k)) (Fin.append (x - a) (y - y0)) := hρeq k _ (hX.trans (hρ3 k))
    have e3 : (Fin.append (x - a) 0 + yproj Y (Fin.append 0 (y - y0)) : Fin (p + (m + 1)) → ℝ) =
        Fin.append (x - a) (y - y0) := by
      rw [hY, yproj_append, append_add_append, add_zero, zero_add]
    have hp : ∀ i, |(Fin.append (x - a) 0 + yproj Y (Fin.append 0 (y - y0)) :
        Fin (p + (m + 1)) → ℝ) i| ≤ (fun _ => ρ) i := by
      intro i
      rw [e3, ← Real.norm_eq_abs]
      exact (norm_le_pi_norm _ i).trans hX
    have hv := dtrick_value (S k) (c k) (hexp k) (w := fun _ => ρ) (fun _ => hρpos)
      (fun β hβ => ⟨hC1 k β hβ, hC2 k β hβ⟩) (Fin.append (x - a) 0) (Fin.append 0 (y - y0)) hp
    rw [e3] at hv
    rw [e1, e2]
    exact hv
  · intro k z hz β hβ
    have hn : ∀ β ∈ F k, ∀ β' ∈ F k, yCoeff Y β'
        ((c k β : CPS (Fin (p + (m + 1)))) : MvPowerSeries (Fin (p + (m + 1))) ℝ) =
          if β' = β then 1 else 0 := by
      intro β hβ β' hβ'
      have := congrArg (fun s : CPS (Fin (p + (m + 1))) => (s : MvPowerSeries (Fin (p + (m + 1))) ℝ))
        (hnorm k β hβ β' hβ')
      simp only [coe_yc] at this
      rw [this]
      split_ifs <;> simp
    have ht : Tendsto (fun u : Fin (p + (m + 1)) → ℝ => y0 + clmR p (m + 1) u) (𝓝 0) (𝓝 y0) := by
      have h1 : Tendsto (fun u : Fin (p + (m + 1)) → ℝ => clmR p (m + 1) u) (𝓝 0) (𝓝 0) := by
        simpa using (clmR p (m + 1)).continuous.tendsto (0 : Fin (p + (m + 1)) → ℝ)
      simpa using (tendsto_const_nhds (x := y0)).add h1
    have h0 : ∀ᶠ u in 𝓝 (0 : Fin (p + (m + 1)) → ℝ), ∑ β ∈ F k, z β *
        ev ((c k β : CPS (Fin (p + (m + 1)))) : MvPowerSeries (Fin (p + (m + 1))) ℝ)
          (0 + yproj Y u) = 0 := by
      filter_upwards [ht.eventually hz] with u hu
      have e : (0 + yproj Y u : Fin (p + (m + 1)) → ℝ) =
          Fin.append (a - a) (y0 + clmR p (m + 1) u - y0) := by
        have hu' : u = Fin.append (clmL p (m + 1) u) (clmR p (m + 1) u) :=
          Fin.append_castAdd_natAdd.symm
        rw [zero_add, hY]
        conv_lhs => rw [hu']
        rw [yproj_append, sub_self, add_sub_cancel_left]
      rw [e]
      exact hu
    exact normalized_nondeg (hFY k) hn (w := fun _ => ρ) (fun _ => hρpos) (hC2 k)
      (x := 0) (fun _ _ => rfl) (fun _ => by simp [hρpos.le]) z h0 β hβ

end DTat

end SubanalyticLib


/-! SubanalyticLib G6c-1 (route G): the algebra of the D-trick pieces: a dominant coefficient
exists unless all vanish, the expansion factors through `Dfn`, and the `z`-parameter set `Zc J`
(cube with some coordinates fixed to `1`) is compact. -/

namespace SubanalyticLib

section Pieces

open Filter Topology

set_option autoImplicit false

theorem Dfn_self {v : ℝ} (hv : v ≠ 0) : Dfn v v = 1 := by
  rw [Dfn_eq le_rfl hv, div_self hv]

/-- either all values vanish on `F`, or one of them dominates and is nonzero. -/
theorem exists_dominant {ι : Type*} (F : Finset ι) (v : ι → ℝ) :
    (∀ β ∈ F, v β = 0) ∨ ∃ i ∈ F, v i ≠ 0 ∧ ∀ β ∈ F, |v β| ≤ |v i| := by
  by_cases h : ∀ β ∈ F, v β = 0
  · exact Or.inl h
  · right
    push_neg at h
    obtain ⟨β0, hβ0, hβ0v⟩ := h
    obtain ⟨i, hi, himax⟩ := F.exists_max_image (fun β => |v β|) ⟨β0, hβ0⟩
    refine ⟨i, hi, ?_, himax⟩
    intro hvi
    have h1 := himax β0 hβ0
    rw [hvi, abs_zero] at h1
    exact hβ0v (abs_nonpos_iff.1 h1)

/-- the expansion factors through the dominant coefficient. -/
theorem sum_eq_mul_Dfn {ι : Type*} {F : Finset ι} {v : ι → ℝ} {i : ι} (hv : v i ≠ 0)
    (hdom : ∀ β ∈ F, |v β| ≤ |v i|) (C : ι → ℝ) :
    ∑ β ∈ F, v β * C β = v i * ∑ β ∈ F, Dfn (v β) (v i) * C β := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [← mul_assoc, mul_Dfn (hdom β hβ) hv]

theorem sign_sum_eq_Dfn {ι : Type*} {F : Finset ι} {v : ι → ℝ} {i : ι} (hv : v i ≠ 0)
    (hdom : ∀ β ∈ F, |v β| ≤ |v i|) (C : ι → ℝ) :
    SignType.sign (∑ β ∈ F, v β * C β) =
      SignType.sign (v i) * SignType.sign (∑ β ∈ F, Dfn (v β) (v i) * C β) := by
  rw [sum_eq_mul_Dfn hv hdom C, sign_mul]

/-- the `z`-parameter set: the unit cube with the coordinates in `J` fixed to `1`. -/
def Zc {Z : ℕ} (J : Set (Fin Z)) : Set (Fin Z → ℝ) := {z | (∀ j, |z j| ≤ 1) ∧ ∀ j ∈ J, z j = 1}

theorem isCompact_Zc {Z : ℕ} (J : Set (Fin Z)) : IsCompact (Zc J) := by
  have hcube : IsCompact (Set.pi Set.univ fun _ : Fin Z => Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hcl : IsClosed {z : Fin Z → ℝ | ∀ j ∈ J, z j = 1} := by
    have e : {z : Fin Z → ℝ | ∀ j ∈ J, z j = 1} = ⋂ j ∈ J, {z | z j = 1} := by
      ext z
      simp
    rw [e]
    exact isClosed_biInter fun j _ => isClosed_eq (continuous_apply j) continuous_const
  have e : Zc J = (Set.pi Set.univ fun _ : Fin Z => Set.Icc (-1 : ℝ) 1) ∩
      {z : Fin Z → ℝ | ∀ j ∈ J, z j = 1} := by
    ext z
    simp only [Zc, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Icc, abs_le]
  rw [e]
  exact hcube.inter_right hcl

end Pieces

end SubanalyticLib

/-! SubanalyticLib G6c (route G): `(★_m) → (★_{m+1})`, hence `(★_m)` for every `m`.
D-trick pieces (selectors `s`), the normalized functions `bigG` in the extra variables `z`,
nondegeneracy on `Zc`, compactness in `z`, and substitution `z = zf s x`. -/

namespace SubanalyticLib

section Star

open Filter Topology

set_option autoImplicit false

theorem exists_pos_le_finset {α : Type*} (t : Finset α) (f : α → ℝ) (hf : ∀ i ∈ t, 0 < f i) :
    ∃ δ > 0, ∀ i ∈ t, δ ≤ f i := by
  classical
  revert hf
  refine Finset.induction_on t ?_ ?_
  · intro _
    exact ⟨1, one_pos, by simp⟩
  · intro i t _ ih hf
    obtain ⟨δ, hδ, h⟩ := ih fun j hj => hf j (Finset.mem_insert_of_mem hj)
    refine ⟨min δ (f i), lt_min hδ (hf i (Finset.mem_insert_self i t)), fun j hj => ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h j hj)

/-- selectors: for each `k`, `none` (all coefficients vanish) or a dominant index and its sign. -/
abbrev Sel {r : ℕ} {ι : Type*} (F : Fin r → Finset ι) : Type _ :=
  (k : Fin r) → Option ({β // β ∈ F k} × SignType)

def selCond {p : ℕ} {ι : Type*} {F : Finset ι} (gt : ι → (Fin p → ℝ) → ℝ) :
    Option ({β // β ∈ F} × SignType) → Set (Fin p → ℝ)
  | none => {x | ∀ β ∈ F, gt β x = 0}
  | some iσ => {x | SignType.sign (gt iσ.1.1 x) = iσ.2 ∧ gt iσ.1.1 x ≠ 0 ∧
      ∀ β ∈ F, |gt β x| ≤ |gt iσ.1.1 x|}

def pieceB {p r : ℕ} {ι : Type*} (F : Fin r → Finset ι) (gt : Fin r → ι → (Fin p → ℝ) → ℝ)
    (s : Sel F) : Set (Fin p → ℝ) :=
  ⋂ k, selCond (F := F k) (gt k) (s k)

theorem isSA_abs_le {p : ℕ} {f h : (Fin p → ℝ) → ℝ} (hf : InLam p f) (hh : InLam p h) :
    IsSA (Lam p) {x | |f x| ≤ |h x|} := by
  have hm : h * h - f * f ∈ Lam p :=
    (Lam p).sub_mem ((Lam p).mul_mem hh hh) ((Lam p).mul_mem hf hf)
  have e : {x | |f x| ≤ |h x|} = {x | (h * h - f * f) x < 0}ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Pi.sub_apply, Pi.mul_apply, not_lt]
    rw [sub_nonneg, ← pow_two (f x), ← pow_two (h x)]
    exact sq_le_sq.symm
  rw [e]
  exact (IsSA.neg hm).compl

theorem isSA_selCond {p : ℕ} {ι : Type*} {F : Finset ι} {gt : ι → (Fin p → ℝ) → ℝ}
    (hgt : ∀ β, InLam p (gt β)) : ∀ o, IsSA (Lam p) (selCond (F := F) gt o) := by
  rintro (_ | ⟨i, σ⟩)
  · have e : selCond (F := F) gt none = ⋂ β ∈ F, {x | gt β x = 0} := by
      ext x
      simp [selCond]
    rw [e]
    exact IsSA.biInter F fun β _ => IsSA.zero (hgt β)
  · have e : selCond (F := F) gt (some (i, σ)) = {x | SignType.sign (gt i.1 x) = σ} ∩
        ({x | gt i.1 x ≠ 0} ∩ ⋂ β ∈ F, {x | |gt β x| ≤ |gt i.1 x|}) := by
      ext x
      simp [selCond]
    rw [e]
    exact IsSA.inter (IsSA.sign (hgt i.1) σ)
      (IsSA.inter (IsSA.ne (hgt i.1)) (IsSA.biInter F fun β _ => isSA_abs_le (hgt β) (hgt i.1)))

theorem isSA_pieceB {p r : ℕ} {ι : Type*} (F : Fin r → Finset ι)
    (gt : Fin r → ι → (Fin p → ℝ) → ℝ) (hgt : ∀ k β, InLam p (gt k β)) (s : Sel F) :
    IsSA (Lam p) (pieceB F gt s) :=
  IsSA.iInter_fintype fun k => isSA_selCond (hgt k) (s k)

theorem pieceB_cover {p r : ℕ} {ι : Type*} (F : Fin r → Finset ι)
    (gt : Fin r → ι → (Fin p → ℝ) → ℝ) (x : Fin p → ℝ) : ∃ s : Sel F, x ∈ pieceB F gt s := by
  have h : ∀ k, ∃ o, x ∈ selCond (F := F k) (gt k) o := by
    intro k
    rcases exists_dominant (F k) (fun β => gt k β x) with h | ⟨i, hi, hne, hdom⟩
    · exact ⟨none, h⟩
    · exact ⟨some (⟨i, hi⟩, SignType.sign (gt k i x)), rfl, hne, hdom⟩
  choose s hs using h
  exact ⟨s, Set.mem_iInter.2 hs⟩

/-- the normalized functions on the piece `s`, in the variables `(x, z, y)`. -/
noncomputable def bigG {p r Z m : ℕ} {ι : Type*} (F : Fin r → Finset ι) (e : (Σ k, {β // β ∈ F k}) ≃ Fin Z)
    (C : Fin r → ι → (Fin p → ℝ) × (Fin m → ℝ) → ℝ) (s : Sel F) (k : Fin r)
    (q : (Fin (p + Z) → ℝ) × (Fin m → ℝ)) : ℝ :=
  Option.elim (s k) 1 fun _ =>
    ∑ β ∈ (F k).attach, q.1 (Fin.natAdd p (e ⟨k, β⟩)) * C k β.1 (clmL p Z q.1, q.2)

def selN {r : ℕ} {ι : Type*} {F : Fin r → Finset ι} (s : Sel F) (N : Set (Fin r → SignType)) :
    Set (Fin r → SignType) :=
  {τ | (fun k => Option.elim (s k) 0 fun iσ => iσ.2 * τ k) ∈ N}

def selJ {r Z : ℕ} {ι : Type*} {F : Fin r → Finset ι} (e : (Σ k, {β // β ∈ F k}) ≃ Fin Z)
    (s : Sel F) : Set (Fin Z) :=
  {j | ∃ k iσ, s k = some iσ ∧ e ⟨k, iσ.1⟩ = j}

/-- the substituted `z`-coordinates on the piece `s`. -/
noncomputable def zf {p r Z : ℕ} {ι : Type*} (F : Fin r → Finset ι) (e : (Σ k, {β // β ∈ F k}) ≃ Fin Z)
    (gt : Fin r → ι → (Fin p → ℝ) → ℝ) (s : Sel F) (j : Fin Z) (x : Fin p → ℝ) : ℝ :=
  Option.elim (s (e.symm j).1) 0 fun iσ =>
    Dfn (gt (e.symm j).1 (e.symm j).2.1 x) (gt (e.symm j).1 iσ.1.1 x)

theorem zf_e {p r Z : ℕ} {ι : Type*} (F : Fin r → Finset ι) (e : (Σ k, {β // β ∈ F k}) ≃ Fin Z)
    (gt : Fin r → ι → (Fin p → ℝ) → ℝ) (s : Sel F) (k : Fin r) (β : {β // β ∈ F k})
    (x : Fin p → ℝ) :
    zf F e gt s (e ⟨k, β⟩) x = Option.elim (s k) 0 fun iσ => Dfn (gt k β.1 x) (gt k iσ.1.1 x) := by
  unfold zf
  rw [Equiv.symm_apply_apply]

theorem inLam_zf {p r Z : ℕ} {ι : Type*} (F : Fin r → Finset ι)
    (e : (Σ k, {β // β ∈ F k}) ≃ Fin Z) (gt : Fin r → ι → (Fin p → ℝ) → ℝ) (s : Sel F)
    (hgt : ∀ k β, InLam p (gt k β)) (j : Fin Z) : InLam p (zf F e gt s j) := by
  obtain ⟨⟨k, β⟩, rfl⟩ := e.surjective j
  have h : zf F e gt s (e ⟨k, β⟩) = fun x => Option.elim (s k) 0 fun iσ =>
      Dfn (gt k β.1 x) (gt k iσ.1.1 x) := funext fun x => zf_e F e gt s k β x
  rw [h]
  rcases s k with _ | iσ
  · exact InLam.const 0
  · exact InLam.dfn (hgt k β.1) (hgt k iσ.1.1)

theorem zf_mem_Zc {p r Z : ℕ} {ι : Type*} (F : Fin r → Finset ι)
    (e : (Σ k, {β // β ∈ F k}) ≃ Fin Z) (gt : Fin r → ι → (Fin p → ℝ) → ℝ) (s : Sel F)
    {x : Fin p → ℝ} (hx : x ∈ pieceB F gt s) :
    (fun j => zf F e gt s j x) ∈ Zc (selJ e s) := by
  refine ⟨fun j => ?_, fun j hj => ?_⟩
  · obtain ⟨⟨k, β⟩, rfl⟩ := e.surjective j
    show |zf F e gt s (e ⟨k, β⟩) x| ≤ 1
    rw [zf_e]
    rcases s k with _ | iσ
    · simp
    · exact abs_Dfn_le _ _
  · obtain ⟨k, iσ, hs, rfl⟩ := hj
    show zf F e gt s (e ⟨k, iσ.1⟩) x = 1
    have hk : x ∈ selCond (F := F k) (gt k) (s k) := Set.mem_iInter.1 hx k
    rw [hs] at hk
    rw [zf_e, hs]
    exact Dfn_self hk.2.1

theorem code_iff {p r Z m : ℕ} {ι : Type*} (F : Fin r → Finset ι)
    (e : (Σ k, {β // β ∈ F k}) ≃ Fin Z) (gt : Fin r → ι → (Fin p → ℝ) → ℝ)
    (C : Fin r → ι → (Fin p → ℝ) × (Fin m → ℝ) → ℝ)
    (g : Fin r → (Fin p → ℝ) × (Fin m → ℝ) → ℝ) (N : Set (Fin r → SignType)) (s : Sel F)
    {x : Fin p → ℝ} (hx : x ∈ pieceB F gt s) {y : Fin m → ℝ}
    (hexp : ∀ k, g k (x, y) = ∑ β ∈ F k, gt k β x * C k β (x, y)) :
    codeIn g N x y ↔
      codeIn (bigG F e C s) (selN s N) (Fin.append x fun j => zf F e gt s j x) y := by
  have key : ∀ k, SignType.sign (g k (x, y)) = Option.elim (s k) 0 fun iσ =>
      iσ.2 * SignType.sign (bigG F e C s k (Fin.append x (fun j => zf F e gt s j x), y)) := by
    intro k
    have hk : x ∈ selCond (F := F k) (gt k) (s k) := Set.mem_iInter.1 hx k
    rw [hexp k]
    rcases hs : s k with _ | ⟨i, σ⟩
    · rw [hs] at hk
      have hk' : ∀ β ∈ F k, gt k β x = 0 := hk
      simp only [Option.elim]
      rw [Finset.sum_eq_zero fun β hβ => by rw [hk' β hβ, zero_mul], sign_zero]
    · rw [hs] at hk
      obtain ⟨hsg, hne, hdom⟩ := hk
      simp only [Option.elim, bigG, hs]
      have hsd := sign_sum_eq_Dfn (v := fun β => gt k β x) hne hdom (fun β => C k β (x, y))
      simp only at hsd
      rw [hsd, hsg]
      congr 2
      refine (Finset.sum_attach (F k) _).symm.trans (Finset.sum_congr rfl fun β _ => ?_)
      rw [Fin.append_right, zf_e, hs, clmL_append]
      rfl
  unfold codeIn selN
  simp only [Set.mem_setOf_eq]
  rw [show (fun k => SignType.sign (g k (x, y))) = _ from funext key]

theorem bigG_nondeg {p r Z m : ℕ} {ι : Type*} (F : Fin r → Finset ι)
    (e : (Σ k, {β // β ∈ F k}) ≃ Fin Z) (C : Fin r → ι → (Fin p → ℝ) × (Fin m → ℝ) → ℝ)
    (s : Sel F) (a : Fin p → ℝ) (y0 : Fin m → ℝ)
    (hnd : ∀ k (z : ι → ℝ), (∀ᶠ y in 𝓝 y0, ∑ β ∈ F k, z β * C k β (a, y) = 0) →
      ∀ β ∈ F k, z β = 0)
    {z0 : Fin Z → ℝ} (hz0 : z0 ∈ Zc (selJ e s)) (k : Fin r) :
    ¬ ∀ᶠ y in 𝓝 y0, bigG F e C s k (Fin.append a z0, y) = 0 := by
  classical
  intro h
  rcases hs : s k with _ | ⟨i, σ⟩
  · obtain ⟨y, hy⟩ := h.exists
    simp only [bigG, hs, Option.elim] at hy
    exact one_ne_zero hy
  · obtain ⟨z, hz⟩ : ∃ z : ι → ℝ, ∀ β (hβ : β ∈ F k), z β = z0 (e ⟨k, ⟨β, hβ⟩⟩) :=
      ⟨fun β => if hβ : β ∈ F k then z0 (e ⟨k, ⟨β, hβ⟩⟩) else 0, fun β hβ => dif_pos hβ⟩
    have hev : ∀ᶠ y in 𝓝 y0, ∑ β ∈ F k, z β * C k β (a, y) = 0 := by
      refine h.mono fun y hy => ?_
      simp only [bigG, hs, Option.elim] at hy
      rw [← hy]
      refine (Finset.sum_attach (F k) _).symm.trans (Finset.sum_congr rfl fun β _ => ?_)
      rw [hz β.1 β.2, Fin.append_right, clmL_append]
    have h2 := hnd k z hev i.1 i.2
    rw [hz i.1 i.2] at h2
    have h3 : z0 (e ⟨k, i⟩) = 0 := h2
    have h1 : z0 (e ⟨k, i⟩) = 1 := hz0.2 _ ⟨k, (i, σ), hs, rfl⟩
    rw [h1] at h3
    exact one_ne_zero h3

theorem bigG_analytic {p r Z m : ℕ} {ι : Type*} (F : Fin r → Finset ι)
    (e : (Σ k, {β // β ∈ F k}) ≃ Fin Z) (C : Fin r → ι → (Fin p → ℝ) × (Fin m → ℝ) → ℝ)
    (s : Sel F) (a : Fin p → ℝ) (y0 : Fin m → ℝ) (hCA : ∀ k β, AnalyticAt ℝ (C k β) (a, y0))
    (z0 : Fin Z → ℝ) (k : Fin r) :
    AnalyticAt ℝ (bigG F e C s k) (Fin.append a z0, y0) := by
  rcases hs : s k with _ | ⟨i, σ⟩
  · have h : bigG F e C s k = fun _ => 1 := by
      funext q
      simp only [bigG, hs, Option.elim]
    rw [h]
    exact analyticAt_const
  · have h : bigG F e C s k = fun q => ∑ β ∈ (F k).attach,
        q.1 (Fin.natAdd p (e ⟨k, β⟩)) * C k β.1 (clmL p Z q.1, q.2) := by
      funext q
      simp only [bigG, hs, Option.elim]
    rw [h]
    apply Finset.analyticAt_fun_sum
    intro β _
    refine AnalyticAt.mul ?_ ?_
    · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (p + Z) => ℝ)
        (Fin.natAdd p (e ⟨k, β⟩))).comp
        (ContinuousLinearMap.fst ℝ (Fin (p + Z) → ℝ) (Fin m → ℝ))).analyticAt _
    · have hφ : AnalyticAt ℝ (fun q : (Fin (p + Z) → ℝ) × (Fin m → ℝ) => (clmL p Z q.1, q.2))
          (Fin.append a z0, y0) :=
        (((clmL p Z).comp (ContinuousLinearMap.fst ℝ (Fin (p + Z) → ℝ) (Fin m → ℝ))).analyticAt
          _).prod ((ContinuousLinearMap.snd ℝ (Fin (p + Z) → ℝ) (Fin m → ℝ)).analyticAt _)
      exact (hCA k β.1).comp_of_eq hφ (by simp [clmL_append])

/-- **G6c core**: at `(a, y0)`, projections over small boxes are locally Λ at `a`. -/
theorem star_core {m : ℕ} (hS : StarM m) {p r : ℕ}
    (g : Fin r → (Fin p → ℝ) × (Fin (m + 1) → ℝ) → ℝ) (a : Fin p → ℝ) (y0 : Fin (m + 1) → ℝ)
    (hg : ∀ k, AnalyticAt ℝ (g k) (a, y0)) (N : Set (Fin r → SignType)) :
    ∃ δ > 0, ∀ lo' hi' : Fin (m + 1) → ℝ, Set.Icc lo' hi' ⊆ Metric.closedBall y0 δ →
      LocLam p (projBox (codeIn g N) (Set.Icc lo' hi')) {a} := by
  classical
  obtain ⟨F, gc, C, ρ, hρ, hgcA, hCA, hexp, hnd⟩ := dtrick_at g a y0 hg
  choose gt hgt hgteq using fun k β => exists_inLam_of_analyticAt (hgcA k β)
  have hev : ∀ᶠ x in 𝓝 a, ∀ k, ∀ β ∈ F k, gt k β x = gc k β x :=
    Filter.eventually_all.2 fun k => (Filter.eventually_all_finset (F k)).2 fun β _ => hgteq k β
  obtain ⟨η0, hη0, hη0x⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨Z, ⟨e⟩⟩ : ∃ Z, Nonempty ((Σ k, {β // β ∈ F k}) ≃ Fin Z) :=
    ⟨_, ⟨Fintype.equivFin _⟩⟩
  have hne : ∀ s : Sel F, ∀ z0 ∈ Zc (selJ e s), ∃ δ > 0, ∃ r' > 0,
      ∀ (N' : Set (Fin r → SignType)) (lo' hi' : Fin (m + 1) → ℝ),
        Set.Icc lo' hi' ⊆ Metric.closedBall y0 δ →
          LocLam (p + Z) (projBox (codeIn (bigG F e C s) N') (Set.Icc lo' hi'))
            (Metric.ball (Fin.append a z0) r') :=
    fun s z0 hz0 => ne_loc hS (bigG F e C s) (Fin.append a z0) y0
      (fun k => bigG_analytic F e C s a y0 hCA z0 k) (fun k => bigG_nondeg F e C s a y0 hnd hz0 k)
  choose! δf hδf rf hrf hloc using hne
  have hc : Continuous fun z : Fin Z → ℝ => (Fin.append a z : Fin (p + Z) → ℝ) :=
    (continuous_append_pair p Z).comp (continuous_const.prodMk continuous_id)
  have hcov : ∀ s : Sel F, ∃ t : Finset (Fin Z → ℝ), (∀ z ∈ t, z ∈ Zc (selJ e s)) ∧
      Zc (selJ e s) ⊆ ⋃ z0 ∈ t, (fun z : Fin Z → ℝ => (Fin.append a z : Fin (p + Z) → ℝ)) ⁻¹'
        Metric.ball (Fin.append a z0) (rf s z0) := by
    intro s
    refine (isCompact_Zc (selJ e s)).elim_nhds_subcover _ fun z0 hz0 => ?_
    exact hc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (hrf s z0 hz0))
  choose t ht htcov using hcov
  have hδs : ∀ s : Sel F, ∃ δ > 0, ∀ z0 ∈ t s, δ ≤ δf s z0 :=
    fun s => exists_pos_le_finset (t s) (δf s) fun z0 hz0 => hδf s z0 (ht s z0 hz0)
  choose δs hδs0 hδsle using hδs
  obtain ⟨δ1, hδ1, hδ1le⟩ :=
    exists_pos_le_finset (Finset.univ : Finset (Sel F)) δs fun s _ => hδs0 s
  refine ⟨min ρ δ1, lt_min hρ hδ1, fun lo' hi' hbox => ?_⟩
  have hA : ∀ s : Sel F, LocLam (p + Z)
      (projBox (codeIn (bigG F e C s) (selN s N)) (Set.Icc lo' hi'))
      (⋃ z0 ∈ t s, Metric.ball (Fin.append a z0) (rf s z0)) := by
    intro s w hw
    simp only [Set.mem_iUnion] at hw
    obtain ⟨z0, hz0t, hw⟩ := hw
    refine hloc s z0 (ht s z0 hz0t) (selN s N) lo' hi'
      (hbox.trans (Metric.closedBall_subset_closedBall ?_)) w hw
    exact (min_le_right _ _).trans ((hδ1le s (Finset.mem_univ s)).trans (hδsle s z0 hz0t))
  have hsub : ∀ s : Sel F, ∃ η > 0, ∃ T', IsSA (Lam p) T' ∧ ∀ x : Fin p → ℝ, ‖x - a‖ < η →
      (fun j => zf F e gt s j x) ∈ Zc (selJ e s) →
      ((Fin.append x (fun j => zf F e gt s j x) : Fin (p + Z) → ℝ) ∈
        projBox (codeIn (bigG F e C s) (selN s N)) (Set.Icc lo' hi') ↔ x ∈ T') := by
    intro s
    refine locLam_subst (hA s) (isCompact_Zc (selJ e s)) a (fun z hz => ?_) (zf F e gt s)
      (inLam_zf F e gt s hgt)
    have := htcov s hz
    simp only [Set.mem_iUnion, Set.mem_preimage] at this ⊢
    exact this
  choose η hη T' hT' hiff using hsub
  obtain ⟨η1, hη1, hη1le⟩ :=
    exists_pos_le_finset (Finset.univ : Finset (Sel F)) η fun s _ => hη s
  have hη2 : 0 < min η0 (min ρ η1) := lt_min hη0 (lt_min hρ hη1)
  have hE : ∀ x : Fin p → ℝ, ‖x - a‖ < min η0 (min ρ η1) → ∀ y ∈ Set.Icc lo' hi', ∀ k,
      g k (x, y) = ∑ β ∈ F k, gt k β x * C k β (x, y) := by
    intro x hx y hy k
    have hxe := hη0x (show dist x a < η0 by
      rw [dist_eq_norm]; exact hx.trans_le (min_le_left _ _))
    have hxρ : ‖x - a‖ ≤ ρ := hx.le.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hyρ : ‖y - y0‖ ≤ ρ := by
      have := hbox hy
      rw [Metric.mem_closedBall, dist_eq_norm] at this
      exact this.trans (min_le_left _ _)
    rw [hexp x y hxρ hyρ k]
    exact Finset.sum_congr rfl fun β hβ => by rw [hxe k β hβ]
  have hP : ∀ x : Fin p → ℝ, ‖x - a‖ < min η0 (min ρ η1) → ∀ s, x ∈ pieceB F gt s →
      (x ∈ projBox (codeIn g N) (Set.Icc lo' hi') ↔ x ∈ T' s) := by
    intro x hx s hxs
    have hxη : ‖x - a‖ < η s :=
      hx.trans_le (((min_le_right _ _).trans (min_le_right _ _)).trans
        (hη1le s (Finset.mem_univ s)))
    rw [← hiff s x hxη (zf_mem_Zc F e gt s hxs)]
    simp only [projBox, Set.mem_setOf_eq]
    exact exists_congr fun y => and_congr_right fun hy =>
      code_iff F e gt C g N s hxs (hE x hx y hy)
  intro a' ha'
  rw [Set.mem_singleton_iff.1 ha']
  refine ⟨Metric.ball a (min η0 (min ρ η1)), Metric.ball_mem_nhds _ hη2,
    ⋃ s, pieceB F gt s ∩ T' s,
    IsSA.iUnion_fintype fun s => IsSA.inter (isSA_pieceB F gt hgt s) (hT' s), ?_⟩
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨hxA, hxb⟩
    have hxn : ‖x - a‖ < min η0 (min ρ η1) := by rw [← dist_eq_norm]; exact hxb
    obtain ⟨s, hs⟩ := pieceB_cover F gt x
    exact ⟨⟨s, hs, (hP x hxn s hs).1 hxA⟩, hxb⟩
  · rintro ⟨⟨s, hs, hT⟩, hxb⟩
    have hxn : ‖x - a‖ < min η0 (min ρ η1) := by rw [← dist_eq_norm]; exact hxb
    exact ⟨(hP x hxn s hs).2 hT, hxb⟩

/-- **G6c**: `(★_m) → (★_{m+1})`. -/
theorem star_succ {m : ℕ} (hS : StarM m) : StarM (m + 1) := by
  intro p r g a lo hi N hg
  refine glue_boxes (codeIn g N) a lo hi fun y0 hy0 => ?_
  obtain ⟨δ, hδ, h⟩ := star_core hS g a y0 (fun k => hg k y0 hy0) N
  exact ⟨δ, hδ, fun lo' hi' hsub => h lo' hi' (hsub.trans Set.inter_subset_right)⟩

/-- **(★_m) for all `m`.** -/
theorem starM_all : ∀ m, StarM m
  | 0 => star_zero
  | m + 1 => star_succ (starM_all m)

end Star

end SubanalyticLib

/-! SubanalyticLib G7a (route G): **Gabrielov's complement theorem**. A subanalytic set is locally Λ
(`(★_m)` for all `m` plus compactness over the bounded fibre), so its complement is subanalytic. -/

namespace SubanalyticLib

section Gab

open Filter Topology

set_option autoImplicit false

theorem LocLam.congr_at {p : ℕ} {A A' U : Set (Fin p → ℝ)} {a : Fin p → ℝ}
    (h : LocLam p A {a}) (hU : U ∈ 𝓝 a) (hAA : A ∩ U = A' ∩ U) : LocLam p A' {a} := by
  intro a' ha'
  have ha : a' = a := Set.mem_singleton_iff.1 ha'
  subst ha
  obtain ⟨U0, hU0, T, hT, hAT⟩ := h a' (Set.mem_singleton a')
  refine ⟨U0 ∩ U, Filter.inter_mem hU0 hU, T, hT, ?_⟩
  ext x
  constructor
  · rintro ⟨hxA', hx0, hxU⟩
    have h1 : x ∈ A ∩ U := by rw [hAA]; exact ⟨hxA', hxU⟩
    have h2 : x ∈ A ∩ U0 := ⟨h1.1, hx0⟩
    rw [hAT] at h2
    exact ⟨h2.1, hx0, hxU⟩
  · rintro ⟨hxT, hx0, hxU⟩
    have h1 : x ∈ T ∩ U0 := ⟨hxT, hx0⟩
    rw [← hAT] at h1
    have h2 : x ∈ A ∩ U := ⟨h1.1, hxU⟩
    rw [hAA] at h2
    exact ⟨h2.1, hx0, hxU⟩

/-- **G7a core**: the projection of a semianalytic set with fibres in a box is locally Λ. -/
theorem gab_core {p m : ℕ} {B : Set ((Fin p → ℝ) × (Fin m → ℝ))} (hB : IsSemianalytic B)
    (lo hi : Fin m → ℝ) (hbox : ∀ q ∈ B, q.2 ∈ Set.Icc lo hi) (x0 : Fin p → ℝ) :
    LocLam p (Prod.fst '' B) {x0} := by
  classical
  have e1 : Prod.fst '' B = projBox (fun x y => (x, y) ∈ B) (Set.Icc lo hi) := by
    ext x
    constructor
    · rintro ⟨⟨x', y⟩, hq, rfl⟩
      exact ⟨y, hbox _ hq, hq⟩
    · rintro ⟨y, -, hq⟩
      exact ⟨(x, y), hq, rfl⟩
  rw [e1]
  refine glue_boxes _ x0 lo hi fun y0 _ => ?_
  obtain ⟨V, hVo, hV0, p', q', F, G, hFG, hEq⟩ := hB (x0, y0)
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hVo _ hV0
  obtain ⟨r, ⟨e⟩⟩ : ∃ r, Nonempty ((Fin p' × Fin q') ⊕ (Fin p' × Fin q') ≃ Fin r) :=
    ⟨_, ⟨Fintype.equivFin _⟩⟩
  obtain ⟨g, hgF, hgG⟩ : ∃ g : Fin r → (Fin p → ℝ) × (Fin m → ℝ) → ℝ,
      (∀ i j, g (e (Sum.inl (i, j))) = F i j) ∧ (∀ i j, g (e (Sum.inr (i, j))) = G i j) :=
    ⟨fun k => Sum.elim (fun ij => F ij.1 ij.2) (fun ij => G ij.1 ij.2) (e.symm k),
      fun i j => by simp, fun i j => by simp⟩
  have hgA : ∀ k, AnalyticOnNhd ℝ (g k) V := by
    intro k
    obtain ⟨s, rfl⟩ := e.surjective k
    rcases s with ⟨i, j⟩ | ⟨i, j⟩
    · rw [hgF]; exact (hFG i j).1
    · rw [hgG]; exact (hFG i j).2
  set N : Set (Fin r → SignType) :=
    {τ | ∃ i, ∀ j, τ (e (Sum.inl (i, j))) = 0 ∧ τ (e (Sum.inr (i, j))) = 1} with hN
  have hcode : ∀ x y, codeIn g N x y ↔ ∃ i, ∀ j, F i j (x, y) = 0 ∧ 0 < G i j (x, y) := by
    intro x y
    simp only [codeIn, hN, Set.mem_setOf_eq, hgF, hgG, sign_eq_zero_iff, sign_eq_one_iff]
  have hmemB : ∀ q ∈ V, (q ∈ B ↔ ∃ i, ∀ j, F i j q = 0 ∧ 0 < G i j q) := by
    intro q hq
    constructor
    · intro hqB
      have h1 : q ∈ B ∩ V := ⟨hqB, hq⟩
      rw [hEq] at h1
      simpa using h1.2
    · intro h
      have h1 : q ∈ V ∩ ⋃ i, ⋂ j, {x | F i j x = 0 ∧ 0 < G i j x} := ⟨hq, by simpa using h⟩
      rw [← hEq] at h1
      exact h1.1
  have hball : ∀ x y, dist x x0 < ε / 2 → dist y y0 ≤ ε / 2 →
      ((x, y) : (Fin p → ℝ) × (Fin m → ℝ)) ∈ V := by
    intro x y hx hy
    apply hεV
    rw [Metric.mem_ball, Prod.dist_eq]
    exact max_lt (by simp only; linarith) (by simp only; linarith)
  have hx00 : dist x0 x0 < ε / 2 := by rw [dist_self]; exact half_pos hε
  refine ⟨ε / 2, half_pos hε, fun lo' hi' hsub => ?_⟩
  have hS := starM_all m p r g x0 lo' hi' N fun k y hy =>
    hgA k _ (hball x0 y hx00 (hsub hy).2)
  refine LocLam.congr_at hS (Metric.ball_mem_nhds x0 (half_pos hε)) ?_
  ext x
  simp only [Set.mem_inter_iff, projBox, Set.mem_setOf_eq, Metric.mem_ball]
  constructor
  · rintro ⟨⟨y, hy, hc⟩, hx⟩
    exact ⟨⟨y, hy, (hmemB _ (hball x y hx (hsub hy).2)).2 ((hcode x y).1 hc)⟩, hx⟩
  · rintro ⟨⟨y, hy, hq⟩, hx⟩
    exact ⟨⟨y, hy, (hcode x y).2 ((hmemB _ (hball x y hx (hsub hy).2)).1 hq)⟩, hx⟩

/-- **G7a**: subanalytic subsets of `ℝ^p` are locally Λ. -/
theorem locLam_of_sub {p : ℕ} {A : Set (Fin p → ℝ)} (hA : IsSubanalytic A) :
    LocLam p A Set.univ := by
  intro x0 _
  obtain ⟨V, hV, m, -, B, hBs, hBb, hAB⟩ := hA x0
  set E : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) := EuclideanSpace.equiv (Fin m) ℝ with hE
  set EL : EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin m → ℝ) := E.toContinuousLinearMap with hEL
  set Φ : (Fin p → ℝ) × (Fin m → ℝ) → (Fin p → ℝ) × EuclideanSpace ℝ (Fin m) :=
    fun q => (q.1, E.symm q.2) with hΦdef
  have hΦ : ∀ q, AnalyticAt ℝ Φ q := fun q =>
    analyticAt_fst.prod
      (((E.symm : (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)).analyticAt _).comp analyticAt_snd)
  obtain ⟨R, hR⟩ := hBb.exists_norm_le
  set M := ‖EL‖ * R with hM
  have hbox : ∀ q ∈ Φ ⁻¹' B, q.2 ∈ Set.Icc (fun _ => -M) (fun _ => M) := by
    intro q hq
    have h1 : ‖(Φ q).2‖ ≤ R := (norm_snd_le _).trans (hR _ hq)
    have h2 : ‖q.2‖ ≤ M := by
      have hq2 : q.2 = EL (Φ q).2 := (E.apply_symm_apply _).symm
      rw [hq2]
      exact (EL.le_opNorm _).trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have h3 := (norm_le_pi_norm q.2 j).trans h2
      rw [Real.norm_eq_abs] at h3
      linarith [neg_abs_le (q.2 j)]
    · have h3 := (norm_le_pi_norm q.2 j).trans h2
      rw [Real.norm_eq_abs] at h3
      linarith [le_abs_self (q.2 j)]
  have hfst : Prod.fst '' (Φ ⁻¹' B) = Prod.fst '' B := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨Φ q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      refine ⟨(q.1, E q.2), ?_, rfl⟩
      show (q.1, E.symm (E q.2)) ∈ B
      rw [E.symm_apply_apply]
      exact hq
  obtain ⟨U0, hU0, T, hT, hUT⟩ :=
    gab_core (semi_preimage hΦ hBs) _ _ hbox x0 x0 (Set.mem_singleton x0)
  rw [hfst] at hUT
  refine ⟨U0 ∩ V, Filter.inter_mem hU0 hV, T, hT, ?_⟩
  ext x
  constructor
  · rintro ⟨hxA, hxU, hxV⟩
    have h1 : x ∈ Prod.fst '' B := by rw [← hAB]; exact ⟨hxA, hxV⟩
    have h2 : x ∈ T ∩ U0 := by rw [← hUT]; exact ⟨h1, hxU⟩
    exact ⟨h2.1, hxU, hxV⟩
  · rintro ⟨hxT, hxU, hxV⟩
    have h2 : x ∈ Prod.fst '' B ∩ U0 := by rw [hUT]; exact ⟨hxT, hxU⟩
    have h1 : x ∈ A ∩ V := by rw [hAB]; exact h2.1
    exact ⟨h1.1, hxU, hxV⟩

theorem sub_compl_fin {p : ℕ} {A : Set (Fin p → ℝ)} (hA : IsSubanalytic A) :
    IsSubanalytic Aᶜ :=
  sub_of_locLam (locLam_of_sub hA).compl

/-- **Gabrielov's complement theorem.** -/
theorem sub_compl {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {A : Set X} (hA : IsSubanalytic A) : IsSubanalytic Aᶜ := by
  set e : X ≃L[ℝ] (Fin (Module.finrank ℝ X) → ℝ) :=
    toEuclidean.trans (EuclideanSpace.equiv (Fin (Module.finrank ℝ X)) ℝ) with he
  have h1 : IsSubanalytic (e '' A)ᶜ := sub_compl_fin (sub_image_equiv e hA)
  rw [← Set.image_compl_eq e.bijective] at h1
  have h2 := sub_image_equiv e.symm h1
  rwa [e.symm_image_image] at h2

end Gab

end SubanalyticLib

/-! SubanalyticLib G7b (route G): first-order closure with locally bounded quantifiers.
`∃ z` (projection) and `∀ z ∈ K x` over fibres that are locally bounded, via Gabrielov (`sub_compl`). -/

namespace SubanalyticLib

section FO

open Filter Topology

set_option autoImplicit false

end FO

end SubanalyticLib

end TopOpen

open NonsmoothLojasiewicz.Continuous in
theorem solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (A : Set X) (hA : IsSubanalytic A) : IsSubanalytic Aᶜ := by
  exact SubanalyticLib.sub_compl hA
