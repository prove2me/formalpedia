-- Prove2me | solution 1 for NonsmoothLojasiewicz.Convex.infDist_isSubanalyticFn
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T06:51:23.442919+00:00
-- url     : https://prove2.me/submissions/1280495b-3848-472d-a492-cd543d07930b

import Mathlib
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic
import Theorems.Thm_NonsmoothLojasiewicz_Continuous_subanalytic_compl

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

theorem isSemianalytic_iff_locForm (A : Set X) :
    IsSemianalytic A ↔ ∀ x₀ : X, ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧ LocForm V A :=
  Iff.rfl

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
    tauto

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
    ext x; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff]; tauto
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

theorem semi_of_locForm {A : Set X}
    (h : ∀ x₀ : X, ∃ V : Set X, IsOpen V ∧ x₀ ∈ V ∧ LocForm V A) : IsSemianalytic A := h

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

theorem semi_diff {A B : Set X} (hA : IsSemianalytic A) (hB : IsSemianalytic B) :
    IsSemianalytic (A \ B) :=
  semi_inter hA (semi_compl hB)

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

/-- Semianalyticity is local: it suffices to have a semianalytic set agreeing with `A` near
each point. -/
theorem semi_of_local {A : Set X}
    (h : ∀ x₀ : X, ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ ∃ A' : Set X, IsSemianalytic A' ∧
      A ∩ U = A' ∩ U) : IsSemianalytic A := by
  intro x₀
  obtain ⟨U, hU, hxU, A', hA', hEq⟩ := h x₀
  obtain ⟨V, hV, hxV, (hL : LocForm V A')⟩ := hA' x₀
  refine ⟨V ∩ U, hV.inter hU, ⟨hxV, hxU⟩, (hL.mono Set.inter_subset_left).congr ?_⟩
  calc A' ∩ (V ∩ U) = (A' ∩ U) ∩ V := by ac_rfl
    _ = (A ∩ U) ∩ V := by rw [hEq]
    _ = A ∩ (V ∩ U) := by ac_rfl

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
    ext x; simp only [Set.mem_inter_iff]; tauto
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

theorem sub_empty : IsSubanalytic (∅ : Set X) := sub_of_semi semi_empty

theorem sub_univ : IsSubanalytic (Set.univ : Set X) := sub_of_semi semi_univ

theorem sub_diff_semi {A S : Set X} (hA : IsSubanalytic A) (hS : IsSemianalytic S) :
    IsSubanalytic (A \ S) :=
  sub_inter hA (sub_of_semi (semi_compl hS))

theorem sub_inter_semi {A S : Set X} (hA : IsSubanalytic A) (hS : IsSemianalytic S) :
    IsSubanalytic (A ∩ S) :=
  sub_inter hA (sub_of_semi hS)

theorem sub_prod {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {A : Set X} {A' : Set Y} (hA : IsSubanalytic A) (hA' : IsSubanalytic A') :
    IsSubanalytic (A ×ˢ A') :=
  sub_inter (sub_preimage (fun _ => analyticAt_fst) hA) (sub_preimage (fun _ => analyticAt_snd) hA')

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


namespace SubanalyticLib
open Filter Topology
/-! CHILD INTERFACE (the two children of this reduction) -/
theorem sub_compl {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {A : Set X} (hA : NonsmoothLojasiewicz.Continuous.IsSubanalytic A) :
    NonsmoothLojasiewicz.Continuous.IsSubanalytic Aᶜ := by
  exact NonsmoothLojasiewicz.Continuous.subanalytic_compl A hA
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
end SubanalyticLib

/-! SubanalyticLib G7b (route G): first-order closure with locally bounded quantifiers.
`∃ z` (projection) and `∀ z ∈ K x` over fibres that are locally bounded, via Gabrielov (`sub_compl`). -/

namespace SubanalyticLib

section FO

open Filter Topology

set_option autoImplicit false

theorem exists_ebox_superset {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [FiniteDimensional ℝ Z] (K : Set Z) (hK : Bornology.IsBounded K) :
    ∃ R : ℝ, K ⊆ ebox 0 R := by
  obtain ⟨R, hR⟩ := hK.exists_norm_le
  set T : Z →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ Z)) :=
    (toEuclidean : Z ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ Z))).toContinuousLinearMap
    with hT
  refine ⟨‖T‖ * R + 1, fun z hz => ?_⟩
  show ‖toEuclidean (z - 0)‖ ^ 2 < (‖T‖ * R + 1) ^ 2
  have h1 : ‖toEuclidean (z - 0)‖ ≤ ‖T‖ * R := by
    rw [sub_zero]
    exact (T.le_opNorm z).trans (mul_le_mul_of_nonneg_left (hR z hz) (norm_nonneg _))
  have h0 := norm_nonneg (toEuclidean (z - 0))
  nlinarith

/-- **projection along locally bounded fibres** (`∃ z`). -/
theorem sub_proj_loc {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {A : Set (X × Z)} (hA : IsSubanalytic A)
    (hb : ∀ x0 : X, ∃ W ∈ 𝓝 x0, ∃ K : Set Z, Bornology.IsBounded K ∧
      ∀ q ∈ A, q.1 ∈ W → q.2 ∈ K) :
    IsSubanalytic (Prod.fst '' A) := by
  apply sub_of_local
  intro x0
  obtain ⟨W, hW, K, hK, hAK⟩ := hb x0
  obtain ⟨r, hr, hrW⟩ := ebox_sub x0 hW
  obtain ⟨R, hKR⟩ := exists_ebox_superset K hK
  have hsemi : IsSemianalytic (Prod.fst ⁻¹' ebox x0 r ∩ Prod.snd ⁻¹' ebox (0 : Z) R) :=
    semi_inter (semi_preimage (fun _ => analyticAt_fst) (ebox_semi x0 r))
      (semi_preimage (fun _ => analyticAt_snd) (ebox_semi 0 R))
  have hbdd : Bornology.IsBounded (A ∩ (Prod.fst ⁻¹' ebox x0 r ∩ Prod.snd ⁻¹' ebox (0 : Z) R)) :=
    ((ebox_bdd x0 r).prod (ebox_bdd (0 : Z) R)).subset fun q hq => ⟨hq.2.1, hq.2.2⟩
  refine ⟨ebox x0 r, ebox_nhds x0 hr,
    Prod.fst '' (A ∩ (Prod.fst ⁻¹' ebox x0 r ∩ Prod.snd ⁻¹' ebox (0 : Z) R)),
    sub_proj (sub_inter_semi hA hsemi) hbdd, ?_⟩
  ext x
  constructor
  · rintro ⟨⟨q, hq, rfl⟩, hx⟩
    exact ⟨⟨q, ⟨hq, hx, hKR (hAK q hq (hrW hx))⟩, rfl⟩, hx⟩
  · rintro ⟨⟨q, ⟨hq, -, -⟩, rfl⟩, hx⟩
    exact ⟨⟨q, hq, rfl⟩, hx⟩

/-- **bounded universal quantifier** (`∀ z, (x, z) ∈ K → (x, z) ∈ S`), `K` locally bounded in `z`. -/
theorem sub_forall_loc {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    {S K : Set (X × Z)} (hS : IsSubanalytic S) (hK : IsSubanalytic K)
    (hb : ∀ x0 : X, ∃ W ∈ 𝓝 x0, ∃ Kb : Set Z, Bornology.IsBounded Kb ∧
      ∀ q ∈ K, q.1 ∈ W → q.2 ∈ Kb) :
    IsSubanalytic {x : X | ∀ z, (x, z) ∈ K → (x, z) ∈ S} := by
  have e : {x : X | ∀ z, (x, z) ∈ K → (x, z) ∈ S} = (Prod.fst '' (K ∩ Sᶜ))ᶜ := by
    ext x
    constructor
    · intro hx hmem
      obtain ⟨q, ⟨hqK, hqS⟩, hq1⟩ := hmem
      apply hqS
      have hq : q = (x, q.2) := Prod.ext hq1 rfl
      rw [hq] at hqK ⊢
      exact hx _ hqK
    · intro hx z hz
      by_contra hzS
      exact hx ⟨(x, z), ⟨hz, hzS⟩, rfl⟩
  rw [e]
  refine sub_compl (sub_proj_loc (sub_inter hK (sub_compl hS)) fun x0 => ?_)
  obtain ⟨W, hW, Kb, hKb, h⟩ := hb x0
  exact ⟨W, hW, Kb, hKb, fun q hq hx => h q hq.1 hx⟩

end FO

end SubanalyticLib

/-! cddf89e7: the distance function `d_S` to a subanalytic set `S` is subanalytic (BDL 2007, Sec. 2.1).
Route: the strict epigraph `E = {d_S < t}` is the projection of `{(x,t,a) | a ∈ S, ‖x-a‖ < t}` along
locally bounded fibres (`sub_proj_loc`); its complement `{t ≤ d_S}` is subanalytic by the complement
theorem (`sub_compl`); `{t < d_S}` is the projection of `{(x,t,s) | t < s ≤ t+1, s ≤ d_S x}` (bounded
fibres); the graph is `{t ≤ d_S} ∩ {d_S ≤ t}`, two complements. -/

namespace SubanalyticLib

namespace InfDist

open Filter Topology

set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem lt_of_sq {u t : ℝ} (hu : 0 ≤ u) (ht : 0 < t) (h : u ^ 2 < t ^ 2) : u < t := by
  nlinarith

/-- the witness set `{((x,t),a) | a ∈ S, 0 < t, ‖x - a‖² < t²}`. -/
def epiW (S : Set E) : Set ((E × ℝ) × E) :=
  {q | q.2 ∈ S} ∩ ({q | 0 < q.1.2} ∩ {q | ‖q.1.1 - q.2‖ ^ 2 < q.1.2 ^ 2})

theorem epiW_sub {S : Set E} (hS : IsSubanalytic S) : IsSubanalytic (epiW S) := by
  refine sub_inter_semi (sub_preimage (Φ := fun q : (E × ℝ) × E => q.2)
    (fun _ => analyticAt_snd) hS) (semi_inter ?_ ?_)
  · exact semi_pos (G := fun q : (E × ℝ) × E => q.1.2)
      (fun q _ => analyticAt_snd.comp analyticAt_fst)
  · refine semi_lt (F := fun q : (E × ℝ) × E => ‖q.1.1 - q.2‖ ^ 2)
      (G := fun q : (E × ℝ) × E => q.1.2 ^ 2) ?_ ?_
    · intro q _
      exact (analytic_normsq _).comp ((analyticAt_fst.comp analyticAt_fst).sub analyticAt_snd)
    · intro q _
      exact (analyticAt_snd.comp analyticAt_fst).pow 2

theorem strictEpi_eq {S : Set E} (hne : S.Nonempty) :
    {p : E × ℝ | Metric.infDist p.1 S < p.2} = Prod.fst '' epiW S := by
  ext p
  constructor
  · intro hp
    obtain ⟨a, haS, hd⟩ := (Metric.infDist_lt_iff hne).1 hp
    rw [dist_eq_norm] at hd
    have h0 : 0 < p.2 := lt_of_le_of_lt (norm_nonneg _) hd
    refine ⟨(p, a), ⟨haS, h0, ?_⟩, rfl⟩
    show ‖p.1 - a‖ ^ 2 < p.2 ^ 2
    nlinarith [norm_nonneg (p.1 - a)]
  · rintro ⟨q, ⟨haS, ht, hlt⟩, rfl⟩
    show Metric.infDist q.1.1 S < q.1.2
    refine (Metric.infDist_lt_iff hne).2 ⟨q.2, haS, ?_⟩
    rw [dist_eq_norm]
    exact lt_of_sq (norm_nonneg _) ht hlt

/-- the strict epigraph `{(x,t) | d_S x < t}` is subanalytic. -/
theorem sub_strictEpi {S : Set E} (hS : IsSubanalytic S) :
    IsSubanalytic {p : E × ℝ | Metric.infDist p.1 S < p.2} := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Metric.infDist_empty]
    exact sub_of_semi (semi_pos (G := fun p : E × ℝ => p.2) (fun p _ => analyticAt_snd))
  rw [strictEpi_eq hne]
  refine sub_proj_loc (epiW_sub hS) fun p0 => ⟨Metric.ball p0 1, Metric.ball_mem_nhds p0 one_pos,
    Metric.closedBall 0 (‖p0.1‖ + |p0.2| + 2), Metric.isBounded_closedBall, ?_⟩
  rintro q ⟨-, ht, hlt⟩ hp
  have hd : ‖q.1.1 - q.2‖ < q.1.2 := lt_of_sq (norm_nonneg _) ht hlt
  have hp' : dist q.1 p0 < 1 := hp
  rw [Prod.dist_eq] at hp'
  have h1 : ‖q.1.1 - p0.1‖ < 1 := by
    rw [← dist_eq_norm]; exact lt_of_le_of_lt (le_max_left _ _) hp'
  have h2 : |q.1.2 - p0.2| < 1 := by
    rw [← Real.dist_eq]; exact lt_of_le_of_lt (le_max_right _ _) hp'
  rw [Metric.mem_closedBall, dist_zero_right]
  have e1 : ‖q.2‖ ≤ ‖q.1.1‖ + ‖q.1.1 - q.2‖ := by
    calc ‖q.2‖ = ‖q.1.1 - (q.1.1 - q.2)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖q.1.1‖ + ‖q.1.1 - q.2‖ := norm_sub_le _ _
  have e2 : ‖q.1.1‖ ≤ ‖p0.1‖ + ‖q.1.1 - p0.1‖ := by
    calc ‖q.1.1‖ = ‖p0.1 + (q.1.1 - p0.1)‖ := by rw [add_sub_cancel]
      _ ≤ ‖p0.1‖ + ‖q.1.1 - p0.1‖ := norm_add_le _ _
  have e3 := le_abs_self p0.2
  have e4 := (abs_lt.1 h2).2
  linarith

/-- the witness set `{((x,t),s) | ¬ (d_S x < s), t < s, s ≤ t + 1}`. -/
def lowW (S : Set E) : Set ((E × ℝ) × ℝ) :=
  (fun q : (E × ℝ) × ℝ => (q.1.1, q.2)) ⁻¹' {p : E × ℝ | Metric.infDist p.1 S < p.2}ᶜ ∩
    ({q | q.1.2 < q.2} ∩ {q | q.2 ≤ q.1.2 + 1})

theorem lowW_sub {S : Set E} (hS : IsSubanalytic S) : IsSubanalytic (lowW S) := by
  refine sub_inter_semi (sub_preimage ?_ (sub_compl (sub_strictEpi hS))) (semi_inter ?_ ?_)
  · intro q
    exact (analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd
  · exact semi_lt (F := fun q : (E × ℝ) × ℝ => q.1.2) (G := fun q : (E × ℝ) × ℝ => q.2)
      (fun q _ => analyticAt_snd.comp analyticAt_fst) (fun q _ => analyticAt_snd)
  · exact semi_le (F := fun q : (E × ℝ) × ℝ => q.2) (G := fun q : (E × ℝ) × ℝ => q.1.2 + 1)
      (fun q _ => analyticAt_snd) (fun q _ => (analyticAt_snd.comp analyticAt_fst).add analyticAt_const)

theorem lowStrict_eq (S : Set E) :
    {p : E × ℝ | p.2 < Metric.infDist p.1 S} = Prod.fst '' lowW S := by
  ext p
  constructor
  · intro hp
    refine ⟨(p, min (Metric.infDist p.1 S) (p.2 + 1)), ⟨?_, ?_, ?_⟩, rfl⟩
    · show ¬ (Metric.infDist p.1 S < min (Metric.infDist p.1 S) (p.2 + 1))
      exact not_lt.2 (min_le_left _ _)
    · show p.2 < min (Metric.infDist p.1 S) (p.2 + 1)
      exact lt_min hp (by linarith)
    · show min (Metric.infDist p.1 S) (p.2 + 1) ≤ p.2 + 1
      exact min_le_right _ _
  · rintro ⟨q, ⟨h1, h2, -⟩, rfl⟩
    have h1' : ¬ (Metric.infDist q.1.1 S < q.2) := h1
    have h2' : q.1.2 < q.2 := h2
    show q.1.2 < Metric.infDist q.1.1 S
    linarith [not_lt.1 h1']

/-- `{(x,t) | t < d_S x}` is subanalytic. -/
theorem sub_lowStrict {S : Set E} (hS : IsSubanalytic S) :
    IsSubanalytic {p : E × ℝ | p.2 < Metric.infDist p.1 S} := by
  rw [lowStrict_eq S]
  refine sub_proj_loc (lowW_sub hS) fun p0 => ⟨Metric.ball p0 1, Metric.ball_mem_nhds p0 one_pos,
    Set.Icc (p0.2 - 1) (p0.2 + 2), Metric.isBounded_Icc _ _, ?_⟩
  rintro q ⟨-, h2, h3⟩ hp
  have h2' : q.1.2 < q.2 := h2
  have h3' : q.2 ≤ q.1.2 + 1 := h3
  have hp' : dist q.1 p0 < 1 := hp
  rw [Prod.dist_eq] at hp'
  have h4 : |q.1.2 - p0.2| < 1 := by
    rw [← Real.dist_eq]; exact lt_of_le_of_lt (le_max_right _ _) hp'
  have h5 := abs_lt.1 h4
  exact ⟨by linarith [h5.1], by linarith [h5.2]⟩

/-- **the graph of `d_S` is subanalytic.** -/
theorem graph_sub {S : Set E} (hS : IsSubanalytic S) :
    IsSubanalytic {p : E × ℝ | ((Metric.infDist p.1 S : ℝ) : EReal) = (p.2 : EReal)} := by
  have e : {p : E × ℝ | ((Metric.infDist p.1 S : ℝ) : EReal) = (p.2 : EReal)} =
      {p : E × ℝ | Metric.infDist p.1 S < p.2}ᶜ ∩ {p : E × ℝ | p.2 < Metric.infDist p.1 S}ᶜ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, EReal.coe_eq_coe_iff,
      not_lt]
    constructor
    · intro h
      exact ⟨h.ge, h.le⟩
    · rintro ⟨h1, h2⟩
      exact le_antisymm h2 h1
  rw [e]
  exact sub_inter (sub_compl (sub_strictEpi hS)) (sub_compl (sub_lowStrict hS))

end InfDist

end SubanalyticLib

end TopOpen

theorem solution {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS : NonsmoothLojasiewicz.Continuous.IsSubanalytic S) :
    NonsmoothLojasiewicz.Continuous.IsSubanalyticFn
      (fun x => ((Metric.infDist x S : ℝ) : EReal)) := by
  exact SubanalyticLib.InfDist.graph_sub hS
