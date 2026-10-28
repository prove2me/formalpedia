-- Prove2me | solution 1 for NonsmoothLojasiewicz.Continuous.lojasiewicz_continuous_subanalytic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T06:41:08.613429+00:00
-- url     : https://prove2.me/submissions/0302a24b-0b7a-4258-908e-ba77bdf6cd6f

import Mathlib
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic
import Definitions.Def_NonsmoothLojasiewicz_Continuous_slope
import Definitions.Def_NonsmoothLojasiewicz_Continuous_LojIneqAt
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Theorems.Thm_NonsmoothLojasiewicz_Continuous_subanalytic_compl
import Theorems.Thm_NonsmoothLojasiewicz_Continuous_subanalytic_curve_selection

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
def HasArcAt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (A : Set X) (x₀ : X) : Prop :=
  ∃ γ : ℝ → X, AnalyticAt ℝ γ 0 ∧ γ 0 = x₀ ∧ ∃ ε > 0, ∀ u ∈ Set.Ioo (0 : ℝ) ε, γ u ∈ A
def CurveSelection (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] :
    Prop :=
  ∀ A : Set X, NonsmoothLojasiewicz.Continuous.IsSubanalytic A → ∀ x₀ ∈ closure A, HasArcAt A x₀
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


/-! SubanalyticLib L6c: the chain rule along a differentiable arc for regular subgradients
(used in BDL 2007 Thm 3.1, c2c9aa25): if `v` is a regular subgradient of `f` at `γ t`, and
`f ∘ γ = φ` near `t` with `φ`, `γ` differentiable at `t`, then `φ'(t) = ⟪v, γ'(t)⟫`. -/

open Filter Topology
open scoped InnerProductSpace

namespace SubanalyticLib

theorem deriv_zero_of_lower {h : ℝ → ℝ} {c t : ℝ} (hd : HasDerivAt h c t) (h0 : h t = 0)
    (hlow : ∀ ε > 0, ∀ᶠ s in 𝓝 t, -(ε * |s - t|) ≤ h s) : c = 0 := by
  by_contra hc
  have hpos : 0 < |c| := abs_pos.2 hc
  have hb := hd.isLittleO.def (half_pos hpos)
  have hl := hlow (|c| / 4) (by positivity)
  have hT : Tendsto (fun δ : ℝ => t - δ * c) (𝓝[>] 0) (𝓝 t) := by
    have hc' : Continuous (fun δ : ℝ => t - δ * c) := continuous_const.sub (continuous_id.mul continuous_const)
    have h1 := hc'.tendsto 0
    simp only [zero_mul, sub_zero] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  obtain ⟨δ, ⟨hb', hl'⟩, hδ⟩ := ((hT.eventually (hb.and hl)).and self_mem_nhdsWithin).exists
  have hδ0 : 0 < δ := hδ
  have e1 : t - δ * c - t = -(δ * c) := by ring
  have e2 : |t - δ * c - t| = δ * |c| := by
    rw [e1, abs_neg, abs_mul, abs_of_pos hδ0]
  simp only [Real.norm_eq_abs, smul_eq_mul, h0, sub_zero] at hb'
  rw [e2] at hb' hl'
  rw [e1] at hb'
  have hcc : |c| * |c| = c * c := abs_mul_abs_self c
  have hup := (abs_le.1 hb').2
  have hk : 0 < δ * (|c| * |c|) := by positivity
  nlinarith

theorem regular_subgrad_chain {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : E → EReal} {γ : ℝ → E} {φ : ℝ → ℝ} {t d : ℝ} {γ' v : E}
    (hγ : HasDerivAt γ γ' t) (hφ : HasDerivAt φ d t)
    (hfφ : ∀ᶠ s in 𝓝 t, f (γ s) = (φ s : EReal))
    (hv : NonconvexSplitting.Shared.IsRegularSubgrad f (γ t) v) : d = ⟪v, γ'⟫_ℝ := by
  have h2 : HasDerivAt (fun s => ⟪v, γ s⟫_ℝ) ⟪v, γ'⟫_ℝ t := by
    have := (hasDerivAt_const t v).inner ℝ hγ
    simpa using this
  let h : ℝ → ℝ := fun s => φ s - φ t - (⟪v, γ s⟫_ℝ - ⟪v, γ t⟫_ℝ)
  have hd : HasDerivAt h (d - ⟪v, γ'⟫_ℝ) t :=
    (hφ.sub_const (φ t)).sub (h2.sub_const _)
  have hlow : ∀ ε > 0, ∀ᶠ s in 𝓝 t, -(ε * |s - t|) ≤ h s := by
    intro ε hε
    obtain ⟨C, hC⟩ := hγ.isBigO_sub.bound
    set ε' := ε / (|C| + 1) with hε'
    have hε'0 : 0 < ε' := by positivity
    have hreg := hv.2 ε' hε'0
    have hreg' : ∀ᶠ s in 𝓝 t, f (γ t) + ((⟪v, γ s - γ t⟫_ℝ - ε' * ‖γ s - γ t‖ : ℝ) : EReal)
        ≤ f (γ s) := hγ.continuousAt.tendsto.eventually hreg
    have hft : f (γ t) = (φ t : EReal) := hfφ.self_of_nhds
    filter_upwards [hreg', hfφ, hC] with s hs hfs hCs
    rw [hft, hfs, ← EReal.coe_add, EReal.coe_le_coe_iff] at hs
    simp only [Real.norm_eq_abs] at hCs
    have hin : ⟪v, γ s - γ t⟫_ℝ = ⟪v, γ s⟫_ℝ - ⟪v, γ t⟫_ℝ := inner_sub_right _ _ _
    have hn := norm_nonneg (γ s - γ t)
    have hCa : ε' * ‖γ s - γ t‖ ≤ ε' * (|C| * |s - t|) := by
      refine mul_le_mul_of_nonneg_left (hCs.trans ?_) hε'0.le
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _)
    have hCb : ε' * (|C| * |s - t|) ≤ ε * |s - t| := by
      have h1 : ε' * |C| ≤ ε := by
        rw [hε', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [abs_nonneg C]
      have := mul_le_mul_of_nonneg_right h1 (abs_nonneg (s - t))
      linarith [mul_assoc ε' |C| |s - t|]
    show -(ε * |s - t|) ≤ φ s - φ t - (⟪v, γ s⟫_ℝ - ⟪v, γ t⟫_ℝ)
    rw [← hin]
    linarith
  have := deriv_zero_of_lower hd (by simp [h]) hlow
  linarith

end SubanalyticLib

/-! SubanalyticLib G8a/G8b (route G): the domain, the finite part and the regular-subgradient
graph of a subanalytic function `f : X → EReal` (closed domain, continuous on it) are subanalytic. -/

namespace SubanalyticLib

section SubDiff

open Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]

@[fun_prop] theorem AnalyticAt.fst' {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F × G} {e : E} (hf : AnalyticAt ℝ f e) : AnalyticAt ℝ (fun x => (f x).1) e :=
  analyticAt_fst.comp hf

@[fun_prop] theorem AnalyticAt.snd' {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F × G} {e : E} (hf : AnalyticAt ℝ f e) : AnalyticAt ℝ (fun x => (f x).2) e :=
  analyticAt_snd.comp hf

theorem analyticAt_inner_fun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → X} {e : E} (ha : AnalyticAt ℝ a e) (hb : AnalyticAt ℝ b e) :
    AnalyticAt ℝ (fun r => ⟪a r, b r⟫_ℝ) e := by
  have h : AnalyticAt ℝ (fun p : X × X => innerSL ℝ p.1 p.2) (a e, b e) :=
    (innerSL ℝ (E := X)).analyticAt_bilinear (a e, b e)
  exact AnalyticAt.comp (f := fun r => (a r, b r)) (x := e) h (ha.prod hb)

/-- **G8a** local bound of `toReal ∘ f` on the closed domain. -/
theorem locBdd_toReal (f : X → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hcl : IsClosed {x | f x ≠ ⊤}) (hcont : ContinuousOn f {x | f x ≠ ⊤}) (x0 : X) (r : ℝ) :
    ∃ M : ℝ, ∀ x ∈ Metric.closedBall x0 r, f x ≠ ⊤ → |(f x).toReal| ≤ M := by
  set K := Metric.closedBall x0 r ∩ {x | f x ≠ ⊤}
  have hK : IsCompact K := (isCompact_closedBall x0 r).inter_right hcl
  rcases K.eq_empty_or_nonempty with hE | hne
  · refine ⟨0, fun x hx hfx => ?_⟩
    have : x ∈ K := ⟨hx, hfx⟩
    rw [hE] at this
    exact absurd this (Set.notMem_empty x)
  obtain ⟨xM, hxM, hM⟩ := hK.exists_isMaxOn hne (hcont.mono Set.inter_subset_right)
  obtain ⟨xm, hxm, hm⟩ := hK.exists_isMinOn hne (hcont.mono Set.inter_subset_right)
  refine ⟨max |(f xm).toReal| |(f xM).toReal|, fun x hx hfx => ?_⟩
  have hxK : x ∈ K := ⟨hx, hfx⟩
  have h1 : (f xm).toReal ≤ (f x).toReal := EReal.toReal_le_toReal (hm hxK) (hbot _) hfx
  have h2 : (f x).toReal ≤ (f xM).toReal := EReal.toReal_le_toReal (hM hxK) (hbot _) hxM.2
  exact abs_le_max_abs_abs h1 h2

theorem graph_iff (f : X → EReal) (hbot : ∀ x, f x ≠ ⊥) (x : X) (t : ℝ) :
    f x = (t : EReal) ↔ f x ≠ ⊤ ∧ (f x).toReal = t := by
  constructor
  · intro h; rw [h]; exact ⟨EReal.coe_ne_top t, EReal.toReal_coe t⟩
  · rintro ⟨h1, h2⟩; rw [← h2, EReal.coe_toReal h1 (hbot x)]

/-- `f x = ↑t` pulled back along analytic coordinate maps. -/
theorem sub_graph_pull {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : X → EReal) (hsub : IsSubanalyticFn f) {π : E → X} {σ : E → ℝ}
    (hπ : ∀ e, AnalyticAt ℝ π e) (hσ : ∀ e, AnalyticAt ℝ σ e) :
    IsSubanalytic {e : E | f (π e) = (σ e : EReal)} :=
  sub_preimage (Φ := fun e => (π e, σ e)) (fun e => (hπ e).prod (hσ e)) hsub

/-- **G8a** the domain `{f ≠ ⊤}` is subanalytic. -/
theorem sub_dom (f : X → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hcl : IsClosed {x | f x ≠ ⊤}) (hcont : ContinuousOn f {x | f x ≠ ⊤})
    (hsub : IsSubanalyticFn f) : IsSubanalytic {x | f x ≠ ⊤} := by
  have e : {x | f x ≠ ⊤} = Prod.fst '' {p : X × ℝ | f p.1 = (p.2 : EReal)} := by
    ext x
    constructor
    · intro hx
      exact ⟨(x, (f x).toReal), (EReal.coe_toReal hx (hbot x)).symm, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      show f p.1 ≠ ⊤
      rw [hp]; exact EReal.coe_ne_top _
  rw [e]
  refine sub_proj_loc hsub fun x0 => ?_
  obtain ⟨M, hM⟩ := locBdd_toReal f hbot hcl hcont x0 1
  refine ⟨Metric.ball x0 1, Metric.ball_mem_nhds x0 one_pos, Set.Icc (-M) M,
    Metric.isBounded_Icc _ _, fun q hq hx => ?_⟩
  have hq' := (graph_iff f hbot q.1 q.2).1 hq
  have := hM q.1 (Metric.ball_subset_closedBall hx) hq'.1
  rw [hq'.2] at this
  exact abs_le.1 this

/-- The `P'` set of G8b: `x, z ∈ dom f` and `g x + ⟪v, z - x⟫ - ε ‖z - x‖ ≤ g z`
(coordinates `((((x, v), ε), δ), z)`). -/
def regP (f : X → EReal) : Set ((((X × X) × ℝ) × ℝ) × X) :=
  {q | f q.1.1.1.1 ≠ ⊤ ∧ f q.2 ≠ ⊤ ∧
    (f q.1.1.1.1).toReal + ⟪q.1.1.1.2, q.2 - q.1.1.1.1⟫_ℝ - q.1.1.2 * ‖q.2 - q.1.1.1.1‖
      ≤ (f q.2).toReal}

theorem sub_regP (f : X → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hcl : IsClosed {x | f x ≠ ⊤}) (hcont : ContinuousOn f {x | f x ≠ ⊤})
    (hsub : IsSubanalyticFn f) : IsSubanalytic (regP f) := by
  set A : Set (((((X × X) × ℝ) × ℝ) × X) × (ℝ × (ℝ × ℝ))) :=
    {r | f r.1.1.1.1.1 = (r.2.1 : EReal)} ∩ {r | f r.1.2 = (r.2.2.1 : EReal)} ∩
      ({r | 0 ≤ r.2.2.2} ∩ {r | r.2.2.2 ^ 2 = ⟪r.1.2 - r.1.1.1.1.1, r.1.2 - r.1.1.1.1.1⟫_ℝ} ∩
        {r | r.2.1 + ⟪r.1.1.1.1.2, r.1.2 - r.1.1.1.1.1⟫_ℝ - r.1.1.1.2 * r.2.2.2 ≤ r.2.2.1})
    with hAdef
  have hA : IsSubanalytic A := by
    refine sub_inter (sub_inter (sub_graph_pull f hsub (fun _ => by fun_prop) (fun _ => by fun_prop))
      (sub_graph_pull f hsub (fun _ => by fun_prop) (fun _ => by fun_prop))) (sub_of_semi ?_)
    refine semi_inter (semi_inter (semi_le (fun _ _ => by fun_prop) (fun _ _ => by fun_prop))
      (semi_eq (fun _ _ => by fun_prop) (fun _ _ => analyticAt_inner_fun (by fun_prop) (by fun_prop))))
      (semi_le (fun _ _ => ?_) (fun _ _ => by fun_prop))
    refine (AnalyticAt.add ?_ (analyticAt_inner_fun ?_ ?_)).sub ?_ <;> fun_prop
  have e : regP f = Prod.fst '' A := by
    ext q
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨(q, ((f q.1.1.1.1).toReal, ((f q.2).toReal, ‖q.2 - q.1.1.1.1‖))), ?_, rfl⟩
      refine ⟨⟨(EReal.coe_toReal h1 (hbot _)).symm, (EReal.coe_toReal h2 (hbot _)).symm⟩,
        ⟨norm_nonneg _, ?_⟩, h3⟩
      simp [real_inner_self_eq_norm_sq]
    · rintro ⟨r, ⟨⟨hr1, hr2⟩, ⟨hr3, hr4⟩, hr5⟩, rfl⟩
      have g1 := (graph_iff f hbot _ _).1 hr1
      have g2 := (graph_iff f hbot _ _).1 hr2
      have hρ : r.2.2.2 = ‖r.1.2 - r.1.1.1.1.1‖ := by
        simp only [Set.mem_setOf_eq, real_inner_self_eq_norm_sq] at hr4
        exact (pow_left_inj₀ hr3 (norm_nonneg _) two_ne_zero).1 hr4
      refine ⟨g1.1, g2.1, ?_⟩
      rw [g1.2, g2.2, ← hρ]
      exact hr5
  rw [e]
  refine sub_proj_loc hA fun q0 => ?_
  obtain ⟨M1, hM1⟩ := locBdd_toReal f hbot hcl hcont q0.1.1.1.1 1
  obtain ⟨M2, hM2⟩ := locBdd_toReal f hbot hcl hcont q0.2 1
  refine ⟨{q | q.1.1.1.1 ∈ Metric.ball q0.1.1.1.1 1 ∧ q.2 ∈ Metric.ball q0.2 1}, ?_,
    Set.Icc (-M1) M1 ×ˢ (Set.Icc (-M2) M2 ×ˢ Set.Icc 0 (‖q0.2 - q0.1.1.1.1‖ + 2)),
    (Metric.isBounded_Icc _ _).prod ((Metric.isBounded_Icc _ _).prod (Metric.isBounded_Icc _ _)),
    ?_⟩
  · refine IsOpen.mem_nhds ?_ ⟨Metric.mem_ball_self one_pos, Metric.mem_ball_self one_pos⟩
    exact (Metric.isOpen_ball.preimage (by fun_prop)).inter
      (Metric.isOpen_ball.preimage continuous_snd)
  · rintro r ⟨⟨hr1, hr2⟩, ⟨hr3, hr4⟩, -⟩ ⟨hx, hz⟩
    have g1 := (graph_iff f hbot _ _).1 hr1
    have g2 := (graph_iff f hbot _ _).1 hr2
    have b1 := hM1 _ (Metric.ball_subset_closedBall hx) g1.1
    have b2 := hM2 _ (Metric.ball_subset_closedBall hz) g2.1
    rw [g1.2] at b1
    rw [g2.2] at b2
    have hρ : r.2.2.2 = ‖r.1.2 - r.1.1.1.1.1‖ := by
      simp only [Set.mem_setOf_eq, real_inner_self_eq_norm_sq] at hr4
      exact (pow_left_inj₀ hr3 (norm_nonneg _) two_ne_zero).1 hr4
    refine ⟨abs_le.1 b1, abs_le.1 b2, hr3, ?_⟩
    rw [hρ]
    have hx' : ‖r.1.1.1.1.1 - q0.1.1.1.1‖ < 1 := by rw [← dist_eq_norm]; exact hx
    have hz' : ‖r.1.2 - q0.2‖ < 1 := by rw [← dist_eq_norm]; exact hz
    calc ‖r.1.2 - r.1.1.1.1.1‖
        = ‖(r.1.2 - q0.2) + (q0.2 - q0.1.1.1.1) - (r.1.1.1.1.1 - q0.1.1.1.1)‖ := by
          congr 1; abel
      _ ≤ ‖r.1.2 - q0.2‖ + ‖q0.2 - q0.1.1.1.1‖ + ‖r.1.1.1.1.1 - q0.1.1.1.1‖ :=
          (norm_sub_le _ _).trans (by linarith [norm_add_le (r.1.2 - q0.2) (q0.2 - q0.1.1.1.1)])
      _ ≤ ‖q0.2 - q0.1.1.1.1‖ + 2 := by linarith

/-- the ball constraint of G8b (coordinates `((((x, v), ε), δ), z)`). -/
def regK (f : X → EReal) : Set ((((X × X) × ℝ) × ℝ) × X) :=
  {q | ⟪q.2 - q.1.1.1.1, q.2 - q.1.1.1.1⟫_ℝ < q.1.2 ^ 2} ∩ {q | 0 < q.1.2} ∩ {q | q.1.2 ≤ 1} ∩
    Prod.snd ⁻¹' {x | f x ≠ ⊤}

theorem norm_lt_of_inner_lt {w : X} {δ : ℝ} (hδ : 0 < δ) (h : ⟪w, w⟫_ℝ < δ ^ 2) : ‖w‖ < δ := by
  rw [real_inner_self_eq_norm_sq] at h
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hδ.le two_ne_zero).1 h

theorem inner_lt_of_norm_lt {w : X} {δ : ℝ} (h : ‖w‖ < δ) : ⟪w, w⟫_ℝ < δ ^ 2 := by
  rw [real_inner_self_eq_norm_sq]
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) ((norm_nonneg _).trans h.le) two_ne_zero).2 h

/-- **G8b** the regular-subgradient condition in bounded first-order form. -/
theorem regSub_iff (f : X → EReal) (hbot : ∀ x, f x ≠ ⊥) (x v : X) :
    NonconvexSplitting.Shared.IsRegularSubgrad f x v ↔ f x ≠ ⊤ ∧ ∀ e : ℝ, 0 < e → e ≤ 1 →
      ∃ δ : ℝ, (0 < δ ∧ δ ≤ 1) ∧ ∀ z, ⟪z - x, z - x⟫_ℝ < δ ^ 2 → f z ≠ ⊤ →
        (f x).toReal + ⟪v, z - x⟫_ℝ - e * ‖z - x‖ ≤ (f z).toReal := by
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun e he _ => ?_⟩
    obtain ⟨δ0, hδ0, hP⟩ := Metric.eventually_nhds_iff.1 (h e he)
    refine ⟨min δ0 1, ⟨lt_min hδ0 one_pos, min_le_right _ _⟩, fun z hz hfz => ?_⟩
    have hn := norm_lt_of_inner_lt (lt_min hδ0 one_pos) hz
    have hd : dist z x < δ0 := by rw [dist_eq_norm]; exact hn.trans_le (min_le_left _ _)
    have := hP hd
    rw [← EReal.coe_toReal hx (hbot x), ← EReal.coe_toReal hfz (hbot z), ← EReal.coe_add,
      EReal.coe_le_coe_iff] at this
    linarith
  · rintro ⟨hx, H⟩
    refine ⟨hx, fun ε hε => ?_⟩
    obtain ⟨δ, ⟨hδ, -⟩, hP⟩ := H (min ε 1) (lt_min hε one_pos) (min_le_right _ _)
    refine Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun {z} hz => ?_⟩
    by_cases hfz : f z = ⊤
    · rw [hfz]; exact le_top
    have hn : ‖z - x‖ < δ := by rw [← dist_eq_norm]; exact hz
    have h1 := hP z (inner_lt_of_norm_lt hn) hfz
    have h2 : min ε 1 * ‖z - x‖ ≤ ε * ‖z - x‖ :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
    rw [← EReal.coe_toReal hx (hbot x), ← EReal.coe_toReal hfz (hbot z), ← EReal.coe_add,
      EReal.coe_le_coe_iff]
    linarith

/-- **G8b** the graph of the regular subdifferential is subanalytic. -/
theorem sub_regSub (f : X → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hcl : IsClosed {x | f x ≠ ⊤}) (hcont : ContinuousOn f {x | f x ≠ ⊤})
    (hsub : IsSubanalyticFn f) :
    IsSubanalytic {u : X × X | NonconvexSplitting.Shared.IsRegularSubgrad f u.1 u.2} := by
  have hD := sub_dom f hbot hcl hcont hsub
  have hK : IsSubanalytic (regK f) := by
    refine sub_inter (sub_of_semi ?_) (sub_preimage (fun _ => analyticAt_snd) hD)
    refine semi_inter (semi_inter (semi_lt (fun _ _ => analyticAt_inner_fun (by fun_prop) (by fun_prop))
      (fun _ _ => by fun_prop)) (semi_lt (fun _ _ => by fun_prop) (fun _ _ => by fun_prop)))
      (semi_le (fun _ _ => by fun_prop) (fun _ _ => by fun_prop))
  have hQ1 : IsSubanalytic {w : ((X × X) × ℝ) × ℝ | ∀ z, (w, z) ∈ regK f → (w, z) ∈ regP f} := by
    refine sub_forall_loc (sub_regP f hbot hcl hcont hsub) hK fun w0 => ?_
    refine ⟨{w | w.1.1.1 ∈ Metric.ball w0.1.1.1 1},
      IsOpen.mem_nhds (Metric.isOpen_ball.preimage (by fun_prop)) (Metric.mem_ball_self one_pos),
      Metric.closedBall w0.1.1.1 2, Metric.isBounded_closedBall, fun q hq hx => ?_⟩
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, -⟩ := hq
    have hn := norm_lt_of_inner_lt h2 h1
    have hx' : dist q.1.1.1.1 w0.1.1.1 < 1 := hx
    rw [Metric.mem_closedBall, dist_eq_norm] at *
    have h3' : q.1.2 ≤ 1 := h3
    have : ‖q.2 - w0.1.1.1‖ ≤ ‖q.2 - q.1.1.1.1‖ + ‖q.1.1.1.1 - w0.1.1.1‖ := by
      simpa using norm_add_le (q.2 - q.1.1.1.1) (q.1.1.1.1 - w0.1.1.1)
    linarith
  have hQ2 : IsSubanalytic (Prod.fst '' ({w : ((X × X) × ℝ) × ℝ |
      ∀ z, (w, z) ∈ regK f → (w, z) ∈ regP f} ∩ ({w | 0 < w.2} ∩ {w | w.2 ≤ 1}))) := by
    refine sub_proj_loc (sub_inter hQ1 (sub_of_semi (semi_inter
      (semi_lt (fun _ _ => by fun_prop) (fun _ _ => by fun_prop))
      (semi_le (fun _ _ => by fun_prop) (fun _ _ => by fun_prop))))) fun _ => ?_
    exact ⟨Set.univ, Filter.univ_mem, Set.Icc 0 1, Metric.isBounded_Icc _ _,
      fun q hq _ => ⟨hq.2.1.le, hq.2.2⟩⟩
  have hQ3 := sub_forall_loc hQ2 (sub_of_semi (semi_inter
      (semi_lt (fun _ _ => by fun_prop) (fun _ _ => by fun_prop))
      (semi_le (fun _ _ => by fun_prop) (fun _ _ => by fun_prop))))
    (K := {p : (X × X) × ℝ | 0 < p.2} ∩ {p | p.2 ≤ 1}) fun _ =>
      ⟨Set.univ, Filter.univ_mem, Set.Icc 0 1, Metric.isBounded_Icc _ _,
        fun q hq _ => ⟨hq.1.le, hq.2⟩⟩
  have e : {u : X × X | NonconvexSplitting.Shared.IsRegularSubgrad f u.1 u.2} =
      Prod.fst ⁻¹' {x | f x ≠ ⊤} ∩ {u | ∀ e, (u, e) ∈ {p : (X × X) × ℝ | 0 < p.2} ∩ {p | p.2 ≤ 1} →
        (u, e) ∈ Prod.fst '' ({w : ((X × X) × ℝ) × ℝ |
          ∀ z, (w, z) ∈ regK f → (w, z) ∈ regP f} ∩ ({w | 0 < w.2} ∩ {w | w.2 ≤ 1}))} := by
    ext ⟨x, v⟩
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, regSub_iff f hbot]
    constructor
    · rintro ⟨hx, H⟩
      refine ⟨hx, fun e ⟨he, he1⟩ => ?_⟩
      obtain ⟨δ, ⟨hδ, hδ1⟩, hP⟩ := H e he he1
      refine ⟨(((x, v), e), δ), ⟨fun z hz => ?_, hδ, hδ1⟩, rfl⟩
      obtain ⟨⟨⟨h1, -⟩, -⟩, h4⟩ := hz
      exact ⟨hx, h4, hP z h1 h4⟩
    · rintro ⟨hx, H⟩
      refine ⟨hx, fun e he he1 => ?_⟩
      obtain ⟨w, ⟨hw, hδ, hδ1⟩, hw1⟩ := H e ⟨he, he1⟩
      obtain ⟨u, δ⟩ := w
      cases hw1
      exact ⟨δ, ⟨hδ, hδ1⟩, fun z hz hfz => (hw z ⟨⟨⟨hz, hδ⟩, hδ1⟩, hfz⟩).2.2⟩
  rw [e]
  exact sub_inter (sub_preimage (fun _ => analyticAt_fst) hD) hQ3

theorem tendsto_of_norm_lt_inv {x : X} {ys : ℕ → X} (h : ∀ t : ℕ, ‖ys t - x‖ < 1 / ((t : ℝ) + 1)) :
    Tendsto ys atTop (𝓝 x) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun t => (h t).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

/-- **G8c** the limiting subdifferential in bounded first-order form (BDL Prop 2.13 shape). -/
theorem limSub_iff (f : X → EReal) (hbot : ∀ x, f x ≠ ⊥) (x v : X) :
    v ∈ NonconvexSplitting.Shared.LimitingSubdiff f x ↔ f x ≠ ⊤ ∧ ∀ e : ℝ, 0 < e → e ≤ 1 →
      ∃ y w : X, NonconvexSplitting.Shared.IsRegularSubgrad f y w ∧ ‖y - x‖ < e ∧
        |(f y).toReal - (f x).toReal| < e ∧ ‖w - v‖ < e := by
  constructor
  · rintro ⟨hx, xs, vs, h1, h2, h3, h4⟩
    refine ⟨hx, fun e he _ => ?_⟩
    have g2 : Tendsto (fun t => (f (xs t)).toReal) atTop (𝓝 (f x).toReal) :=
      (EReal.tendsto_toReal hx (hbot x)).comp h2
    have a1 := (tendsto_iff_norm_sub_tendsto_zero.1 h1).eventually (gt_mem_nhds he)
    have a2 := (tendsto_iff_norm_sub_tendsto_zero.1 g2).eventually (gt_mem_nhds he)
    have a3 := (tendsto_iff_norm_sub_tendsto_zero.1 h3).eventually (gt_mem_nhds he)
    obtain ⟨t, ht⟩ := ((a1.and a2).and a3).exists
    exact ⟨xs t, vs t, h4 t, ht.1.1, by simpa [Real.norm_eq_abs] using ht.1.2, ht.2⟩
  · rintro ⟨hx, H⟩
    have H' : ∀ t : ℕ, ∃ y w : X, NonconvexSplitting.Shared.IsRegularSubgrad f y w ∧
        ‖y - x‖ < 1 / ((t : ℝ) + 1) ∧ |(f y).toReal - (f x).toReal| < 1 / ((t : ℝ) + 1) ∧
        ‖w - v‖ < 1 / ((t : ℝ) + 1) := fun t =>
      H _ (by positivity) (by
        rw [div_le_one (by positivity)]; exact le_add_of_nonneg_left (Nat.cast_nonneg t))
    choose ys ws hreg hy hg hw using H'
    refine ⟨hx, ys, ws, tendsto_of_norm_lt_inv hy, ?_, tendsto_of_norm_lt_inv hw, hreg⟩
    have hr : Tendsto (fun t => (f (ys t)).toReal) atTop (𝓝 (f x).toReal) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      exact squeeze_zero (fun _ => norm_nonneg _) (fun t => (hg t).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    have hc := (continuous_coe_real_ereal.tendsto _).comp hr
    rw [EReal.coe_toReal hx (hbot x)] at hc
    refine hc.congr fun t => ?_
    exact EReal.coe_toReal (hreg t).1 (hbot _)

/-- **G8c** the graph of the limiting subdifferential is subanalytic. -/
theorem sub_limSub (f : X → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hcl : IsClosed {x | f x ≠ ⊤}) (hcont : ContinuousOn f {x | f x ≠ ⊤})
    (hsub : IsSubanalyticFn f) :
    IsSubanalytic {u : X × X | u.2 ∈ NonconvexSplitting.Shared.LimitingSubdiff f u.1} := by
  have hD := sub_dom f hbot hcl hcont hsub
  have hRS := sub_regSub f hbot hcl hcont hsub
  set A : Set (((X × X) × ℝ) × ((X × X) × (ℝ × ℝ))) :=
    {r | NonconvexSplitting.Shared.IsRegularSubgrad f r.2.1.1 r.2.1.2} ∩
      {r | f r.2.1.1 = (r.2.2.1 : EReal)} ∩ {r | f r.1.1.1 = (r.2.2.2 : EReal)} ∩
      ({r | ⟪r.2.1.1 - r.1.1.1, r.2.1.1 - r.1.1.1⟫_ℝ < r.1.2 ^ 2} ∩ {r | 0 < r.1.2} ∩
        {r | ⟪r.2.1.2 - r.1.1.2, r.2.1.2 - r.1.1.2⟫_ℝ < r.1.2 ^ 2} ∩
        {r | r.2.2.1 - r.2.2.2 < r.1.2} ∩ {r | r.2.2.2 - r.2.2.1 < r.1.2}) with hA
  have hAs : IsSubanalytic A := by
    refine sub_inter (sub_inter (sub_inter
      (sub_preimage (Φ := fun r : ((X × X) × ℝ) × ((X × X) × (ℝ × ℝ)) => r.2.1)
        (fun _ => by fun_prop) hRS)
      (sub_graph_pull f hsub (fun _ => by fun_prop) (fun _ => by fun_prop)))
      (sub_graph_pull f hsub (fun _ => by fun_prop) (fun _ => by fun_prop))) (sub_of_semi ?_)
    refine semi_inter (semi_inter (semi_inter (semi_inter
      (semi_lt (fun _ _ => analyticAt_inner_fun (by fun_prop) (by fun_prop)) (fun _ _ => by fun_prop))
      (semi_lt (fun _ _ => by fun_prop) (fun _ _ => by fun_prop)))
      (semi_lt (fun _ _ => analyticAt_inner_fun (by fun_prop) (by fun_prop)) (fun _ _ => by fun_prop)))
      (semi_lt (fun _ _ => by fun_prop) (fun _ _ => by fun_prop)))
      (semi_lt (fun _ _ => by fun_prop) (fun _ _ => by fun_prop))
  have hP : IsSubanalytic (Prod.fst '' A) := by
    refine sub_proj_loc hAs fun p0 => ?_
    set R : ℝ := |p0.2| + 2 with hR
    obtain ⟨M, hM⟩ := locBdd_toReal f hbot hcl hcont p0.1.1 R
    refine ⟨{p | p.1.1 ∈ Metric.ball p0.1.1 1 ∧ p.1.2 ∈ Metric.ball p0.1.2 1 ∧ p.2 < p0.2 + 1}, ?_,
      (Metric.closedBall p0.1.1 R ×ˢ Metric.closedBall p0.1.2 R) ×ˢ
        (Set.Icc (-M) M ×ˢ Set.Icc (-M) M),
      (Metric.isBounded_closedBall.prod Metric.isBounded_closedBall).prod
        ((Metric.isBounded_Icc _ _).prod (Metric.isBounded_Icc _ _)), ?_⟩
    · exact IsOpen.mem_nhds ((Metric.isOpen_ball.preimage (by fun_prop)).inter
        ((Metric.isOpen_ball.preimage (by fun_prop)).inter (isOpen_lt continuous_snd continuous_const)))
        ⟨Metric.mem_ball_self one_pos, Metric.mem_ball_self one_pos, lt_add_one _⟩
    · rintro r ⟨⟨⟨hreg, hs⟩, ht⟩, ⟨⟨⟨⟨h1, h0⟩, h3⟩, -⟩, -⟩⟩ ⟨hx, hv, he⟩
      have h0' : 0 < r.1.2 := h0
      have hy := norm_lt_of_inner_lt h0' h1
      have hw := norm_lt_of_inner_lt h0' h3
      have hx' : ‖r.1.1.1 - p0.1.1‖ < 1 := by rw [← dist_eq_norm]; exact hx
      have hv' : ‖r.1.1.2 - p0.1.2‖ < 1 := by rw [← dist_eq_norm]; exact hv
      have he' : r.1.2 < |p0.2| + 1 := he.trans_le (by linarith [le_abs_self p0.2])
      have ny : ‖r.2.1.1 - p0.1.1‖ ≤ R := by
        have := norm_add_le (r.2.1.1 - r.1.1.1) (r.1.1.1 - p0.1.1)
        rw [sub_add_sub_cancel] at this
        linarith
      have nw : ‖r.2.1.2 - p0.1.2‖ ≤ R := by
        have := norm_add_le (r.2.1.2 - r.1.1.2) (r.1.1.2 - p0.1.2)
        rw [sub_add_sub_cancel] at this
        linarith
      have nx : ‖r.1.1.1 - p0.1.1‖ ≤ R := by linarith [abs_nonneg p0.2]
      have gs := (graph_iff f hbot _ _).1 hs
      have gt := (graph_iff f hbot _ _).1 ht
      have b1 := hM _ (by rw [Metric.mem_closedBall, dist_eq_norm]; exact ny) gs.1
      have b2 := hM _ (by rw [Metric.mem_closedBall, dist_eq_norm]; exact nx) gt.1
      rw [gs.2] at b1
      rw [gt.2] at b2
      refine ⟨⟨?_, ?_⟩, abs_le.1 b1, abs_le.1 b2⟩
      · rw [Metric.mem_closedBall, dist_eq_norm]; exact ny
      · rw [Metric.mem_closedBall, dist_eq_norm]; exact nw
  have e : {u : X × X | u.2 ∈ NonconvexSplitting.Shared.LimitingSubdiff f u.1} =
      Prod.fst ⁻¹' {x | f x ≠ ⊤} ∩ {u | ∀ e, (u, e) ∈ {p : (X × X) × ℝ | 0 < p.2} ∩ {p | p.2 ≤ 1} →
        (u, e) ∈ Prod.fst '' A} := by
    ext ⟨x, v⟩
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, limSub_iff f hbot]
    constructor
    · rintro ⟨hx, H⟩
      refine ⟨hx, fun e ⟨he, he1⟩ => ?_⟩
      obtain ⟨y, w, hreg, h1, h2, h3⟩ := H e he he1
      refine ⟨(((x, v), e), ((y, w), ((f y).toReal, (f x).toReal))),
        ⟨⟨⟨hreg, (EReal.coe_toReal hreg.1 (hbot y)).symm⟩, (EReal.coe_toReal hx (hbot x)).symm⟩,
          ⟨⟨⟨⟨inner_lt_of_norm_lt h1, he⟩, inner_lt_of_norm_lt h3⟩, ?_⟩, ?_⟩⟩, rfl⟩
      · exact (abs_lt.1 h2).2
      · show (f x).toReal - (f y).toReal < e
        linarith [(abs_lt.1 h2).1]
    · rintro ⟨hx, H⟩
      refine ⟨hx, fun e he he1 => ?_⟩
      obtain ⟨r, ⟨⟨⟨hreg, hs⟩, ht⟩, ⟨⟨⟨⟨h1, -⟩, h3⟩, h4⟩, h5⟩⟩, hr⟩ := H e ⟨he, he1⟩
      obtain ⟨u, ⟨y, w⟩, s, t⟩ := r
      cases hr
      have gs := (graph_iff f hbot _ _).1 hs
      have gt := (graph_iff f hbot _ _).1 ht
      refine ⟨y, w, hreg, norm_lt_of_inner_lt he h1, ?_, norm_lt_of_inner_lt he h3⟩
      rw [gs.2, gt.2]
      have h5' : t - s < e := h5
      have h4' : s - t < e := h4
      exact abs_lt.2 ⟨by linarith, h4'⟩
  rw [e]
  exact sub_inter (sub_preimage (fun _ => analyticAt_fst) hD)
    (sub_forall_loc hP (sub_of_semi (semi_inter
      (semi_lt (fun _ _ => by fun_prop) (fun _ _ => by fun_prop))
      (semi_le (fun _ _ => by fun_prop) (fun _ _ => by fun_prop)))) fun _ =>
      ⟨Set.univ, Filter.univ_mem, Set.Icc 0 1, Metric.isBounded_Icc _ _,
        fun q hq _ => ⟨hq.1.le, hq.2⟩⟩)

end SubDiff

end SubanalyticLib

/-! SubanalyticLib G9a/G9b (route G9, parent c2c9aa25): norm inequalities and the "near-minimal subgradient"
set `parA` used for curve selection in the proof of BDL Thm 3.1. -/

namespace SubanalyticLib

section ParSet

open Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]

theorem norm_eq_of_sq {w : X} {ρ : ℝ} (h0 : 0 ≤ ρ) (h : ρ ^ 2 = ⟪w, w⟫_ℝ) : ρ = ‖w‖ := by
  rw [real_inner_self_eq_norm_sq] at h
  exact (pow_left_inj₀ h0 (norm_nonneg _) two_ne_zero).1 h

/-- **G9a** `{e | ‖a e‖ ≤ ‖b e‖ + c e}` is subanalytic for analytic `a, b, c`. -/
theorem sub_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {a b : E → X} {c : E → ℝ} (ha : ∀ e, AnalyticAt ℝ a e) (hb : ∀ e, AnalyticAt ℝ b e)
    (hc : ∀ e, AnalyticAt ℝ c e) : IsSubanalytic {e | ‖a e‖ ≤ ‖b e‖ + c e} := by
  set B : Set (E × (ℝ × ℝ)) := {r | 0 ≤ r.2.1} ∩ {r | r.2.1 ^ 2 = ⟪a r.1, a r.1⟫_ℝ} ∩
    {r | 0 ≤ r.2.2} ∩ {r | r.2.2 ^ 2 = ⟪b r.1, b r.1⟫_ℝ} ∩ {r | r.2.1 ≤ r.2.2 + c r.1} with hB
  have haf : ∀ r : E × (ℝ × ℝ), AnalyticAt ℝ (fun r : E × (ℝ × ℝ) => a r.1) r :=
    fun r => (ha r.1).comp analyticAt_fst
  have hbf : ∀ r : E × (ℝ × ℝ), AnalyticAt ℝ (fun r : E × (ℝ × ℝ) => b r.1) r :=
    fun r => (hb r.1).comp analyticAt_fst
  have hcf : ∀ r : E × (ℝ × ℝ), AnalyticAt ℝ (fun r : E × (ℝ × ℝ) => c r.1) r :=
    fun r => (hc r.1).comp analyticAt_fst
  have hBs : IsSubanalytic B := by
    refine sub_of_semi (semi_inter (semi_inter (semi_inter (semi_inter
      (semi_le (fun _ _ => by fun_prop) (fun _ _ => by fun_prop))
      (semi_eq (fun _ _ => by fun_prop) (fun r _ => analyticAt_inner_fun (haf r) (haf r))))
      (semi_le (fun _ _ => by fun_prop) (fun _ _ => by fun_prop)))
      (semi_eq (fun _ _ => by fun_prop) (fun r _ => analyticAt_inner_fun (hbf r) (hbf r))))
      (semi_le (fun _ _ => by fun_prop) (fun r _ => (AnalyticAt.add (by fun_prop) (hcf r)))))
  have e : {e | ‖a e‖ ≤ ‖b e‖ + c e} = Prod.fst '' B := by
    ext e
    constructor
    · intro h
      exact ⟨(e, (‖a e‖, ‖b e‖)), ⟨⟨⟨⟨norm_nonneg _, by simp [real_inner_self_eq_norm_sq]⟩,
        norm_nonneg _⟩, by simp [real_inner_self_eq_norm_sq]⟩, h⟩, rfl⟩
    · rintro ⟨r, ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, rfl⟩
      have e1 := norm_eq_of_sq h1 h2
      have e2 := norm_eq_of_sq h3 h4
      show ‖a r.1‖ ≤ ‖b r.1‖ + c r.1
      rw [← e1, ← e2]; exact h5
  rw [e]
  have hac : Continuous a := continuous_iff_continuousAt.2 fun e => (ha e).continuousAt
  have hbc : Continuous b := continuous_iff_continuousAt.2 fun e => (hb e).continuousAt
  refine sub_proj_loc hBs fun e0 => ?_
  refine ⟨{e | ‖a e‖ < ‖a e0‖ + 1 ∧ ‖b e‖ < ‖b e0‖ + 1},
    IsOpen.mem_nhds ((isOpen_lt hac.norm continuous_const).inter (isOpen_lt hbc.norm continuous_const))
      ⟨lt_add_one _, lt_add_one _⟩,
    Set.Icc 0 (‖a e0‖ + 1) ×ˢ Set.Icc 0 (‖b e0‖ + 1),
    (Metric.isBounded_Icc _ _).prod (Metric.isBounded_Icc _ _), ?_⟩
  rintro r ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩ ⟨ha', hb'⟩
  have e1 := norm_eq_of_sq h1 h2
  have e2 := norm_eq_of_sq h3 h4
  exact ⟨⟨h1, by rw [e1]; exact ha'.le⟩, ⟨h3, by rw [e2]; exact hb'.le⟩⟩

theorem sub_norm_le' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {a : E → X} {c : E → ℝ} (ha : ∀ e, AnalyticAt ℝ a e) (hc : ∀ e, AnalyticAt ℝ c e) :
    IsSubanalytic {e | ‖a e‖ ≤ c e} := by
  simpa using sub_norm_le (b := fun _ => (0 : X)) ha (fun _ => analyticAt_const) hc

/-- the comparison set of G9b: competitors `((x', w'), t')` in the same level shell. -/
def parK (f : X → EReal) (a : X) (ε : ℝ) : Set (((X × X) × ℝ) × ((X × X) × ℝ)) :=
  {r | NonconvexSplitting.Shared.IsRegularSubgrad f r.2.1.1 r.2.1.2} ∩ {r | f r.2.1.1 = (r.2.2 : EReal)} ∩
    {r | ‖r.2.1.1 - a‖ ≤ ε} ∩ {r | ‖r.2.1.2‖ ≤ 2} ∩
    {r | (r.2.2 - (f a).toReal) ^ 2 = (r.1.2 - (f a).toReal) ^ 2}

def parS (f : X → EReal) (a : X) : Set (((X × X) × ℝ) × ((X × X) × ℝ)) :=
  {r | ‖r.1.1.2‖ ≤ ‖r.2.1.2‖ + (r.1.2 - (f a).toReal) ^ 2}

/-- **G9b** the set of near-minimal regular subgradients in the level shell `|f - f a| = s`. -/
def parA (f : X → EReal) (a : X) (ε : ℝ) : Set ((X × X) × ℝ) :=
  {q | NonconvexSplitting.Shared.IsRegularSubgrad f q.1.1 q.1.2} ∩ {q | f q.1.1 = (q.2 : EReal)} ∩
    {q | ‖q.1.1 - a‖ ≤ ε} ∩ {q | 0 < (q.2 - (f a).toReal) ^ 2} ∩ {q | (q.2 - (f a).toReal) ^ 2 < 1} ∩
    {q | ‖q.1.2‖ ≤ 1 + (q.2 - (f a).toReal) ^ 2} ∩
    {q | ∀ z, (q, z) ∈ parK f a ε → (q, z) ∈ parS f a}

theorem sub_parA (f : X → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hcl : IsClosed {x | f x ≠ ⊤}) (hcont : ContinuousOn f {x | f x ≠ ⊤})
    (hsub : IsSubanalyticFn f) (a : X) (ε : ℝ) : IsSubanalytic (parA f a ε) := by
  have hRS := sub_regSub f hbot hcl hcont hsub
  have hK : IsSubanalytic (parK f a ε) := by
    refine sub_inter (sub_inter (sub_inter (sub_inter
      (sub_preimage (Φ := fun r : ((X × X) × ℝ) × ((X × X) × ℝ) => r.2.1) (fun _ => by fun_prop) hRS)
      (sub_graph_pull f hsub (fun _ => by fun_prop) (fun _ => by fun_prop)))
      (sub_norm_le' (fun _ => by fun_prop) (fun _ => by fun_prop)))
      (sub_norm_le' (fun _ => by fun_prop) (fun _ => by fun_prop)))
      (sub_of_semi (semi_eq (fun _ _ => by fun_prop) (fun _ _ => by fun_prop)))
  have hS : IsSubanalytic (parS f a) :=
    sub_norm_le (fun _ => by fun_prop) (fun _ => by fun_prop) (fun _ => by fun_prop)
  obtain ⟨M, hM⟩ := locBdd_toReal f hbot hcl hcont a ε
  have hQ : IsSubanalytic {q : (X × X) × ℝ | ∀ z, (q, z) ∈ parK f a ε → (q, z) ∈ parS f a} := by
    refine sub_forall_loc hS hK fun _ => ⟨Set.univ, Filter.univ_mem,
      (Metric.closedBall a ε ×ˢ Metric.closedBall 0 2) ×ˢ Set.Icc (-M) M,
      (Metric.isBounded_closedBall.prod Metric.isBounded_closedBall).prod (Metric.isBounded_Icc _ _),
      fun r hr _ => ?_⟩
    obtain ⟨⟨⟨⟨-, h2⟩, h3⟩, h4⟩, -⟩ := hr
    have g := (graph_iff f hbot _ _).1 h2
    have b := hM _ (by rw [Metric.mem_closedBall, dist_eq_norm]; exact h3) g.1
    rw [g.2] at b
    refine ⟨⟨?_, ?_⟩, abs_le.1 b⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]; exact h3
    · rw [Metric.mem_closedBall, dist_zero_right]; exact h4
  refine sub_inter (sub_inter (sub_inter (sub_inter (sub_inter (sub_inter
    (sub_preimage (Φ := fun q : (X × X) × ℝ => q.1) (fun _ => by fun_prop) hRS)
    (sub_graph_pull f hsub (fun _ => by fun_prop) (fun _ => by fun_prop)))
    (sub_norm_le' (fun _ => by fun_prop) (fun _ => by fun_prop)))
    (sub_of_semi (semi_lt (fun _ _ => by fun_prop) (fun _ _ => by fun_prop))))
    (sub_of_semi (semi_lt (fun _ _ => by fun_prop) (fun _ _ => by fun_prop))))
    (sub_norm_le' (fun _ => by fun_prop) (fun _ => by fun_prop))) hQ

/-- **G9c** the inequality for regular subgradients on a ball passes to limiting subgradients. -/
theorem lim_of_reg (f : X → EReal) (hbot : ∀ x, f x ≠ ⊥) (a : X) {θ C r : ℝ} (hθ : 0 < θ)
    (H : ∀ x ∈ Metric.ball a r, ∀ w, NonconvexSplitting.Shared.IsRegularSubgrad f x w →
      |(f x).toReal - (f a).toReal| ^ θ ≤ C * ‖w‖) :
    ∀ x ∈ Metric.ball a r, ∀ v ∈ NonconvexSplitting.Shared.LimitingSubdiff f x,
      |(f x).toReal - (f a).toReal| ^ θ ≤ C * ‖v‖ := by
  rintro x hx v ⟨hfx, xs, vs, h1, h2, h3, h4⟩
  have g2 : Tendsto (fun t => (f (xs t)).toReal) atTop (𝓝 (f x).toReal) :=
    (EReal.tendsto_toReal hfx (hbot x)).comp h2
  have hl : Tendsto (fun t => |(f (xs t)).toReal - (f a).toReal| ^ θ) atTop
      (𝓝 (|(f x).toReal - (f a).toReal| ^ θ)) :=
    ((g2.sub_const _).abs).rpow_const (Or.inr hθ.le)
  have hr : Tendsto (fun t => C * ‖vs t‖) atTop (𝓝 (C * ‖v‖)) := (h3.norm).const_mul C
  refine le_of_tendsto_of_tendsto hl hr ?_
  filter_upwards [h1.eventually (Metric.isOpen_ball.mem_nhds hx)] with t ht
  exact H _ ht _ (h4 t)

/-- **G9d-1** a regular subgradient of norm `< 1` in the shell `s ∈ (0,1)` yields a `parA` point in that shell. -/
theorem parA_of_small (f : X → EReal) (hbot : ∀ x, f x ≠ ⊥) (a : X) (ε : ℝ) {x w : X}
    (hreg : NonconvexSplitting.Shared.IsRegularSubgrad f x w) (hxa : ‖x - a‖ ≤ ε)
    (hs0 : 0 < ((f x).toReal - (f a).toReal) ^ 2) (hs1 : ((f x).toReal - (f a).toReal) ^ 2 < 1)
    (hw : ‖w‖ < 1) :
    ∃ q ∈ parA f a ε, (q.2 - (f a).toReal) ^ 2 = ((f x).toReal - (f a).toReal) ^ 2 := by
  set s2 := ((f x).toReal - (f a).toReal) ^ 2 with hs2
  set F : Set ℝ := {r | ∃ x' w' : X, NonconvexSplitting.Shared.IsRegularSubgrad f x' w' ∧
    ‖x' - a‖ ≤ ε ∧ ‖w'‖ ≤ 2 ∧ ((f x').toReal - (f a).toReal) ^ 2 = s2 ∧ r = ‖w'‖} with hF
  have hwF : ‖w‖ ∈ F := ⟨x, w, hreg, hxa, by linarith, rfl, rfl⟩
  have hbdd : BddBelow F := ⟨0, by rintro r ⟨_, _, _, _, _, _, rfl⟩; exact norm_nonneg _⟩
  have hm : sInf F ≤ ‖w‖ := csInf_le hbdd hwF
  obtain ⟨r, ⟨x'', w'', hreg'', hxa'', hw2'', hs'', rfl⟩, hlt⟩ :=
    exists_lt_of_csInf_lt ⟨_, hwF⟩ (lt_add_of_pos_right (sInf F) hs0)
  refine ⟨((x'', w''), (f x'').toReal), ⟨⟨⟨⟨⟨⟨hreg'', ?_⟩, hxa''⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, hs''⟩
  · exact (EReal.coe_toReal hreg''.1 (hbot _)).symm
  · show 0 < ((f x'').toReal - (f a).toReal) ^ 2; rw [hs'']; exact hs0
  · show ((f x'').toReal - (f a).toReal) ^ 2 < 1; rw [hs'']; exact hs1
  · show ‖w''‖ ≤ 1 + ((f x'').toReal - (f a).toReal) ^ 2
    rw [hs'']; linarith
  · rintro ⟨⟨x', w'⟩, t'⟩ ⟨⟨⟨⟨hr1, hr2⟩, hr3⟩, hr4⟩, hr5⟩
    have g := (graph_iff f hbot _ _).1 hr2
    have hr5' : (t' - (f a).toReal) ^ 2 = ((f x'').toReal - (f a).toReal) ^ 2 := hr5
    have hmem : ‖w'‖ ∈ F := ⟨x', w', hr1, hr3, hr4, by rw [g.2, hr5', hs''], rfl⟩
    have := csInf_le hbdd hmem
    show ‖w''‖ ≤ ‖w'‖ + ((f x'').toReal - (f a).toReal) ^ 2
    rw [hs'']; linarith

/-- **G9d-2** a one-variable analytic germ vanishing at `0` but not on `(0, δ)`: power upper bound
for `σ` and the matching lower bound for `σ'`. -/
theorem germ_lower {σ : ℝ → ℝ} (hσ : AnalyticAt ℝ σ 0) (h0 : σ 0 = 0) {δ : ℝ} (hδ : 0 < δ)
    (hne : ∀ u ∈ Set.Ioo 0 δ, σ u ≠ 0) :
    ∃ p : ℕ, 1 ≤ p ∧ ∃ c > 0, ∃ δ1 > 0, ∀ u ∈ Set.Ioo 0 δ1,
      |σ u| ≤ c * u ^ p ∧ (1 / c) * u ^ (p - 1) ≤ |deriv σ u| ∧ DifferentiableAt ℝ σ u := by
  have hnot : ¬ ∀ᶠ z in 𝓝 (0 : ℝ), σ z = 0 := by
    intro h
    obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff.1 h
    have hu : min r δ / 2 ∈ Set.Ioo 0 δ := ⟨by positivity, by
      have := min_le_right r δ; linarith [lt_min hr hδ]⟩
    refine hne _ hu (hr' ?_)
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    have := min_le_left r δ; linarith [lt_min hr hδ]
  obtain ⟨p, h, hh, hh0, hev⟩ := hσ.exists_eventuallyEq_pow_smul_nonzero_iff.2 hnot
  have hp : 1 ≤ p := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · exfalso; apply hh0
      have := hev.self_of_nhds
      simp [hp] at this
      rw [← this, h0]
    · exact hp
  set A0 := |h 0| with hA0
  have hA0p : 0 < A0 := abs_pos.2 hh0
  set k : ℝ → ℝ := fun z => (p : ℝ) * h z + z * deriv h z with hk
  have hkc : ContinuousAt k 0 :=
    (continuousAt_const.mul hh.continuousAt).add (continuousAt_id.mul hh.deriv.continuousAt)
  have hk0 : k 0 = p * h 0 := by simp [hk]
  have hpk : A0 ≤ |k 0| := by
    rw [hk0, abs_mul, Nat.abs_cast]
    exact le_mul_of_one_le_left (abs_nonneg _) (by exact_mod_cast hp)
  have e1 : ∀ᶠ z in 𝓝 (0 : ℝ), A0 / 2 ≤ |k z| := by
    have := hkc.norm.eventually (lt_mem_nhds (show ‖k 0‖ / 2 < ‖k 0‖ by
      simp only [Real.norm_eq_abs]; linarith))
    filter_upwards [this] with z hz
    simp only [Real.norm_eq_abs] at hz
    linarith
  have e2 : ∀ᶠ z in 𝓝 (0 : ℝ), |h z| ≤ 2 * A0 := by
    have := hh.continuousAt.norm.eventually (gt_mem_nhds (show ‖h 0‖ < 2 * A0 by
      simp only [Real.norm_eq_abs]; linarith))
    filter_upwards [this] with z hz
    simp only [Real.norm_eq_abs] at hz
    exact hz.le
  have e3 := hh.eventually_analyticAt
  obtain ⟨r, hr, hall⟩ := Metric.eventually_nhds_iff.1 ((hev.and e1).and (e2.and e3))
  set c := 2 * A0 + 2 / A0 with hc
  have hcpos : 0 < c := by positivity
  refine ⟨p, hp, c, hcpos, r, hr, fun u hu => ?_⟩
  have hur : dist u 0 < r := by rw [Real.dist_eq, sub_zero, abs_of_pos hu.1]; exact hu.2
  obtain ⟨⟨-, hku⟩, hhu, hau⟩ := hall hur
  have hball : Metric.ball (0 : ℝ) r ∈ 𝓝 u := Metric.isOpen_ball.mem_nhds hur
  have heq : σ =ᶠ[𝓝 u] fun z => z ^ p * h z := by
    filter_upwards [hball] with z hz
    have := (hall hz).1.1
    simpa [smul_eq_mul] using this
  have hd : HasDerivAt (fun z => z ^ p * h z)
      ((p : ℝ) * u ^ (p - 1) * h u + u ^ p * deriv h u) u :=
    (hasDerivAt_pow p u).mul hau.differentiableAt.hasDerivAt
  have hdσ : HasDerivAt σ ((p : ℝ) * u ^ (p - 1) * h u + u ^ p * deriv h u) u :=
    hd.congr_of_eventuallyEq heq
  have hup : u ^ p = u ^ (p - 1) * u := by
    rw [← pow_succ, Nat.sub_add_cancel hp]
  have hderiv : deriv σ u = u ^ (p - 1) * k u := by
    rw [hdσ.deriv, hup]; simp only [hk]; ring
  have hu0 : 0 ≤ u ^ (p - 1) := pow_nonneg hu.1.le _
  refine ⟨?_, ?_, hdσ.differentiableAt⟩
  · rw [heq.self_of_nhds, abs_mul, abs_of_nonneg (pow_nonneg hu.1.le _)]
    have : 2 * A0 ≤ c := by rw [hc]; linarith [div_pos two_pos hA0p]
    calc u ^ p * |h u| ≤ u ^ p * (2 * A0) := mul_le_mul_of_nonneg_left hhu (pow_nonneg hu.1.le _)
      _ ≤ c * u ^ p := by nlinarith [pow_nonneg hu.1.le p]
  · rw [hderiv, abs_mul, abs_of_nonneg hu0]
    have h1c : 1 / c ≤ A0 / 2 := by
      rw [div_le_div_iff₀ hcpos two_pos, hc]
      have : A0 * (2 / A0) = 2 := by field_simp
      nlinarith [sq_nonneg A0]
    calc 1 / c * u ^ (p - 1) ≤ A0 / 2 * u ^ (p - 1) := mul_le_mul_of_nonneg_right h1c hu0
      _ ≤ u ^ (p - 1) * |k u| := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hku hu0

/-- **G9d-3** along an analytic arc of `parA` starting on the level `f a`, the shells `s ∈ (0, s1)` all
contain a `parA` point whose subgradient satisfies `s ^ θ ≤ K ‖w‖`, with `θ = 1 - 1/(2p) < 1`. -/
theorem arc_step (f : X → EReal) (a : X) (ε : ℝ) {γ : ℝ → (X × X) × ℝ} (hγ : AnalyticAt ℝ γ 0)
    (hγ0 : (γ 0).2 = (f a).toReal) {ε0 : ℝ} (hε0 : 0 < ε0)
    (hA : ∀ u ∈ Set.Ioo 0 ε0, γ u ∈ parA f a ε) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ K > 0, ∃ s1 > 0, ∀ s ∈ Set.Ioo 0 s1, ∃ q ∈ parA f a ε,
      (q.2 - (f a).toReal) ^ 2 = s ^ 2 ∧ s ^ θ ≤ K * ‖q.1.2‖ := by
  set ga := (f a).toReal with hga
  set σ : ℝ → ℝ := fun u => (γ u).2 - ga with hσ
  have hσa : AnalyticAt ℝ σ 0 := (AnalyticAt.snd' hγ).sub analyticAt_const
  have hσ0 : σ 0 = 0 := by simp [hσ, hγ0]
  have hσne : ∀ u ∈ Set.Ioo 0 ε0, σ u ≠ 0 := by
    intro u hu h
    have := (hA u hu).1.1.1.2
    simp only [Set.mem_setOf_eq] at this
    have h' : (γ u).2 - ga = 0 := h
    rw [h'] at this; simp at this
  obtain ⟨p, hp, c, hc, δ1, hδ1, hσb⟩ := germ_lower hσa hσ0 hε0 hσne
  set g1 : ℝ → X := fun u => (γ u).1.1 with hg1
  have hg1a : AnalyticAt ℝ g1 0 := AnalyticAt.fst' (AnalyticAt.fst' hγ)
  have hdc : ContinuousAt (deriv g1) 0 := hg1a.deriv.continuousAt
  set L := ‖deriv g1 0‖ + 1 with hL
  have hLp : 0 < L := by positivity
  have eL : ∀ᶠ u in 𝓝 (0 : ℝ), ‖deriv g1 u‖ ≤ L :=
    (hdc.norm.eventually (gt_mem_nhds (lt_add_one _))).mono fun _ h => h.le
  obtain ⟨r, hr, hall⟩ := Metric.eventually_nhds_iff.1 (eL.and hγ.eventually_analyticAt)
  set δ2 := min (min δ1 ε0) (min r 1) with hδ2
  have hδ2p : 0 < δ2 := lt_min (lt_min hδ1 hε0) (lt_min hr one_pos)
  have hδ2a : δ2 ≤ δ1 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2b : δ2 ≤ ε0 := (min_le_left _ _).trans (min_le_right _ _)
  have hδ2c : δ2 ≤ r := (min_le_right _ _).trans (min_le_left _ _)
  have hδ2d : δ2 ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  set θ : ℝ := 1 - 1 / (2 * p) with hθ
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hθ0 : 0 < θ := by
    rw [hθ, sub_pos, div_lt_one (by positivity)]; linarith
  have hθ1 : θ < 1 := by rw [hθ]; have : 0 < 1 / (2 * (p : ℝ)) := by positivity
                         linarith
  set K := c ^ θ * (c * L) with hK
  have hKp : 0 < K := by positivity
  -- the key pointwise bound along the arc
  have key : ∀ u ∈ Set.Ioo 0 δ2, |σ u| ^ θ ≤ K * ‖(γ u).1.2‖ := by
    intro u hu
    have hu1 : u ∈ Set.Ioo 0 δ1 := ⟨hu.1, hu.2.trans_le hδ2a⟩
    have hue : u ∈ Set.Ioo 0 ε0 := ⟨hu.1, hu.2.trans_le hδ2b⟩
    have hur : dist u 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hu.1]; exact hu.2.trans_le hδ2c
    obtain ⟨hLu, hau⟩ := hall hur
    obtain ⟨hup, hlow, hdiff⟩ := hσb u hu1
    have hφ : HasDerivAt (fun v => (γ v).2) (deriv σ u) u := by
      have := hdiff.hasDerivAt
      have h2 : HasDerivAt (fun v => σ v + ga) (deriv σ u) u := this.add_const ga
      simpa [hσ] using h2
    have hfφ : ∀ᶠ v in 𝓝 u, f (g1 v) = ((γ v).2 : EReal) := by
      filter_upwards [isOpen_Ioo.mem_nhds hue] with v hv
      exact (hA v hv).1.1.1.1.1.2
    have hch := regular_subgrad_chain (AnalyticAt.fst' (AnalyticAt.fst' hau)).differentiableAt.hasDerivAt hφ hfφ
      (hA u hue).1.1.1.1.1.1
    have hdb : |deriv σ u| ≤ ‖(γ u).1.2‖ * L := by
      rw [hch]
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left hLu (norm_nonneg _))
    have hu0 := hu.1
    have hu1' : u ≤ 1 := (hu.2.trans_le hδ2d).le
    -- |σ u| ^ θ ≤ (c u^p)^θ = c^θ u^(p-1/2) ≤ c^θ u^(p-1) ≤ c^θ c L ‖w‖
    have s1 : |σ u| ^ θ ≤ (c * u ^ p) ^ θ :=
      Real.rpow_le_rpow (abs_nonneg _) hup hθ0.le
    have s2 : (c * u ^ p) ^ θ = c ^ θ * u ^ ((p : ℝ) * θ) := by
      rw [Real.mul_rpow hc.le (pow_nonneg hu0.le _), Real.rpow_natCast_mul hu0.le]
    have s3 : u ^ ((p : ℝ) * θ) ≤ u ^ (((p - 1 : ℕ) : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_ge hu0 hu1'
      have hpθ : (p : ℝ) * (1 - 1 / (2 * p)) = p - 1 / 2 := by field_simp
      rw [Nat.cast_sub hp, Nat.cast_one, hθ, hpθ]; linarith
    have s4 : u ^ (((p - 1 : ℕ) : ℝ)) ≤ c * L * ‖(γ u).1.2‖ := by
      rw [Real.rpow_natCast]
      have := hlow.trans hdb
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hc] at this
      nlinarith [norm_nonneg (γ u).1.2]
    calc |σ u| ^ θ ≤ c ^ θ * u ^ ((p : ℝ) * θ) := s1.trans s2.le
      _ ≤ c ^ θ * (c * L * ‖(γ u).1.2‖) :=
          mul_le_mul_of_nonneg_left (s3.trans s4) (Real.rpow_nonneg hc.le _)
      _ = K * ‖(γ u).1.2‖ := by rw [hK]; ring
  -- intermediate values
  have hcont : ContinuousOn (fun u => |σ u|) (Set.Icc 0 (δ2 / 2)) := by
    intro u hu
    have hur : dist u 0 < r := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hu.1]
      linarith [hu.2, hδ2c]
    exact ((AnalyticAt.snd' (hall hur).2).continuousAt.sub continuousAt_const).abs.continuousWithinAt
  have hmid : δ2 / 2 ∈ Set.Ioo 0 δ2 := ⟨by positivity, by linarith⟩
  set s1 := |σ (δ2 / 2)| with hs1
  have hs1p : 0 < s1 := abs_pos.2 (hσne _ ⟨hmid.1, hmid.2.trans_le hδ2b⟩)
  refine ⟨θ, hθ0, hθ1, K, hKp, s1, hs1p, fun s hs => ?_⟩
  have hivt := intermediate_value_Icc (show (0 : ℝ) ≤ δ2 / 2 by positivity) hcont
  obtain ⟨u, hu, hus0⟩ := hivt ⟨by show |σ 0| ≤ s; rw [hσ0, abs_zero]; exact hs.1.le, hs.2.le⟩
  have hus : |σ u| = s := hus0
  have hu0 : u ≠ 0 := by
    rintro rfl; rw [hσ0, abs_zero] at hus; linarith [hs.1]
  have huI : u ∈ Set.Ioo 0 δ2 := ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0), by linarith [hu.2]⟩
  refine ⟨γ u, hA u ⟨huI.1, huI.2.trans_le hδ2b⟩, ?_, ?_⟩
  · rw [← hus, sq_abs]
  · rw [← hus]; exact key u huI

end ParSet

end SubanalyticLib

/-! SubanalyticLib G9d-4 (route G9, parent c2c9aa25): assembly of BDL Thm 3.1 for regular subgradients
on a ball, from curve selection on `parA` (case 2) or a uniform gap (case 1). -/

namespace SubanalyticLib

section MainLoj

open Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]

/-- continuity of `toReal ∘ f` at a finite point, on the domain. -/
theorem near_level (f : X → EReal) (hbot : ∀ x, f x ≠ ⊥) (hcont : ContinuousOn f {x | f x ≠ ⊤})
    {a : X} (ha : f a ≠ ⊤) {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, r ≤ 1 ∧ ∀ x, dist x a < r → f x ≠ ⊤ → |(f x).toReal - (f a).toReal| < η := by
  have ht : Tendsto (fun x => (f x).toReal) (𝓝[{x | f x ≠ ⊤}] a) (𝓝 (f a).toReal) :=
    (EReal.tendsto_toReal ha (hbot a)).comp (hcont a ha)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.tendsto_nhdsWithin_nhds.1 ht η hη
  refine ⟨min δ 1, lt_min hδ one_pos, min_le_right _ _, fun x hx hfx => ?_⟩
  have := hδ' (x := x) hfx (lt_of_lt_of_le hx (min_le_left _ _))
  rwa [Real.dist_eq] at this

/-- case 2 set-up: `parA` points with level tending to `f a` accumulate at a point of level `f a`. -/
theorem exists_closure_level (f : X → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hcl : IsClosed {x | f x ≠ ⊤}) (hcont : ContinuousOn f {x | f x ≠ ⊤}) (a : X)
    (h : ∀ s1 : ℝ, 0 < s1 → ∃ q ∈ parA f a 1, (q.2 - (f a).toReal) ^ 2 < s1 ^ 2) :
    ∃ q0 ∈ closure (parA f a 1), q0.2 = (f a).toReal := by
  choose q hq hlt using fun k : ℕ => h (1 / ((k : ℝ) + 1)) (by positivity)
  obtain ⟨M, hM⟩ := locBdd_toReal f hbot hcl hcont a 1
  set Kc : Set ((X × X) × ℝ) :=
    (Metric.closedBall a 1 ×ˢ Metric.closedBall (0 : X) 2) ×ˢ Set.Icc (-M) M with hKc
  have hKcc : IsCompact Kc :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).prod isCompact_Icc
  have hmem : ∀ k, q k ∈ Kc := by
    intro k
    obtain ⟨⟨⟨⟨⟨⟨-, h2⟩, h3⟩, -⟩, h5⟩, h6⟩, -⟩ := hq k
    have g := (graph_iff f hbot _ _).1 h2
    have hb := hM _ (by rw [Metric.mem_closedBall, dist_eq_norm]; exact h3) g.1
    rw [g.2] at hb
    have h5' : ((q k).2 - (f a).toReal) ^ 2 < 1 := h5
    have h6' : ‖(q k).1.2‖ ≤ 1 + ((q k).2 - (f a).toReal) ^ 2 := h6
    refine ⟨⟨?_, ?_⟩, abs_le.1 hb⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]; exact h3
    · rw [Metric.mem_closedBall, dist_zero_right]; linarith
  obtain ⟨q0, -, φ, hφ, hlim⟩ := hKcc.tendsto_subseq hmem
  refine ⟨q0, mem_closure_of_tendsto hlim (Eventually.of_forall fun k => hq (φ k)), ?_⟩
  have t1 : Tendsto (fun k => (q (φ k)).2) atTop (𝓝 q0.2) :=
    (continuous_snd.tendsto _).comp hlim
  have t2 : Tendsto (fun k => (q k).2) atTop (𝓝 (f a).toReal) := by
    apply tendsto_of_norm_lt_inv
    intro k
    rw [Real.norm_eq_abs]
    exact abs_lt_of_sq_lt_sq (hlt k) (by positivity)
  exact tendsto_nhds_unique t1 (t2.comp hφ.tendsto_atTop)

/-- **G9d-4** BDL Thm 3.1 for regular subgradients on a ball around a finite point. -/
theorem loj_reg (hCS : CurveSelection ((X × X) × ℝ)) (f : X → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hcl : IsClosed {x | f x ≠ ⊤}) (hcont : ContinuousOn f {x | f x ≠ ⊤})
    (hsub : IsSubanalyticFn f) (a : X) (ha : f a ≠ ⊤) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∃ C r : ℝ, 0 < r ∧
      ∀ x ∈ Metric.ball a r, ∀ w, NonconvexSplitting.Shared.IsRegularSubgrad f x w →
        |(f x).toReal - (f a).toReal| ^ θ ≤ C * ‖w‖ := by
  by_cases hcase : ∃ s1 : ℝ, 0 < s1 ∧ ∀ q ∈ parA f a 1, s1 ^ 2 ≤ (q.2 - (f a).toReal) ^ 2
  · -- CASE 1: a uniform gap below the levels of `parA`
    obtain ⟨s1, hs1, hgap⟩ := hcase
    obtain ⟨r, hr, hr1, hnear⟩ := near_level f hbot hcont ha (lt_min hs1 one_pos)
    refine ⟨1 / 2, by norm_num, by norm_num, 1, r, hr, fun x hx w hw => ?_⟩
    have hfx : f x ≠ ⊤ := hw.1
    have hlt := hnear x hx hfx
    have hlt1 : |(f x).toReal - (f a).toReal| < 1 := hlt.trans_le (min_le_right _ _)
    have hlts : |(f x).toReal - (f a).toReal| < s1 := hlt.trans_le (min_le_left _ _)
    have hle1 : |(f x).toReal - (f a).toReal| ^ (1 / 2 : ℝ) ≤ 1 :=
      Real.rpow_le_one (abs_nonneg _) hlt1.le (by norm_num)
    rcases le_or_gt 1 ‖w‖ with hw1 | hw1
    · rw [one_mul]; exact hle1.trans hw1
    rcases eq_or_lt_of_le (abs_nonneg ((f x).toReal - (f a).toReal)) with h0 | h0
    · rw [← h0, Real.zero_rpow (by norm_num)]; positivity
    exfalso
    have hxa : ‖x - a‖ ≤ 1 := by
      rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hx).le.trans hr1
    have hs0 : 0 < ((f x).toReal - (f a).toReal) ^ 2 := by rw [← sq_abs]; positivity
    have hs1' : ((f x).toReal - (f a).toReal) ^ 2 < 1 := by
      rw [← sq_abs]; nlinarith [abs_nonneg ((f x).toReal - (f a).toReal)]
    obtain ⟨q, hqA, hqs⟩ := parA_of_small f hbot a 1 hw hxa hs0 hs1' hw1
    have h1 := hgap q hqA
    rw [hqs] at h1
    have h' := pow_lt_pow_left₀ hlts (abs_nonneg _) two_ne_zero
    rw [sq_abs] at h'
    linarith
  · -- CASE 2: levels of `parA` accumulate at `f a`; curve selection gives an arc
    have h2 : ∀ s1 : ℝ, 0 < s1 → ∃ q ∈ parA f a 1, (q.2 - (f a).toReal) ^ 2 < s1 ^ 2 := by
      intro s1 hs1
      by_contra hn
      push_neg at hn
      exact hcase ⟨s1, hs1, hn⟩
    obtain ⟨q0, hq0, hq02⟩ := exists_closure_level f hbot hcl hcont a h2
    obtain ⟨γ, hγ, hγ0, ε0, hε0, hγA⟩ := hCS _ (sub_parA f hbot hcl hcont hsub a 1) q0 hq0
    obtain ⟨θ, hθ0, hθ1, K, hK, s1, hs1, hstep⟩ :=
      arc_step f a 1 hγ (by rw [hγ0, hq02]) hε0 hγA
    set η := min s1 (min (1 / (2 * K)) 1) with hη
    have hηp : 0 < η := lt_min hs1 (lt_min (by positivity) one_pos)
    obtain ⟨r, hr, hr1, hnear⟩ := near_level f hbot hcont ha hηp
    refine ⟨θ, hθ0, hθ1, max (2 * K) 1, r, hr, fun x hx w hw => ?_⟩
    have hfx : f x ≠ ⊤ := hw.1
    have hlt := hnear x hx hfx
    generalize hs : |(f x).toReal - (f a).toReal| = s at hlt ⊢
    have hlt1 : s < 1 := hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hltK : s < 1 / (2 * K) := hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hlts : s < s1 := hlt.trans_le (min_le_left _ _)
    have hC1 : 1 ≤ max (2 * K) 1 := le_max_right _ _
    have hCK : 2 * K ≤ max (2 * K) 1 := le_max_left _ _
    rcases eq_or_lt_of_le (hs ▸ abs_nonneg ((f x).toReal - (f a).toReal) : 0 ≤ s) with h0 | h0
    · rw [← h0, Real.zero_rpow hθ0.ne']; positivity
    have hsp : 0 < s := h0
    have hle1 : s ^ θ ≤ 1 := Real.rpow_le_one hsp.le hlt1.le hθ0.le
    rcases lt_or_ge 2 ‖w‖ with hw2 | hw2
    · nlinarith
    obtain ⟨q, hqA, hqs, hqK⟩ := hstep s ⟨hsp, hlts⟩
    have hxa : ‖x - a‖ ≤ 1 := by
      rw [← dist_eq_norm]; exact (Metric.mem_ball.1 hx).le.trans hr1
    have hK' : (q, ((x, w), (f x).toReal)) ∈ parK f a 1 := by
      refine ⟨⟨⟨⟨hw, (EReal.coe_toReal hfx (hbot x)).symm⟩, hxa⟩, hw2⟩, ?_⟩
      show ((f x).toReal - (f a).toReal) ^ 2 = (q.2 - (f a).toReal) ^ 2
      rw [hqs, ← hs, sq_abs]
    have hS : ‖q.1.2‖ ≤ ‖w‖ + (q.2 - (f a).toReal) ^ 2 := hqA.2 _ hK'
    rw [hqs] at hS
    have hsθ : s ≤ s ^ θ := by
      have := Real.rpow_le_rpow_of_exponent_ge hsp hlt1.le hθ1.le
      rwa [Real.rpow_one] at this
    have hKs : K * s ≤ 1 / 2 := by
      have h1 := mul_lt_mul_of_pos_left hltK hK
      have e : K * (1 / (2 * K)) = 1 / 2 := by
        rw [mul_one_div, div_eq_iff (by positivity)]; ring
      rw [e] at h1
      linarith
    have hs2 : K * s ^ 2 ≤ s ^ θ / 2 := by
      have : K * s ^ 2 = (K * s) * s := by ring
      rw [this]; nlinarith
    have hmain : s ^ θ ≤ 2 * K * ‖w‖ := by
      have := hqK.trans (mul_le_mul_of_nonneg_left hS hK.le)
      nlinarith
    exact hmain.trans (mul_le_mul_of_nonneg_right hCK (norm_nonneg _))

end MainLoj

end SubanalyticLib

end TopOpen

open NonsmoothLojasiewicz.Continuous in
/-- dev assembly of the leaf from `loj_reg` (curve selection supplied by the library). -/
theorem solution_dev (hCS : ∀ n : ℕ, SubanalyticLib.CurveSelection
      ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ))
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hf : ∀ x, f x ≠ ⊥)
    (hdom : IsClosed {x | f x ≠ ⊤}) (hcont : ContinuousOn f {x | f x ≠ ⊤})
    (hsub : IsSubanalyticFn f) (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ crit f) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ LojIneqAt f a θ := by
  obtain ⟨θ, hθ0, hθ1, C, r, hr, H⟩ := SubanalyticLib.loj_reg (hCS n) f hf hdom hcont hsub a ha.1
  exact ⟨θ, hθ0.le, hθ1, C, Metric.ball a r, Metric.ball_mem_nhds a hr,
    SubanalyticLib.lim_of_reg f hf a hθ0 H⟩

open Filter Topology in
open scoped ENNReal in
open NonsmoothLojasiewicz.Continuous in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hf : ∀ x, f x ≠ ⊥)
    (hdom : IsClosed {x | f x ≠ ⊤}) (hcont : ContinuousOn f {x | f x ≠ ⊤})
    (hsub : IsSubanalyticFn f) (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ crit f) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ LojIneqAt f a θ := by
  exact solution_dev (fun m A hA x₀ hx₀ =>
    NonsmoothLojasiewicz.Continuous.subanalytic_curve_selection A hA x₀ hx₀) f hf hdom hcont hsub a ha
