-- Prove2me | solution 1 for NonsmoothLojasiewicz.Convex.prop213_crit_isSubanalytic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T07:00:22.618607+00:00
-- url     : https://prove2.me/submissions/8a9ea867-9bd0-4a6b-9480-496ababb8e00

import Mathlib
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonsmoothLojasiewicz_Convex_crit
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
    (hrb : ∀ B : Set X, Bornology.IsBounded B → ∃ M : ℝ, ∀ x ∈ B, f x ≠ ⊤ → |(f x).toReal| ≤ M) (x0 : X) (r : ℝ) :
    ∃ M : ℝ, ∀ x ∈ Metric.closedBall x0 r, f x ≠ ⊤ → |(f x).toReal| ≤ M :=
  hrb _ Metric.isBounded_closedBall

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
    (hrb : ∀ B : Set X, Bornology.IsBounded B → ∃ M : ℝ, ∀ x ∈ B, f x ≠ ⊤ → |(f x).toReal| ≤ M)
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
  obtain ⟨M, hM⟩ := locBdd_toReal f hbot hrb x0 1
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
    (hrb : ∀ B : Set X, Bornology.IsBounded B → ∃ M : ℝ, ∀ x ∈ B, f x ≠ ⊤ → |(f x).toReal| ≤ M)
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
  obtain ⟨M1, hM1⟩ := locBdd_toReal f hbot hrb q0.1.1.1.1 1
  obtain ⟨M2, hM2⟩ := locBdd_toReal f hbot hrb q0.2 1
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
    (hrb : ∀ B : Set X, Bornology.IsBounded B → ∃ M : ℝ, ∀ x ∈ B, f x ≠ ⊤ → |(f x).toReal| ≤ M)
    (hsub : IsSubanalyticFn f) :
    IsSubanalytic {u : X × X | NonconvexSplitting.Shared.IsRegularSubgrad f u.1 u.2} := by
  have hD := sub_dom f hbot hrb hsub
  have hK : IsSubanalytic (regK f) := by
    refine sub_inter (sub_of_semi ?_) (sub_preimage (fun _ => analyticAt_snd) hD)
    refine semi_inter (semi_inter (semi_lt (fun _ _ => analyticAt_inner_fun (by fun_prop) (by fun_prop))
      (fun _ _ => by fun_prop)) (semi_lt (fun _ _ => by fun_prop) (fun _ _ => by fun_prop)))
      (semi_le (fun _ _ => by fun_prop) (fun _ _ => by fun_prop))
  have hQ1 : IsSubanalytic {w : ((X × X) × ℝ) × ℝ | ∀ z, (w, z) ∈ regK f → (w, z) ∈ regP f} := by
    refine sub_forall_loc (sub_regP f hbot hrb hsub) hK fun w0 => ?_
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
    (hrb : ∀ B : Set X, Bornology.IsBounded B → ∃ M : ℝ, ∀ x ∈ B, f x ≠ ⊤ → |(f x).toReal| ≤ M)
    (hsub : IsSubanalyticFn f) :
    IsSubanalytic {u : X × X | u.2 ∈ NonconvexSplitting.Shared.LimitingSubdiff f u.1} := by
  have hD := sub_dom f hbot hrb hsub
  have hRS := sub_regSub f hbot hrb hsub
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
    obtain ⟨M, hM⟩ := locBdd_toReal f hbot hrb p0.1.1 R
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

end TopOpen

open Filter Topology in
open NonconvexSplitting.Shared in
open NonsmoothLojasiewicz.Convex in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hbot : ∀ x, f x ≠ ⊥) (hsub : NonsmoothLojasiewicz.Continuous.IsSubanalyticFn f)
    (hrb : ∀ B : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded B →
      ∃ M : ℝ, ∀ x ∈ B, f x ≠ ⊤ → |(f x).toReal| ≤ M) :
    NonsmoothLojasiewicz.Continuous.IsSubanalytic (crit f) := by
  have hL := SubanalyticLib.sub_limSub f hbot hrb hsub
  have e : crit f = (fun x : EuclideanSpace ℝ (Fin n) => (x, (0 : EuclideanSpace ℝ (Fin n)))) ⁻¹'
      {u : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
        u.2 ∈ NonconvexSplitting.Shared.LimitingSubdiff f u.1} := rfl
  rw [e]
  exact SubanalyticLib.sub_preimage (fun x => analyticAt_id.prod analyticAt_const) hL
