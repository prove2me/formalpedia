-- Prove2me | solution 1 for GlobalTheory.KeyKa.KoszulCx.isCx_kosD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:50:15.398808+00:00
-- url     : https://prove2.me/submissions/e4f13c1d-f7cf-4d00-a146-1936b6b4abdc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignInsert
import Theorems.Thm_GlobalTheory_KeyKa_KoszulCx_sign_insert
import Theorems.Thm_GlobalTheory_KeyKa_KoszulCx_kosD_deg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KoszulCx
variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}
namespace GlobalTheory.KeyKa.KoszulCx
theorem _root_.solution (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (hc : ∀ i i' j, j + 2 ≤ g → m i j (j + 1) * m i' (j + 1) (j + 2) = m i' j (j + 1) * m i (j + 1) (j + 2))
    (he : ∀ i, ev 0 * m i 0 (0 + 1) = 0) : IsCx kdeg (kosD m ev) := by
  have hc' : ∀ i i' j j₁ j₁' j₂, j₁ = j + 1 → j₁' = j + 1 → j₂ = j + 2 → j₂ ≤ g →
      m i j j₁ * m i' j₁ j₂ = m i' j j₁' * m i j₁' j₂ := by
    rintro i i' j _ _ _ rfl rfl rfl h
    exact hc i i' j h
  have he' : ∀ i j j₁, j = 0 → j₁ = 0 + 1 → ev j * m i j j₁ = 0 := by
    rintro i _ _ rfl rfl
    exact he i
  refine ⟨kosD_deg m ev, ?_⟩
  ext p r
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.zero_apply]
  rcases r with ⟨K, c⟩ | r
  swap
  · rcases p with p | p <;> simp [kosD]
  rcases p with ⟨I, a⟩ | a
  · have h2 : ∑ q : Fin d, kosD m ev (.inl ⟨I, a⟩) (.inr q) * kosD m ev (.inr q) (.inl ⟨K, c⟩) = 0 := by
      simp [kosD]
    rw [h2, add_zero, Fintype.sum_sigma]
    let T : Fin g → Fin g → R := fun i i' =>
      if i ∉ I ∧ i' ∉ insert i I ∧ K = insert i' (insert i I) then
        (-1) ^ (I.filter (· < i)).card * (-1) ^ ((insert i I).filter (· < i')).card *
          (m i I.card (insert i I).card * m i' (insert i I).card K.card) a c else 0
    have h3 : ∀ J : Finset (Fin g), ∑ k : Fin (N J.card),
        kosD m ev (.inl ⟨I, a⟩) (.inl ⟨J, k⟩) * kosD m ev (.inl ⟨J, k⟩) (.inl ⟨K, c⟩) =
        ∑ i, if J = insert i I then ∑ i', T i i' else 0 := by
      intro J
      simp only [kosD, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hJ : J = insert i I
      · subst hJ
        rw [if_pos rfl]
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i' _ => ?_
        by_cases hi : i ∉ I
        · by_cases hi' : i' ∉ insert i I ∧ K = insert i' (insert i I)
          · simp only [T]
            rw [if_pos ⟨hi, hi'⟩, Matrix.mul_apply, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [if_pos ⟨hi, trivial⟩, if_pos hi']
            ring
          · simp only [T]
            rw [if_neg (fun h => hi' h.2)]
            exact Finset.sum_eq_zero fun k _ => by rw [if_neg hi', mul_zero]
        · simp only [T]
          rw [if_neg (fun h => hi h.1)]
          exact Finset.sum_eq_zero fun k _ => by rw [if_neg (fun h => hi h.1), zero_mul]
      · rw [if_neg hJ]
        exact Finset.sum_eq_zero fun k _ => by rw [if_neg (fun h => hJ h.2), zero_mul]
    rw [Finset.sum_congr rfl fun J _ => h3 J, Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Fintype.sum_prod_type']
    have hT : ∀ i i', T i i' + T i' i = 0 := by
      intro i i'
      by_cases h : i ∉ I ∧ i' ∉ insert i I ∧ K = insert i' (insert i I)
      · obtain ⟨h1, h2, h3⟩ := h
        have hne : i' ≠ i := fun e => h2 (e ▸ Finset.mem_insert_self _ _)
        have h4 : i' ∉ I := fun e => h2 (Finset.mem_insert_of_mem e)
        have h5 : i ∉ insert i' I := by simp [h1, hne.symm]
        have h6 : K = insert i (insert i' I) := h3.trans (Finset.insert_comm _ _ _)
        have hK : K.card = I.card + 2 := by
          rw [h3, Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1]
        have hg : K.card ≤ g := by simpa using Finset.card_le_univ K
        simp only [T]
        rw [if_pos ⟨h1, h2, h3⟩, if_pos ⟨h4, h5, h6⟩, sign_insert I h1, sign_insert I h4,
          hc' i i' _ _ _ _ (Finset.card_insert_of_notMem h1) (Finset.card_insert_of_notMem h4) hK hg]
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · rw [if_pos hlt, if_neg hlt.not_gt]; ring
        · rw [if_pos hlt, if_neg hlt.not_gt]; ring
      · have h' : ¬ (i' ∉ I ∧ i ∉ insert i' I ∧ K = insert i (insert i' I)) := by
          rintro ⟨h1, h2, h3⟩
          have hne : i ≠ i' := fun e => h2 (e ▸ Finset.mem_insert_self _ _)
          exact h ⟨fun e => h2 (Finset.mem_insert_of_mem e), by simp [h1, hne.symm],
            h3.trans (Finset.insert_comm _ _ _)⟩
        simp only [T]
        rw [if_neg h, if_neg h', add_zero]
    refine Finset.sum_involution (fun p _ => p.swap) (fun p _ => hT p.1 p.2) ?_ (fun _ _ => Finset.mem_univ _)
      (fun p _ => Prod.swap_swap p)
    rintro ⟨i, i'⟩ _ h e
    apply h
    obtain rfl : i' = i := congrArg Prod.fst e
    exact if_neg fun h => h.2.1 (Finset.mem_insert_self _ _)
  · have h2 : ∑ q : Fin d, kosD m ev (.inr a) (.inr q) * kosD m ev (.inr q) (.inl ⟨K, c⟩) = 0 := by
      simp [kosD]
    rw [h2, add_zero, Fintype.sum_sigma]
    refine Finset.sum_eq_zero fun J _ => ?_
    simp only [kosD]
    by_cases hJ : J = ∅
    · simp only [if_pos hJ, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases h : i ∉ J ∧ K = insert i J
      · simp only [if_pos h]
        have e := congrFun (congrFun (he' i J.card K.card (by simp [hJ]) (by simp [h.2, hJ])) a) c
        rw [Matrix.mul_apply, Matrix.zero_apply] at e
        rw [← mul_zero ((-1 : R) ^ (J.filter (· < i)).card), ← e, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      · simp only [if_neg h, mul_zero, Finset.sum_const_zero]
    · simp only [if_neg hJ, zero_mul, Finset.sum_const_zero]
end GlobalTheory.KeyKa.KoszulCx
