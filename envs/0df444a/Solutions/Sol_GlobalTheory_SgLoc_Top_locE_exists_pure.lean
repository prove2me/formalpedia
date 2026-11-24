-- Prove2me | solution 1 for GlobalTheory.SgLoc.Top.locE_exists_pure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:47:01.245103+00:00
-- url     : https://prove2.me/submissions/ce02e02b-388b-49e1-9c94-46a02d7cffb1

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RowRawRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Theorems.Thm_GlobalTheory_SgLoc_Top_locE_nontrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel MeasureTheory Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.SgLoc GlobalTheory.SgLoc.Top
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.SgLoc.Top
theorem _root_.solution [CharZero F] (L : LocE F E) :
    ∃ (d : E) (D : F), D ≠ 0 ∧ D ∈ 𝒪[F] ∧ L.cj d = -d ∧ d * d = algebraMap F E D := by
  have := L.free
  have := L.reduced
  have hnt := locE_nontrivial L
  obtain ⟨x, hx⟩ : ∃ x : E, ∀ a : F, algebraMap F E a ≠ x := by
    by_contra! h
    have e := LinearEquiv.ofBijective (Algebra.linearMap F E) ⟨(algebraMap F E).injective, fun y => h y⟩
    have := e.finrank_eq
    rw [Module.finrank_self, L.rank] at this
    norm_num at this
  set d0 := x - L.cj x with hd0def
  have hcj0 : L.cj d0 = -d0 := by
    rw [hd0def, map_sub, L.cj_cj]; ring
  have hd0 : d0 ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := (L.cj_fix x).mp (by rw [hd0def, sub_eq_zero] at h0; exact h0.symm)
    exact hx a ha
  obtain ⟨D0, hD0⟩ := (L.cj_fix (d0 * d0)).mp (by rw [map_mul, hcj0, neg_mul_neg])
  have hD0ne : D0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hD0
    exact hd0 (IsReduced.eq_zero d0 ⟨2, by rw [pow_two, ← hD0]⟩)
  by_cases hD : D0 ∈ 𝒪[F]
  · exact ⟨d0, D0, hD0ne, hD, hcj0, hD0.symm⟩
  · refine ⟨algebraMap F E D0⁻¹ * d0, D0⁻¹, inv_ne_zero hD0ne, ?_, ?_, ?_⟩
    · rw [Valuation.mem_integer_iff] at hD ⊢
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp hD))
    · rw [map_mul, AlgEquiv.commutes, hcj0, mul_neg]
    · rw [show (algebraMap F E D0⁻¹ * d0) * (algebraMap F E D0⁻¹ * d0) =
          algebraMap F E (D0⁻¹ * D0⁻¹ * D0) by rw [map_mul, map_mul, hD0]; ring]
      congr 1
      field_simp
end GlobalTheory.SgLoc.Top
