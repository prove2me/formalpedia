-- Prove2me | solution 1 for GlobalTheory.HermTuple.exists_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:42:19.807836+00:00
-- url     : https://prove2.me/submissions/f9d78dea-c410-4262-aa8c-b1bddb6f96b0

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralValIntegerIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEquivOfRetractions
import Theorems.Thm_GlobalTheory_HermTuple_exists_matrix_split
import Theorems.Thm_GlobalTheory_HermWitt_exists_gl_isometry_mul_eq_of_det_ne_zero
import Theorems.Thm_GlobalTheory_SgLoc_LocE_isField_or_split


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HermTuple
open Matrix Module
namespace GlobalTheory.HermTuple
theorem _root_.solution {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CharZero F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {n m : ℕ}
    (G : Matrix (Fin n) (Fin n) E) (hG : ∀ a b, L.cj (G a b) = G b a) (hdet : IsUnit G.det)
    (X Y : Matrix (Fin n) (Fin m) E)
    (hu : IsUnit (Xᵀ * G * X.map L.cj).det) (h : Yᵀ * G * Y.map L.cj = Xᵀ * G * X.map L.cj) :
    ∃ γ : Matrix (Fin n) (Fin n) E, γᵀ * G * γ.map L.cj = G ∧ γ * X = Y := by
  rcases GlobalTheory.SgLoc.LocE_isField_or_split L with hE | ⟨e, he⟩
  · letI := hE.toField
    have h2 : (2 : E) ≠ 0 := by
      have : (algebraMap F E 2) ≠ 0 := by
        rw [map_ne_zero]; exact two_ne_zero
      rwa [map_ofNat] at this
    obtain ⟨γ, h1, h3⟩ := GlobalTheory.HermWitt.exists_gl_isometry_mul_eq_of_det_ne_zero
      (c := (L.cj : E →+* E)) h2 L.cj_cj hG (X := X) (Y := Y) hu.ne_zero h
    exact ⟨γ, h1, h3⟩
  · exact exists_matrix_split (L.cj : E →+* E) e.toRingEquiv he G hG hdet X Y hu h
end GlobalTheory.HermTuple
