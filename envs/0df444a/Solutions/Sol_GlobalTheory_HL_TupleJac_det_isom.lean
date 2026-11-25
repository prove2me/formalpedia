-- Prove2me | solution 1 for GlobalTheory.HL.TupleJac.det_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:46:31.770719+00:00
-- url     : https://prove2.me/submissions/90be5e28-4b8d-4508-a7f5-1afbeeb4eb91

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelVolMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometry
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TupleJac
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.TupleJac
theorem _root_.solution (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (hH : IsUnit Hm.det)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) (hg : g ∈ isomG L Hm) :
    LinearMap.det g.toLinearMap * L.cj (LinearMap.det g.toLinearMap) = 1 := by
  set M := LinearMap.toMatrix' g.toLinearMap with hM
  have h : M.transpose * Hm * (L.cj.toRingEquiv.toRingHom.mapMatrix M) = Hm := by
    ext i j
    have h1 := hg (Pi.single i 1) (Pi.single j 1)
    have h2 : hf L Hm (Pi.single i 1) (Pi.single j 1) = Hm i j := by
      simp [hf, Pi.single_apply, apply_ite L.cj]
    rw [h2] at h1
    rw [← h1, hf, Finset.sum_comm]
    simp [hM, Matrix.mul_apply, Finset.sum_mul, LinearMap.toMatrix'_apply]
  have h3 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, hM,
    LinearMap.det_toMatrix'] at h3
  refine hH.mul_left_cancel ?_
  rw [mul_one]
  conv_rhs => rw [← h3]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
    AlgEquiv.toRingEquiv_eq_coe]
  ring
end GlobalTheory.HL.TupleJac
