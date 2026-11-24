-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HInv.det_mul_conj_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:21:24.997557+00:00
-- url     : https://prove2.me/submissions/4bcbc7ff-e291-4c0f-a3f6-de2559e4ccfe

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulVecEqSmul
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulEqOfNormOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryActionPreservesHaarLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HInv
namespace GlobalTheory.CompanionTheory.SW.HInv
theorem _root_.solution {A : Type} [CommRing A] {m : Type} [Fintype m] [DecidableEq m]
    (τ : A →+* A) (g J : Matrix m m A) (hg : cT τ g * J * g = J) (hJ : IsUnit J.det) :
    g.det * τ g.det = 1 := by
  have hc : (cT τ g).det = τ g.det := by
    rw [cT, Matrix.det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, hc] at h
  apply hJ.mul_left_cancel
  linear_combination h
end GlobalTheory.CompanionTheory.SW.HInv
