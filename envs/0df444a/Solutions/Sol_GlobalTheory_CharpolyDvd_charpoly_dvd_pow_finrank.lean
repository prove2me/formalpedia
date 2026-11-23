-- Prove2me | solution 1 for GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:58.0843+00:00
-- url     : https://prove2.me/submissions/8d0e5752-70e7-4ce4-8770-dee07f91f22b

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CharpolyDvdPowFinrankOfAevalEqZero
import Theorems.Thm_GlobalTheory_CharpolyDvd_matrix_charpoly_dvd_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Polynomial GlobalTheory.NormalDescent
open GlobalTheory GlobalTheory.CharpolyDvd
namespace GlobalTheory.CharpolyDvd
theorem _root_.solution {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (G : K[X]) (hG : aeval f G = 0) :
    f.charpoly ∣ G ^ Module.finrank K V := by
  classical
  let b := Module.finBasis K V
  have hM : aeval (LinearMap.toMatrix b b f) G = 0 := by
    have := aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b).toAlgHom f G
    rw [hG, map_zero] at this
    have e : LinearMap.toMatrixAlgEquiv b f = LinearMap.toMatrix b b f := by
      ext i j
      simp [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
    rw [← e]
    exact this
  have := matrix_charpoly_dvd_pow _ G hM
  rwa [LinearMap.charpoly_toMatrix, Fintype.card_fin] at this
end GlobalTheory.CharpolyDvd
