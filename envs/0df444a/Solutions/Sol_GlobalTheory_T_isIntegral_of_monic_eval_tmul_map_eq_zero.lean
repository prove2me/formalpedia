-- Prove2me | solution 1 for GlobalTheory.T.isIntegral_of_monic_eval_tmul_map_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:10:11.206424+00:00
-- url     : https://prove2.me/submissions/473b687a-f88f-438e-998c-697e08c21c9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntegralOfFiniteBaseChangeImage
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IntegralOfFiniteBaseChangeImageStatement
import Theorems.Thm_GlobalTheory_integral_of_finite_base_change_image


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (T U C F K L : Type) [CommRing T] [IsDomain T] [CommRing U] [IsDomain U] [CommRing C] [IsDomain C] [Field F] [Field K] [Field L] [Algebra T U] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra U L] [IsFractionRing U L] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Algebra T L] [Algebra F L] [IsScalarTower T U L] [IsScalarTower T F L] [Module.Finite T C] (φ : U ⊗[T] C →+* L ⊗[F] K), (∀ u c, φ (u ⊗ₜ c) = algebraMap U L u ⊗ₜ algebraMap C K c) → ∀ (ω : L ⊗[F] K) (p : Polynomial (U ⊗[T] C)), p.Monic → p.eval₂ φ ω = 0 → IsIntegral U ω := by
  first | exact @GlobalTheory.integral_of_finite_base_change_image | exact GlobalTheory.integral_of_finite_base_change_image | (intros; apply GlobalTheory.integral_of_finite_base_change_image <;> assumption)
end _root_.GlobalTheory.T
