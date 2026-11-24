-- Prove2me | solution 1 for GlobalTheory.T.ray_L_series_euler_product
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:21:16.621952+00:00
-- url     : https://prove2.me/submissions/bbd4941b-7be6-4e2a-952b-1d6c8a37a8b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProduct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProductStatement
import Theorems.Thm_GlobalTheory_Mem_RayData_lseries_eq_exp_tsum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (χ : D.G →* ℂˣ) (s : ℂ), 1 < s.re → LSeriesSummable (D.coef χ) s ∧ Summable (fun v : D.Pr => ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖) ∧ LSeries (D.coef χ) s = Complex.exp (∑' v : D.Pr, -Complex.log (1 - (χ (D.cls v.1.asIdeal) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  first | exact @GlobalTheory.Mem.RayData.lseries_eq_exp_tsum | exact GlobalTheory.Mem.RayData.lseries_eq_exp_tsum | (intros; apply GlobalTheory.Mem.RayData.lseries_eq_exp_tsum <;> assumption)
end _root_.GlobalTheory.T
