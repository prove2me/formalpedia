-- Prove2me | solution 1 for GlobalTheory.PeriodicCousin.dbar_antilin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:24:37.749508+00:00
-- url     : https://prove2.me/submissions/677b9d1e-86a0-44f6-b5d7-19da331ca04b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DbarSolveComplexTorusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PeriodicCechCocycleSmoothCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HolomorphicPeriodicCocycleCoboundary
import Theorems.Thm_GlobalTheory_PeriodicCousin_antilin_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real Topology
open GlobalTheory GlobalTheory.PeriodicCousin
variable {g : ℕ}
namespace GlobalTheory.PeriodicCousin
theorem _root_.solution (t z : Fin g → ℂ) (a : Fin g) : dbar a (antilin t) z = 2 * t a := by
  unfold dbar
  rw [ContinuousLinearMap.fderiv, antilin_apply, antilin_apply]
  have h1 : star (Pi.single a 1 : Fin g → ℂ) = Pi.single a 1 := by
    ext j; by_cases h : j = a
    · subst h; simp
    · simp [h]
  rw [star_smul, h1]
  simp only [dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul, star_def, conj_I]
  linear_combination (-t a) * I_mul_I
end GlobalTheory.PeriodicCousin
