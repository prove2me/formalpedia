-- Prove2me | solution 1 for GlobalTheory.PeriodChart.exists_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:24:30.032717+00:00
-- url     : https://prove2.me/submissions/cd32e8bc-9e1d-4201-96a8-e2ab7630a0bd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
import Theorems.Thm_GlobalTheory_PeriodChart_anti_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {g : ℕ}
namespace GlobalTheory.PeriodChart
theorem _root_.solution (N : (Fin g → ℂ) →ₗ⋆[ℂ] (Fin g → ℂ)) : ∃ Z, N = anti Z := by
  refine ⟨Matrix.of fun i j => N (Pi.single j 1) i, ?_⟩
  ext z i
  have hz : z = ∑ j, z j • (Pi.single j (1 : ℂ) : Fin g → ℂ) := by
    funext k
    simp [Pi.single_apply]
  rw [anti_apply]
  conv_lhs => rw [hz]
  simp only [map_sum, LinearMap.map_smulₛₗ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct,
    Matrix.of_apply, Pi.star_apply, Complex.star_def]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _
end GlobalTheory.PeriodChart
