-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BmuRootVec.ex_of_mul_self_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:37:11.77865+00:00
-- url     : https://prove2.me/submissions/affc1719-6805-458c-bc67-0836cd3ad84d

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_BesselMapUniqGap
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_RootVectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BmuRootVec
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace GlobalTheory.CompanionTheory.BmuRootVec
theorem _root_.solution {n : ℕ} (Y : Mat n) (hY : Y * Y = 0) (τ : ℝ) :
    ex Y τ = 1 + (τ : ℂ) • Y := by
  unfold ex
  have h2 : ((τ : ℂ) • Y) ^ 2 = 0 := by
    rw [pow_two, Matrix.smul_mul, Matrix.mul_smul, hY, smul_zero, smul_zero]
  rw [NormedSpace.exp_eq_tsum ℂ]
  beta_reduce
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ]
  · intro m hm
    have : 2 ≤ m := by
      have := Finset.mem_range.not.1 hm
      omega
    rw [pow_eq_zero_of_le this h2, smul_zero]
end GlobalTheory.CompanionTheory.BmuRootVec
