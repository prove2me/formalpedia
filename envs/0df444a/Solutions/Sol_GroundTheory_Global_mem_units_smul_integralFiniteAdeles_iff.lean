-- Prove2me | solution 1 for GroundTheory.Global.mem_units_smul_integralFiniteAdeles_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:49:02.263457+00:00
-- url     : https://prove2.me/submissions/62af1d09-43c7-4906-85cb-7606a303df1e

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleIdealMeasure
import Theorems.Thm_GroundTheory_Global_mem_integralFiniteAdeles
import Theorems.Thm_GroundTheory_Global_units_mul_inv_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory Measure WithZero
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution (u : (𝔸ᶠ[K])ˣ) (y : 𝔸ᶠ[K]) :
    y ∈ u • (integralFiniteAdeles (𝓞 K) K : Set 𝔸ᶠ[K]) ↔
      ∀ v : HeightOneSpectrum (𝓞 K), ((u : 𝔸ᶠ[K]) v)⁻¹ * y v ∈ v.adicCompletionIntegers K := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul, SetLike.mem_coe,
    mem_integralFiniteAdeles]
  refine forall_congr' fun v ↦ ?_
  rw [← eq_inv_of_mul_eq_one_right (units_mul_inv_apply u v)]
  rfl
end GroundTheory.Global
