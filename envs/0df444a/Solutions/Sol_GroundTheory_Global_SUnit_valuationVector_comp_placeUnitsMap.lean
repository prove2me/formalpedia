-- Prove2me | solution 1 for GroundTheory.Global.SUnit.valuationVector_comp_placeUnitsMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:26.425195+00:00
-- url     : https://prove2.me/submissions/56fdcc6a-cac8-4d77-8934-54fb099aef3f

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnitsKernel
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Theorems.Thm_GroundTheory_Global_SUnit_valuationVector_placeUnit

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
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Module
open scoped NumberField nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.SUnit
variable (S : Set (HeightOneSpectrum (𝓞 K)))
variable [Finite S]
namespace GroundTheory.Global.SUnit
theorem _root_.solution :
    valuationVector S ∘ₗ placeUnitsMap S = (-(classNumber K : ℤ)) • LinearMap.id := by
  classical
  refine (Pi.basisFun ℤ S).ext fun v => ?_
  rw [LinearMap.comp_apply, placeUnitsMap, Basis.constr_basis, valuationVector_placeUnit,
    LinearMap.smul_apply, LinearMap.id_apply, Pi.basisFun_apply]
  rw [← Pi.single_smul, smul_eq_mul, mul_one]
end GroundTheory.Global.SUnit
