-- Prove2me | solution 1 for GlobalTheory.NoetherPrimitive.exists_map_eq_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:12.794696+00:00
-- url     : https://prove2.me/submissions/c02f334e-0094-46ce-8236-be57ddf4f44b

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsPrimitiveElementDiscriminantMultiple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherPrimitive
open Polynomial
open scoped nonZeroDivisors
namespace GlobalTheory.NoetherPrimitive
theorem _root_.solution {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (f : K[X]) :
    ∃ s : R, s ≠ 0 ∧ ∃ g : R[X], g.map (algebraMap R K) = C (algebraMap R K s) * f := by
  obtain ⟨s, hs, h⟩ := IsLocalization.integerNormalization_spec R⁰ f
  refine ⟨s, nonZeroDivisors.ne_zero hs, IsLocalization.integerNormalization R⁰ f, ?_⟩
  rw [h, ← smul_eq_C_mul, algebraMap_smul]
end GlobalTheory.NoetherPrimitive
