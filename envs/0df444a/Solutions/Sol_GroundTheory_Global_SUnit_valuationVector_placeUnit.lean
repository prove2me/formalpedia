-- Prove2me | solution 1 for GroundTheory.Global.SUnit.valuationVector_placeUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:05.557497+00:00
-- url     : https://prove2.me/submissions/e9f1f8fb-11ec-42f3-a65e-d3c8b5989297

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnitsKernel
import Definitions.Def_GroundTheory_GlobalFields_SUnits

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
open scoped Classical
namespace GroundTheory.Global.SUnit
theorem _root_.solution (v : S) :
    valuationVector S (Additive.ofMul ⟨placeUnit v.1, placeUnit_mem S v.2⟩) =
      Pi.single v (-(classNumber K : ℤ)) := by
  funext w
  rw [valuationVector_apply, valuationOfNeZero_placeUnit]
  by_cases h : w = v
  · subst h; simp
  · have h' : w.1 ≠ v.1 := fun e => h (Subtype.ext e)
    simp [h, h']
end GroundTheory.Global.SUnit
