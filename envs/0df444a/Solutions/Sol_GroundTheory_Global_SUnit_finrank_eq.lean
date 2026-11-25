-- Prove2me | solution 1 for GroundTheory.Global.SUnit.finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:35:08.532044+00:00
-- url     : https://prove2.me/submissions/b6756eb7-e1e0-4e20-add4-3f11e2f63da7

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnitsKernel
import Definitions.Def_GroundTheory_GlobalFields_SUnits
import Theorems.Thm_GroundTheory_Global_SUnit_finrank_range_valuationVector

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
theorem _root_.solution : finrank ℤ (Additive (S.unit K)) = Units.rank K + Nat.card S := by
  rw [← Submodule.finrank_quotient_add_finrank (LinearMap.ker (valuationVector S)),
    LinearEquiv.finrank_eq (valuationVector S).quotKerEquivRange,
    finrank_range_valuationVector, ← LinearEquiv.finrank_eq (unitsEquivKer S),
    Units.finrank_eq, add_comm]
end GroundTheory.Global.SUnit
