-- Prove2me | solution 1 for GroundTheory.LocalField.Padic.stdCharOf_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:47:36.807015+00:00
-- url     : https://prove2.me/submissions/c142e3e9-aadd-4a6f-bb7b-7eebbe808fd8

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierTrace
import Definitions.Def_GroundTheory_LocalFields_LocalFourierPadic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory
open scoped NNReal ENNReal
open GroundTheory.LocalField.Padic
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra ℚ_[p] K] [ValuativeExtension ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
namespace GroundTheory.LocalField.Padic
theorem _root_.solution (x : K) : stdCharOf p K x = stdChar p (Algebra.trace ℚ_[p] K x) := rfl
end GroundTheory.LocalField.Padic
