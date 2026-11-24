-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.jM_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:42:55.020175+00:00
-- url     : https://prove2.me/submissions/36dfd7cd-99b0-4a5e-af56-85e07b62b5c0

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_sub_jM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {α κ β : Type} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution {e : κ → α} (he : Function.Injective e) (m : Matrix κ κ R) (x y : κ) :
    jM e m (e x) (e y) = m x y := by
  have := congrFun (congrFun (sub_jM he m) x) y
  simpa using this
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
