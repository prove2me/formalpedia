-- Prove2me | solution 1 for GroundTheory.Global.reverse_charpoly_eq_charpolyRev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:09:49.805623+00:00
-- url     : https://prove2.me/submissions/ff068b0d-4a96-4daf-ab72-e1cd2a4a6e70

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly

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
open Polynomial
open GroundTheory GroundTheory.Global
variable {k W W' : Type*} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  [AddCommGroup W'] [Module k W'] [FiniteDimensional k W']
namespace GroundTheory.Global
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι k W) (A : Module.End k W) :
    A.charpoly.reverse = (LinearMap.toMatrix b b A).charpolyRev := by
  rw [← Matrix.reverse_charpoly, LinearMap.charpoly_toMatrix]
end GroundTheory.Global
