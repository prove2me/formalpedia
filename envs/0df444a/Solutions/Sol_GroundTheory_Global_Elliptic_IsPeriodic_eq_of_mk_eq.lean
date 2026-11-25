-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.IsPeriodic.eq_of_mk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:05:16.938686+00:00
-- url     : https://prove2.me/submissions/3f26a537-9beb-4ff5-a805-99772bf130a6

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Theorems.Thm_GroundTheory_Global_Elliptic_Torus_mk_eq_mk_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable (L : PeriodPair)
variable {L}
namespace GroundTheory.Global.Elliptic
namespace IsPeriodic
theorem _root_.solution {E : Type*} {f : ℂ → E} (hf : IsPeriodic L f) {z w : ℂ}
    (h : Torus.mk L z = Torus.mk L w) : f z = f w := by
  have hzw := (Torus.mk_eq_mk_iff L).1 h
  simpa using hf w (z - w) hzw
end IsPeriodic
end GroundTheory.Global.Elliptic
