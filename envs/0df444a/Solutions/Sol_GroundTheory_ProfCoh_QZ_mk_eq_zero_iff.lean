-- Prove2me | solution 1 for GroundTheory.ProfCoh.QZ.mk_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:23:08.762015+00:00
-- url     : https://prove2.me/submissions/d6fb806e-ba5d-45b7-9e59-6c585d731c47

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Topology
open GroundTheory.ProfCoh.QZ
namespace GroundTheory.ProfCoh.QZ
theorem _root_.solution (q : ℚ) : mk q = 0 ↔ ∃ n : ℤ, (n : ℚ) = q := by
  simp only [mk, AddEquivClass.map_eq_zero_iff, AddCircle.coe_eq_zero_iff, zsmul_eq_mul, mul_one]
end GroundTheory.ProfCoh.QZ
