-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.germDeriv_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:06:38.558623+00:00
-- url     : https://prove2.me/submissions/8907d058-6d21-4d52-9f6f-6bde5b878122

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AnalyticAlgebraicGerm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f : ℂ → ℂ} (hf : Meromorphic f) : germDeriv (germ f) = germ (deriv f) :=
  derivFun_germ hf
end GroundTheory.Global.Elliptic
