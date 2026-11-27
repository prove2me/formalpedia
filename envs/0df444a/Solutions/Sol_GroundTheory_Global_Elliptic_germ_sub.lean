-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.germ_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:47:10.577742+00:00
-- url     : https://prove2.me/submissions/195d5236-a16f-48a7-9a0c-ae9bed6bcd78

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_AnalyticAlgebraicGerm
import Theorems.Thm_GroundTheory_Global_Elliptic_germ_neg

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
theorem _root_.solution {f g : ℂ → ℂ} (hf : Meromorphic f) (hg : Meromorphic g) :
    germ (f - g) = germ f - germ g := by
  rw [sub_eq_add_neg, germ_add hf hg.neg, germ_neg hg, ← sub_eq_add_neg]
end GroundTheory.Global.Elliptic
