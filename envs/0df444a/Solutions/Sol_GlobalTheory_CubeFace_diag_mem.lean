-- Prove2me | solution 1 for GlobalTheory.CubeFace.diag_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:02:44.653672+00:00
-- url     : https://prove2.me/submissions/851327b9-a292-4a7b-b9f4-e78c260d6883

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeSectionFacesAndDoubling
import Theorems.Thm_GlobalTheory_CubeFace_sum_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.CubeFace
namespace GlobalTheory.CubeFace
theorem _root_.solution {V ι : Type*} [AddCommGroup V] [Module ℂ V] (W : ι → Set V) {a b d o : ι}
    {z : V} (ha : z ∈ W a) (hb : -z ∈ W b) (hd : (2 : ℂ) • z ∈ W d) (ho : (0 : V) ∈ W o)
    (J : Finset (Fin 3)) :
    ∑ i ∈ J, (![z, z, -z] : Fin 3 → V) i ∈ W (diagChart a b d o J) := by
  rw [sum_diag]
  unfold diagChart
  split_ifs <;> assumption
end GlobalTheory.CubeFace
