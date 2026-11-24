-- Prove2me | solution 1 for GlobalTheory.CubeFace.diag_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:41:09.431274+00:00
-- url     : https://prove2.me/submissions/a309c75d-09ff-4ce0-b799-fb9a66bdb220

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeSectionFacesAndDoubling
import Theorems.Thm_GlobalTheory_CubeFace_prod_alt
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
theorem _root_.solution {V ι : Type*} [AddCommGroup V] [Module ℂ V] (c : ι → ι → V → ℂ)
    (a b d a' b' d' o : ι) (ho : c o o 0 = 1) (z : V) :
    ∏ J : Finset (Fin 3), c (diagChart a b d o J) (diagChart a' b' d' o J)
      (∑ i ∈ J, (![z, z, -z] : Fin 3 → V) i) ^ ((-1 : ℤ) ^ (3 - J.card)) =
      c a a' z ^ 3 * c b b' (-z) * (c d d' ((2 : ℂ) • z))⁻¹ := by
  simp only [sum_diag]
  rw [prod_alt (fun J => c (diagChart a b d o J) (diagChart a' b' d' o J)
    (diagChart z (-z) ((2 : ℂ) • z) 0 J))]
  simp (config := {decide := true}) only [diagChart, if_true, if_false, ho]
  simp only [inv_one, mul_one, one_mul]
  ring
end GlobalTheory.CubeFace
