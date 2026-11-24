-- Prove2me | solution 1 for GlobalTheory.ThetaGen.differentiable_of_mem_adjoin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:31:26.566423+00:00
-- url     : https://prove2.me/submissions/dc011951-ece8-4992-bcf4-052eccd82527

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsHomogeneousOfMemSpanPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.ThetaGen
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.ThetaGen
theorem _root_.solution {S : Set (E → ℂ)} (hS : ∀ F ∈ S, Differentiable ℂ F)
    {F : E → ℂ} (hF : F ∈ Algebra.adjoin ℂ S) : Differentiable ℂ F := by
  induction hF using Algebra.adjoin_induction with
  | mem x hx => exact hS x hx
  | algebraMap c => exact differentiable_const _
  | add x y _ _ hx hy => exact hx.add hy
  | mul x y _ _ hx hy => exact hx.mul hy
end GlobalTheory.ThetaGen
