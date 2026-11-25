-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.dH_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:07:00.103855+00:00
-- url     : https://prove2.me/submissions/410677e2-1a49-4e9f-9cd8-c9b201393613

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped ContDiff Real
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
open MeasureTheory Complex Matrix
open scoped ContDiff Real
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
  [NormedSpace ℂ B]
namespace GlobalTheory.Mem.Lift
namespace _root_.GlobalTheory.Mem.Lift
theorem _root_.solution (ρ : V → B →L[ℂ] B) (r : ℝ) (v : V) (f : B) :
    _root_.GlobalTheory.Mem.Lift.dH ρ (r • v) f = r • _root_.GlobalTheory.Mem.Lift.dH ρ v f :=
  map_smul _ _ _
end _root_.GlobalTheory.Mem.Lift
end GlobalTheory.Mem.Lift
