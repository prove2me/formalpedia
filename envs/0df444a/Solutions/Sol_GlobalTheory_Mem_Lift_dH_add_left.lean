-- Prove2me | solution 1 for GlobalTheory.Mem.Lift.dH_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:03:47.397774+00:00
-- url     : https://prove2.me/submissions/b26e9549-9648-4d5f-8ab4-f83a604a76ce

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
theorem _root_.solution (ρ : V → B →L[ℂ] B) (u v : V) (f : B) :
    _root_.GlobalTheory.Mem.Lift.dH ρ (u + v) f =
      _root_.GlobalTheory.Mem.Lift.dH ρ u f + _root_.GlobalTheory.Mem.Lift.dH ρ v f :=
  map_add _ _ _
end _root_.GlobalTheory.Mem.Lift
end GlobalTheory.Mem.Lift
