-- Prove2me | solution 1 for GlobalTheory.RealWeil.IsHeis.twist
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:58:01.539177+00:00
-- url     : https://prove2.me/submissions/26ffaa47-7c7c-46b7-8841-21134596d208

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix
open scoped RealInnerProductSpace ContDiff Real FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
namespace GlobalTheory.RealWeil
namespace IsHeis
theorem _root_.solution {om : V → V → ℝ} {ρ : V → B →L[ℂ] B} (h : IsHeis om ρ) (g : V →L[ℝ] V)
    (hg : ∀ x y, om (g x) (g y) = om x y) : IsHeis om fun v => ρ (g v) :=
  ⟨fun f => by simp only [map_zero, h.1], fun u v f => by simp only [h.2.1, hg, map_add], fun u f => h.2.2.1 _ f,
    fun f => (h.2.2.2 f).comp g.continuous⟩
end IsHeis
end GlobalTheory.RealWeil
