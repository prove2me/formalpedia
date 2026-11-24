-- Prove2me | solution 1 for GlobalTheory.RealWeil.hasFDerivAt_of_norming
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:50:10.611837+00:00
-- url     : https://prove2.me/submissions/ed883547-2fea-40b3-ab07-9b4ba3f5b23f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil
namespace GlobalTheory.RealWeil
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
    [NormedSpace ℂ B] {X : Type} (l : X → B →L[ℂ] ℂ) (h1 : ∀ x b, ‖l x b‖ ≤ ‖b‖)
    (h2 : ∀ b (C : ℝ), 0 ≤ C → (∀ x, ‖l x b‖ ≤ C) → ‖b‖ ≤ C) (F : V → B) (A : V → V →L[ℝ] B) (hA : Continuous A)
    (hF : ∀ x v, HasFDerivAt (fun w => l x (F w)) (((l x).restrictScalars ℝ).comp (A v)) v) (v : V) :
    HasFDerivAt F (A v) v := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.1 (hA.continuousAt (x := v)) c hc
  filter_upwards [Metric.ball_mem_nhds v hδ] with w hw
  refine h2 _ _ (by positivity) fun x => ?_
  have := (convex_ball v δ).norm_image_sub_le_of_norm_hasFDerivWithin_le' (𝕜 := ℝ) (C := c)
    (φ := ((l x).restrictScalars ℝ).comp (A v))
    (fun u _ => (hF x u).hasFDerivWithinAt) (fun u hu => ?_) (Metric.mem_ball_self hδ) hw
  · simpa only [map_sub, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars'] using this
  · refine ContinuousLinearMap.opNorm_le_bound _ hc.le fun z => ?_
    have e : (((l x).restrictScalars ℝ).comp (A u) - ((l x).restrictScalars ℝ).comp (A v)) z = l x ((A u - A v) z) := by
      simp
    rw [e]
    refine (h1 _ _).trans (((A u - A v).le_opNorm z).trans ?_)
    have := hb hu
    rw [dist_eq_norm] at this
    gcongr
end GlobalTheory.RealWeil
