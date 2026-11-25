-- Prove2me | solution 1 for GlobalTheory.JacobianIndependence.eq_zero_of_eventually_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:09:32.322595+00:00
-- url     : https://prove2.me/submissions/7db3e25a-b4b2-4643-9da7-b1f52c797048

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpolationModelInequalities
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EqZeroOfDetFderivNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open Filter Topology
open GlobalTheory GlobalTheory.JacobianIndependence
namespace GlobalTheory.JacobianIndependence
theorem _root_.solution {n : ℕ} (p : MvPolynomial (Fin n) ℂ)
    (a : EuclideanSpace ℂ (Fin n))
    (h : ∀ᶠ w in 𝓝 a, MvPolynomial.eval (fun k => w k) p = 0) : p = 0 := by
  have hc : Continuous (fun x : Fin n → ℂ => (WithLp.toLp 2 x : EuclideanSpace ℂ (Fin n))) :=
    PiLp.continuous_toLp 2 _
  have h1 : ∀ᶠ x in 𝓝 (fun k => a k), MvPolynomial.eval x p = 0 :=
    (hc.tendsto (fun k => a k)).eventually h
  rw [nhds_pi, Filter.Eventually, Filter.mem_pi] at h1
  obtain ⟨I, -, t, ht, hsub⟩ := h1
  refine MvPolynomial.funext_set t (fun i => infinite_of_mem_nhds _ (ht i)) ?_
  intro x hx
  rw [map_zero]
  exact hsub (fun i _ => hx i (Set.mem_univ i))
end GlobalTheory.JacobianIndependence
