-- Prove2me | solution 1 for GlobalTheory.differentiableOn_quotient_of_differentiableOn_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:31:28.15182+00:00
-- url     : https://prove2.me/submissions/60eebc26-7c12-471a-afc7-f973ff2aa36e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DifferentiableOnQuotientOfDifferentiableOnSlice
import Theorems.Thm_GlobalTheory_exists_circle_ne_zero_of_frequently_ne_zero
import Theorems.Thm_GlobalTheory_differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Metric Set
open scoped Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V V' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
      [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V'] (W : Set (V × V'))
      (f θ F : V × V' → ℂ), IsOpen W → DifferentiableOn ℂ f W → DifferentiableOn ℂ θ W →
      (∀ w ∈ W, F w * θ w = f w) →
      (∀ b, DifferentiableOn ℂ (fun z => F (b, z)) {z | (b, z) ∈ W}) →
      (∀ w ∈ W, ∃ᶠ z in nhds w.2, θ (w.1, z) ≠ 0) → DifferentiableOn ℂ F W := by
  intro V V' _ _ _ _ _ _ W f θ F hW hf hθ hF hsl hfr w hw
  obtain ⟨v, r, hr, hin, hne⟩ := exists_circle_ne_zero_of_frequently_ne_zero
    (S := {z | (w.1, z) ∈ W}) (g := fun z => θ (w.1, z)) (z₀ := w.2)
    ((hW.preimage (f := fun z => (w.1, z)) (by fun_prop)).mem_nhds hw)
    (hθ.comp (f := fun z => (w.1, z)) (by fun_prop) fun z hz => hz) (hfr w hw)
  let p : V × V' → ℂ → V × V' := fun y t => (y.1, y.2 + t • v)
  have hp : Continuous fun q : (V × V') × ℂ => p q.1 q.2 := by fun_prop
  have h1 : ∀ᶠ y in 𝓝 w, ∀ t ∈ closedBall (0 : ℂ) r, p y t ∈ W :=
    (isCompact_closedBall (0 : ℂ) r).eventually_forall_of_forall_eventually fun t ht =>
      hp.continuousAt.eventually (hW.mem_nhds (hin t ht))
  have h2 : ∀ᶠ y in 𝓝 w, ∀ t ∈ sphere (0 : ℂ) r, θ (p y t) ≠ 0 :=
    (isCompact_sphere (0 : ℂ) r).eventually_forall_of_forall_eventually fun t ht => by
      have hc : ContinuousAt θ (p w t) :=
        (hθ.differentiableAt (hW.mem_nhds (hin t (sphere_subset_closedBall ht)))).continuousAt
      exact (ContinuousAt.comp (g := θ) (f := fun q : (V × V') × ℂ => p q.1 q.2) (x := (w, t))
        hc hp.continuousAt).eventually_ne (hne t ht)
  obtain ⟨U, hU, hUo, hwU⟩ := _root_.eventually_nhds_iff.1 (h1.and h2)
  have hcm : ∀ s : ℝ, circleMap 0 r s ∈ sphere (0 : ℂ) r := fun s =>
    circleMap_mem_sphere 0 hr.le s
  have hG := (differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn
    (F := fun (s : ℝ) (y : V × V') => f (p y (circleMap 0 r s)) / θ (p y (circleMap 0 r s)))
    (a := 0) (b := 2 * Real.pi) hUo ?_ ?_).1
  · have hEq : ∀ y ∈ U, F y = (2 * Real.pi)⁻¹ • ∫ s in (0 : ℝ)..2 * Real.pi,
        f (p y (circleMap 0 r s)) / θ (p y (circleMap 0 r s)) := by
      intro y hy
      have hd : DifferentiableOn ℂ (fun t : ℂ => F (p y t)) (closedBall 0 r) :=
        (hsl y.1).comp (f := fun t : ℂ => y.2 + t • v) (by fun_prop) fun t ht => (hU y hy).1 t ht
      have hdc : DiffContOnCl ℂ (fun t : ℂ => F (p y t)) (ball 0 |r|) := by
        apply DifferentiableOn.diffContOnCl
        rwa [abs_of_pos hr, closure_ball _ hr.ne']
      have hav := hdc.circleAverage
      rw [Real.circleAverage_def] at hav
      have : F y = F (p y 0) := by simp [p]
      rw [this, ← hav]
      congr 1
      refine intervalIntegral.integral_congr fun s _ => ?_
      have hs := hcm s
      rw [eq_div_iff ((hU y hy).2 _ hs), hF _ ((hU y hy).1 _ (sphere_subset_closedBall hs))]
    have hFU : DifferentiableOn ℂ F U := (hG.const_smul ((2 * Real.pi)⁻¹ : ℝ)).congr hEq
    exact (hFU.differentiableAt (hUo.mem_nhds hwU)).differentiableWithinAt
  · have hq : Continuous fun q : ℝ × (V × V') => p q.2 (circleMap 0 r q.1) :=
      hp.comp (f := fun q : ℝ × (V × V') => (q.2, circleMap 0 r q.1)) (by fun_prop)
    have hm : ∀ q : ℝ × (V × V'), q ∈ uIcc 0 (2 * Real.pi) ×ˢ U →
        p q.2 (circleMap 0 r q.1) ∈ W := fun q hq =>
      (hU _ hq.2).1 _ (sphere_subset_closedBall (hcm _))
    exact (hf.continuousOn.comp hq.continuousOn hm).div
      (hθ.continuousOn.comp hq.continuousOn hm) fun q hq => (hU _ hq.2).2 _ (hcm _)
  · intro s _
    have hq : Differentiable ℂ fun y : V × V' => p y (circleMap 0 r s) := by fun_prop
    have hm : ∀ y ∈ U, p y (circleMap 0 r s) ∈ W := fun y hy =>
      (hU _ hy).1 _ (sphere_subset_closedBall (hcm _))
    simp only [div_eq_mul_inv]
    exact (hf.comp hq.differentiableOn hm).mul
      ((hθ.comp hq.differentiableOn hm).inv fun y hy => (hU _ hy).2 _ (hcm _))
end GlobalTheory
