-- Prove2me | solution 1 for GlobalTheory.ThetaFamily.exists_quotient_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:31:27.215712+00:00
-- url     : https://prove2.me/submissions/a12144b4-60f7-4afd-86a1-b1504bc99bce

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DifferentiableOnQuotientOfDifferentiableOnSlice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOfFiniteOfClosedFibres
import Theorems.Thm_GlobalTheory_differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn
import Theorems.Thm_GlobalTheory_exists_circle_ne_zero_of_frequently_ne_zero


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
open GlobalTheory GlobalTheory.ThetaFamily
namespace GlobalTheory.ThetaFamily
theorem _root_.solution {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V'] {W : Set (V × V')}
    {f θ : V × V' → ℂ} (hW : IsOpen W) (hf : DifferentiableOn ℂ f W) (hθ : DifferentiableOn ℂ θ W) {S : Set V}
    (hS : ∀ b ∈ S, ∃ F : V' → ℂ, DifferentiableOn ℂ F {z | (b, z) ∈ W} ∧ ∀ z, (b, z) ∈ W → F z * θ (b, z) = f (b, z))
    {w : V × V'} (hw : w ∈ W) (hfr : ∃ᶠ z in 𝓝 w.2, θ (w.1, z) ≠ 0) :
    ∃ (U : Set (V × V')) (G : V × V' → ℂ), IsOpen U ∧ w ∈ U ∧ U ⊆ W ∧ DifferentiableOn ℂ G U ∧
      ∀ y ∈ U, y.1 ∈ closure S → G y * θ y = f y := by
  obtain ⟨v, r, hr, hin, hne⟩ := exists_circle_ne_zero_of_frequently_ne_zero
    (S := {z | (w.1, z) ∈ W}) (g := fun z => θ (w.1, z)) (z₀ := w.2)
    ((hW.preimage (f := fun z => (w.1, z)) (by fun_prop)).mem_nhds hw)
    (hθ.comp (f := fun z => (w.1, z)) (by fun_prop) fun z hz => hz) hfr
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
  have hp0 : ∀ y, p y 0 = y := fun y => by simp [p]
  have hUW : U ⊆ W := fun y hy => hp0 y ▸ (hU y hy).1 0 (mem_closedBall_self hr.le)
  have hcm : ∀ s : ℝ, circleMap 0 r s ∈ sphere (0 : ℂ) r := fun s =>
    circleMap_mem_sphere 0 hr.le s
  have hG := (differentiableOn_intervalIntegral_of_holomorphic_of_continuousOn
    (F := fun (s : ℝ) (y : V × V') => f (p y (circleMap 0 r s)) / θ (p y (circleMap 0 r s)))
    (a := 0) (b := 2 * Real.pi) hUo ?_ ?_).1
  · obtain ⟨G, hGd, hEq⟩ : ∃ G : V × V' → ℂ, DifferentiableOn ℂ G U ∧ ∀ y ∈ U, y.1 ∈ S → G y * θ y = f y := by
      refine ⟨fun y => ((2 * Real.pi)⁻¹ : ℝ) • ∫ s in (0 : ℝ)..2 * Real.pi,
        f (p y (circleMap 0 r s)) / θ (p y (circleMap 0 r s)), hG.const_smul ((2 * Real.pi)⁻¹ : ℝ), fun y hy hyS => ?_⟩
      obtain ⟨F, hFd, hF⟩ := hS _ hyS
      have hd : DifferentiableOn ℂ (fun t : ℂ => F (y.2 + t • v)) (closedBall 0 r) :=
        hFd.comp (f := fun t : ℂ => y.2 + t • v) (by fun_prop) fun t ht => (hU y hy).1 t ht
      have hdc : DiffContOnCl ℂ (fun t : ℂ => F (y.2 + t • v)) (ball 0 |r|) := by
        apply DifferentiableOn.diffContOnCl
        rwa [abs_of_pos hr, closure_ball _ hr.ne']
      have hav := hdc.circleAverage
      rw [Real.circleAverage_def, zero_smul, add_zero] at hav
      rw [← hF y.2 (hUW hy), ← hav]
      beta_reduce
      congr 2
      refine intervalIntegral.integral_congr fun s _ => ?_
      have hs := hcm s
      show _ / _ = _
      rw [div_eq_iff ((hU y hy).2 _ hs)]
      exact (hF _ ((hU y hy).1 _ (sphere_subset_closedBall hs))).symm
    refine ⟨U, G, hUo, hwU, hUW, hGd, fun y hy hyS => ?_⟩
    have hc : Continuous fun b : V => (b, y.2) := by fun_prop
    have c1 : ContinuousAt (fun b : V => G (b, y.2) * θ (b, y.2)) y.1 :=
      ContinuousAt.comp (g := fun q => G q * θ q) (f := fun b : V => (b, y.2)) (x := y.1)
        ((hGd.mul (hθ.mono hUW)).differentiableAt (hUo.mem_nhds hy)).continuousAt hc.continuousAt
    have c2 : ContinuousAt (fun b : V => f (b, y.2)) y.1 :=
      ContinuousAt.comp (g := f) (f := fun b : V => (b, y.2)) (x := y.1)
        (hf.differentiableAt (hW.mem_nhds (hUW hy))).continuousAt hc.continuousAt
    have hev : ∀ᶠ b in 𝓝 y.1, (b, y.2) ∈ U := hc.continuousAt.eventually (hUo.mem_nhds hy)
    exact tendsto_nhds_unique_of_frequently_eq c1 c2
      (((mem_closure_iff_frequently.1 hyS).and_eventually hev).mono fun b hb => hEq _ hb.2 hb.1)
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
end GlobalTheory.ThetaFamily
