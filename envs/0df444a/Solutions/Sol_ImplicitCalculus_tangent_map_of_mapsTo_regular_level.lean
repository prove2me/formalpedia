-- Prove2me | solution 1 for ImplicitCalculus.tangent_map_of_mapsTo_regular_level
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T19:49:52.274326+00:00
-- url     : https://prove2.me/submissions/1821de2a-41be-4b1b-bc9f-cb960bc36002

import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Data.Real.Basic

open Set Filter
open scoped Topology
set_option autoImplicit false

theorem solution {V W U Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : V → W) (D : V →L[ℝ] W) (y v : V)
    (hF : HasStrictFDerivAt F D y) (hD : Function.Surjective D) (hv : D v = 0)
    (g : V → U) (H : U → Z) (hg : DifferentiableAt ℝ g y)
    (hH : DifferentiableAt ℝ H (g y))
    (hmap : ∀ᶠ z in 𝓝 y, F z = F y → H (g z) = H (g y)) :
    fderiv ℝ H (g y) (fderiv ℝ g y v) = 0 := by
  have hr : D.range = ⊤ := LinearMap.range_eq_top.mpr hD
  let vk : D.ker := ⟨v, hv⟩
  let φ := hF.implicitFunction F D hr
  let γ : ℝ → V := fun s => φ (F y) (s • vk)
  have hline : HasDerivAt (fun s : ℝ => s • vk) vk 0 :=
    by simpa using (hasDerivAt_id (0 : ℝ)).smul_const vk
  have hγ : HasDerivAt γ v 0 := by
    have hp : HasFDerivAt (φ (F y)) D.ker.subtypeL ((0 : ℝ) • vk) := by
      simpa [φ] using (hF.to_implicitFunction hr).hasFDerivAt
    simpa [γ, φ, vk, Function.comp_def] using
      hp.comp_hasDerivAt 0 hline
  have hγ0 : γ 0 = y := by
    simp [γ, φ, hF.implicitFunction_apply_image hr]
  have hparam : Tendsto (fun s : ℝ => (F y, s • vk)) (𝓝 0) (𝓝 (F y, (0 : D.ker))) := by
    simpa using tendsto_const_nhds.prodMk_nhds hline.continuousAt.tendsto
  have hlevel : ∀ᶠ s in 𝓝 (0 : ℝ), F (γ s) = F y := by
    simpa [γ, φ] using hparam.eventually (hF.map_implicitFunction_eq hr)
  have hγlim : Tendsto γ (𝓝 0) (𝓝 y) := hγ0 ▸ hγ.continuousAt.tendsto
  have hconstant : (fun s => H (g (γ s))) =ᶠ[𝓝 (0 : ℝ)] (fun _ => H (g y)) := by
    filter_upwards [hlevel, hγlim.eventually hmap] with s hs hm
    exact hm hs
  have hg0 : HasFDerivAt g (fderiv ℝ g y) (γ 0) := by simpa [hγ0] using hg.hasFDerivAt
  have hH0 : HasFDerivAt H (fderiv ℝ H (g y)) (g (γ 0)) := by
    simpa [hγ0] using hH.hasFDerivAt
  have hd := hH0.comp_hasDerivAt 0 (hg0.comp_hasDerivAt 0 hγ)
  exact hd.unique ((hasDerivAt_const (0 : ℝ) (H (g y))).congr_of_eventuallyEq hconstant)
