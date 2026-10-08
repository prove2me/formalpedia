-- Prove2me | solution 1 for ImplicitCalculus.smooth_level_parametrization
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T16:37:30.182018+00:00
-- url     : https://prove2.me/submissions/c308a40b-5fb6-46e8-9082-6558051edf8e

import Mathlib.Analysis.Calculus.ImplicitContDiff

set_option autoImplicit false
open Filter
open scoped ContDiff Topology

theorem solution {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (F : V → W) (y : V) (hF : ContDiffAt ℝ ∞ F y)
    (hD : Function.Surjective (fderiv ℝ F y)) :
    ∃ γ : (fderiv ℝ F y).ker → V,
      ContDiffAt ℝ ∞ γ 0 ∧ γ 0 = y ∧
      HasFDerivAt γ (fderiv ℝ F y).ker.subtypeL 0 ∧
      ∀ᶠ z in 𝓝 (0 : (fderiv ℝ F y).ker), F (γ z) = F y := by
  letI : CompleteSpace W := FiniteDimensional.complete ℝ W
  let D := fderiv ℝ F y
  have hs : HasStrictFDerivAt F D y := hF.hasStrictFDerivAt (by simp)
  have hr : D.range = ⊤ := LinearMap.range_eq_top.mpr hD
  have hk : D.ker.ClosedComplemented := D.ker_closedComplemented_of_finiteDimensional_range
  let φ := hs.implicitFunctionDataOfComplemented F D hr hk
  let γ : D.ker → V := hs.implicitFunctionOfComplemented F D hr hk (F y)
  have hγ0 : γ 0 = y := hs.implicitFunctionOfComplemented_apply_image hr hk
  have hφ : ContDiffAt ℝ ∞ φ.implicitFunction.uncurry (F y, (0 : D.ker)) := by
    have hl : ContDiffAt ℝ ∞ φ.leftFun φ.pt := hF
    have hr' : ContDiffAt ℝ ∞ φ.rightFun φ.pt := by
      dsimp [φ, HasStrictFDerivAt.implicitFunctionDataOfComplemented]
      fun_prop
    simpa [φ, ImplicitFunctionData.prodFun] using φ.contDiffAt_implicitFunction hl hr' (by simp)
  have hγ : ContDiffAt ℝ ∞ γ 0 := by
    exact hφ.comp 0 (contDiffAt_const.prodMk contDiffAt_id)
  have hlevel : ∀ᶠ z in 𝓝 (0 : D.ker), F (γ z) = F y := by
    exact (continuousAt_const.prodMk continuousAt_id).tendsto.eventually
      (hs.map_implicitFunctionOfComplemented_eq hr hk)
  exact ⟨γ, hγ, hγ0, (hs.to_implicitFunctionOfComplemented hr hk).hasFDerivAt, hlevel⟩
