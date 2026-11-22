-- Prove2me | solution 1 for GradientFieldOrderShift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:09:50.550785+00:00
-- url     : https://prove2.me/submissions/26bee2ab-a737-4857-aa4b-6a06e71b9129

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_GradientFieldOrderShift

set_option autoImplicit false

theorem _root_.solution (U : Set Plane) (v : Plane → ℝ)
    (hUo : IsOpen U) (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U) :
    gradient v
        = (fun T : Plane →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ Plane).symm T) ∘ fderiv ℝ v
      ∧ ContDiffOn ℝ (⊤ : ℕ∞) (gradient v) U
      ∧ (∀ (n : ℕ) (x : Plane),
          ‖iteratedFDeriv ℝ n (gradient v) x‖ = ‖iteratedFDeriv ℝ (n + 1) v x‖)
      ∧ (∀ (n : ℕ), ∀ x ∈ U, ∀ y ∈ U,
          ‖iteratedFDeriv ℝ n (gradient v) x - iteratedFDeriv ℝ n (gradient v) y‖
            = ‖iteratedFDeriv ℝ (n + 1) v x - iteratedFDeriv ℝ (n + 1) v y‖) := by
  -- (1) THE RIESZ FACTORIZATION.  Pointwise, `D¹v z` is the Riesz dual of `gradient v z`.
  have hgfac : gradient v
      = (fun T : Plane →L[ℝ] ℝ => (InnerProductSpace.toDual ℝ Plane).symm T) ∘ fderiv ℝ v := by
    funext z
    show gradient v z = (InnerProductSpace.toDual ℝ Plane).symm (fderiv ℝ v z)
    rw [← toDual_gradient, LinearIsometryEquiv.symm_apply_apply]
  refine ⟨hgfac, ?_, ?_, ?_⟩
  -- (2) SMOOTHNESS.  The Riesz map is a continuous linear equivalence, hence `C^∞`, and `D¹v`
  -- is `C^∞` on the OPEN set `U` because `v` is.
  · rw [hgfac]
    exact (InnerProductSpace.toDual ℝ Plane).symm.contDiff.comp_contDiffOn
      (hv.fderiv_of_isOpen hUo (by norm_cast))
  -- (3) THE ONE-POINT ORDER SHIFT.  Two isometries, no domain hypothesis.
  · intro n x
    rw [hgfac, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_fderiv]
  -- (4) THE TWO-POINT ORDER SHIFT.
  · intro n x hx y hy
    obtain ⟨Λ, hΛ⟩ : ∃ t : (Plane →L[ℝ] ℝ) →L[ℝ] Plane,
        t = (InnerProductSpace.toDual ℝ Plane).symm.toLinearIsometry.toContinuousLinearMap :=
      ⟨_, rfl⟩
    have hgfac' : gradient v = (fun T : Plane →L[ℝ] ℝ => Λ T) ∘ fderiv ℝ v := by
      rw [hΛ]; exact hgfac
    -- (i) move the Riesz map outside the iterated derivative, at both points
    have hstr : ∀ z ∈ U, iteratedFDeriv ℝ n (gradient v) z
        = Λ.compContinuousMultilinearMap (iteratedFDeriv ℝ n (fderiv ℝ v) z) := by
      intro z hz
      have hcd : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ v) z :=
        (hv.contDiffAt (hUo.mem_nhds hz)).fderiv_right (by norm_cast)
      rw [hgfac']
      exact Λ.iteratedFDeriv_comp_left hcd (by exact_mod_cast le_top)
    rw [hstr x hx, hstr y hy,
      show Λ.compContinuousMultilinearMap (iteratedFDeriv ℝ n (fderiv ℝ v) x)
          - Λ.compContinuousMultilinearMap (iteratedFDeriv ℝ n (fderiv ℝ v) y)
          = Λ.compContinuousMultilinearMap
              (iteratedFDeriv ℝ n (fderiv ℝ v) x - iteratedFDeriv ℝ n (fderiv ℝ v) y)
        from by ext u; simp, hΛ,
      LinearIsometry.norm_compContinuousMultilinearMap]
    -- (ii) the order shift, on the difference
    rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
    show _ = ‖(continuousMultilinearCurryRightEquiv' ℝ n Plane ℝ).symm
          (iteratedFDeriv ℝ n (fun z => fderiv ℝ v z) x)
        - (continuousMultilinearCurryRightEquiv' ℝ n Plane ℝ).symm
          (iteratedFDeriv ℝ n (fun z => fderiv ℝ v z) y)‖
    rw [← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
