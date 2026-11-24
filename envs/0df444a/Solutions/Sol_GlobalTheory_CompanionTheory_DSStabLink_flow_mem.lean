-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSStabLink.flow_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:26:20.174391+00:00
-- url     : https://prove2.me/submissions/5d9f1635-a19f-467b-b9cf-20b1fdaee1e7

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExpMemUJ
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Matrix Finset Filter Topology Set
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSStabLink
open PI.UpqRep CompanionTheory.D.DSIC
namespace GlobalTheory.CompanionTheory.DSStabLink
theorem _root_.solution {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (T : ℝ → (H →L[ℂ] H)) (h0 : ∀ v, T 0 v = v)
    (hadd : ∀ s t v, T (s + t) v = T s (T t v)) (hiso : ∀ t v, ‖T t v‖ = ‖v‖)
    (hder : ∀ w ∈ W, ∃ z ∈ W, HasDerivAt (fun t => T t w) z 0) (u : H) (hu : u ∈ W) :
    T 1 u ∈ W := by
  set Q : H →L[ℂ] H := Wᗮ.starProjection with hQ
  have hQW : ∀ w ∈ W, Q w = 0 := fun w hw => Submodule.starProjection_orthogonal_apply_eq_zero hw
  have hQs : ∀ x, x - Q x ∈ W := fun x => by
    have := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) x
    rwa [Submodule.orthogonal_orthogonal] at this
  have hQn : ∀ x, ‖Q x‖ ≤ ‖x‖ := fun x => Submodule.norm_starProjection_apply_le _ x
  have hcont : Continuous fun t => T t u := by
    rw [continuous_iff_continuousAt]
    intro t
    obtain ⟨z, -, hz⟩ := hder u hu
    have h1 : ContinuousAt (fun s : ℝ => T (s - t) u) t := by
      have h2 : ContinuousAt (fun s : ℝ => s - t) t := by fun_prop
      exact ContinuousAt.comp_of_eq (g := fun t => T t u) hz.continuousAt h2 (by simp)
    have h3 : ContinuousAt (fun s : ℝ => T t (T (s - t) u)) t :=
      (T t).continuous.continuousAt.comp h1
    convert h3 using 2 with s
    rw [← hadd]; simp
  have key : ∀ ⦃x⦄, x ∈ Icc (0 : ℝ) 1 → ‖Q (T x u)‖ ≤ 0 := by
    refine image_le_of_liminf_slope_right_le_deriv_boundary (f := fun t => ‖Q (T t u)‖)
      (B := fun _ => 0) (B' := fun _ => 0) ?_ ?_ continuousOn_const
      (fun x _ => hasDerivWithinAt_const _ _ _) ?_
    · exact ((Q.continuous.comp hcont).norm).continuousOn
    · simp [h0, hQW u hu]
    · intro x _ r hr
      set w := T x u - Q (T x u) with hw
      obtain ⟨z, hzW, hz⟩ := hder w (hQs _)
      have hg : HasDerivAt (fun t => Q (T t w)) 0 0 := by
        have := (Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hz
        simpa [hQW z hzW, Function.comp_def] using this
      have hg2 : HasDerivAt (fun s : ℝ => Q (T (s - x) w)) 0 x := by
        have h2 : HasDerivAt (fun s : ℝ => s - x) 1 x := (hasDerivAt_id x).sub_const x
        have := HasDerivAt.scomp_of_eq (g₁ := fun t => Q (T t w)) x hg h2 (by simp)
        simpa [Function.comp_def] using this
      have hsl := (hasDerivAt_iff_tendsto_slope.1 hg2).norm
      rw [norm_zero] at hsl
      have hev : ∀ᶠ s in 𝓝[>] x, ‖slope (fun s : ℝ => Q (T (s - x) w)) x s‖ < r :=
        (hsl.eventually (gt_mem_nhds hr)).filter_mono (nhdsWithin_mono _ fun s hs => ne_of_gt hs)
      refine (hev.and self_mem_nhdsWithin).frequently.mono ?_
      rintro s ⟨hs, hsx⟩
      have hpos : 0 < s - x := sub_pos.2 hsx
      refine lt_of_le_of_lt ?_ hs
      rw [slope_def_field, slope_def_module, norm_smul, sub_self, h0, hQW w (hQs _), sub_zero,
        Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos), div_eq_inv_mul]
      refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hpos).le
      have e : Q (T s u) = Q (T (s - x) w) + Q (T (s - x) (Q (T x u))) := by
        rw [← map_add, ← map_add, hw, sub_add_cancel, ← hadd, sub_add_cancel]
      have e2 : ‖Q (T (s - x) (Q (T x u)))‖ ≤ ‖Q (T x u)‖ := (hQn _).trans (hiso _ _).le
      have e3 := norm_add_le (Q (T (s - x) w)) (Q (T (s - x) (Q (T x u))))
      rw [← e] at e3
      linarith
  have h1 := norm_le_zero_iff.1 (key (x := 1) ⟨zero_le_one, le_rfl⟩)
  simpa [h1] using hQs (T 1 u)
end GlobalTheory.CompanionTheory.DSStabLink
