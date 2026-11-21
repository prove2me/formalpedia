-- Prove2me | solution 2 for MasulloRH.realTraceIntegrand_integrable
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T22:20:41.435189+00:00
-- url     : https://prove2.me/submissions/987518ad-e4c3-4654-b380-69f9126a2f71

import Mathlib
import Definitions.Def_MasulloRH_RationalTrace
open MasulloRH Set MeasureTheory
private theorem support_bounds (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    ∃ M : ℝ, ∀ x : ℝ, M < x → φ x = 0 ∧ φ x⁻¹ = 0 := by
  have hK : IsCompact (tsupport φ) := hφ.2.1
  obtain ⟨A, hA⟩ := hK.bddAbove
  have hi : ContinuousOn (fun x : ℝ => x⁻¹) (tsupport φ) :=
    continuousOn_id.inv₀ (fun x hx => (hφ.2.2.1 hx : 0 < x).ne')
  obtain ⟨D, hD⟩ := hK.bddAbove_image hi
  refine ⟨max A D, fun x hx => ⟨?_, ?_⟩⟩
  · by_contra hn
    exact (not_lt_of_ge (hA (subset_tsupport φ hn))) ((le_max_left A D).trans_lt hx)
  · by_contra hn
    have hb := hD ⟨x⁻¹, subset_tsupport φ hn, rfl⟩
    simp only [inv_inv] at hb
    exact (not_lt_of_ge hb) ((le_max_right A D).trans_lt hx)

theorem solution (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) := by
  obtain ⟨M, hM⟩ := support_bounds φ hφ
  let f (x : ℝ) := φ x + φ x⁻¹
  let G (x : ℝ) := (Real.sqrt x / (x + 1)) • dslope f 1 x
  have hf (x : ℝ) (hx : 0 < x) : DifferentiableAt ℝ f x :=
    (hφ.1.differentiable (by simp) x).add
      ((hφ.1.differentiable (by simp) x⁻¹).comp x (differentiableAt_inv_iff.mpr hx.ne'))
  have hGc : ContinuousOn G (Icc 1 M) := by
    intro x hx
    have hx' : 1 ≤ x := hx.1
    have hd : ContinuousAt (dslope f 1) x := by
      rcases eq_or_ne x 1 with rfl | hn
      · exact continuousAt_dslope_same.mpr (hf 1 one_pos)
      · exact (continuousAt_dslope_of_ne hn).mpr (hf x (by linarith)).continuousAt
    exact (((Real.continuous_sqrt.continuousAt.div
      (continuousAt_id.add continuousAt_const) (by change x + 1 ≠ 0; linarith)).smul hd)).continuousWithinAt
  have hEq {x : ℝ} (hx : 1 < x) : realTraceIntegrand φ x = G x := by
    have hf1 : f 1 = 0 := by simp [f, hφ.2.2.2]
    have hprod : (x - 1) • dslope f 1 x = f x := by simp [hf1]
    change (φ x + φ x⁻¹) * _ = _
    rw [show (φ x + φ x⁻¹) * ((Real.sqrt x / (x^2-1) : ℝ) : ℂ) =
        (Real.sqrt x / (x^2-1)) • f x by rw [Complex.real_smul]; exact mul_comm _ _]
    rw [← hprod, smul_smul]
    unfold G
    congr 1
    have h₁ : x+1 ≠ 0 := by linarith
    have h₂ : x^2-1 ≠ 0 := by nlinarith [sq_nonneg (x-1)]
    field_simp
    <;> ring
  have hnear : IntegrableOn (realTraceIntegrand φ) (Ioc 1 M) :=
    ((hGc.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self).congr_fun
      (fun x hx => (hEq hx.1).symm) measurableSet_Ioc
  have hfar : IntegrableOn (realTraceIntegrand φ) (Ioi M) := by
    apply integrableOn_zero.congr_fun _ measurableSet_Ioi
    intro x hx
    obtain ⟨h₁,h₂⟩ := hM x hx
    simp [realTraceIntegrand, h₁, h₂]
  exact (integrableOn_union.mpr ⟨hnear, hfar⟩).mono_set Ioi_subset_Ioc_union_Ioi
