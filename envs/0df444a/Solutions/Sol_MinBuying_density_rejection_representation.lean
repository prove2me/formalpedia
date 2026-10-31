-- Prove2me | solution 1 for MinBuying.density_rejection_representation
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T18:06:54.784584+00:00
-- url     : https://prove2.me/submissions/fe7435ec-c984-419a-b1f1-a4063972ae3e

import Definitions.Def_MinBuying_Symmetry

open MeasureTheory Set MinBuying
open scoped BigOperators ENNReal
noncomputable section
namespace MinBuyingDensityConditioningProof

private lemma mtp2_restrict (n : ℕ) (f : Valuations (n+1) → ℝ)
    (hf : ∀ v,0 ≤ f v) (hmtp : MTP2 f) (a : ℝ) :
    MTP2 (fun v => if v 0 < a then f v else 0) := by
  intro v w
  by_cases hv : v 0 < a
  · by_cases hw : w 0 < a
    · have hmax : max (v 0) (w 0) < a := max_lt hv hw
      have hmin : min (v 0) (w 0) < a := (min_le_left _ _).trans_lt hv
      simpa only [hv,hw,hmax,hmin,if_true] using hmtp v w
    · simp only [hw,if_false,mul_zero]
      apply mul_nonneg <;> split_ifs <;> first | exact hf _ | exact le_rfl
  · simp only [hv,if_false,zero_mul]
    apply mul_nonneg <;> split_ifs <;> first | exact hf _ | exact le_rfl

private lemma mtp2_scale {n : ℕ} (f : Valuations n → ℝ) (hmtp : MTP2 f) (c : ℝ) :
    MTP2 (fun v => c*f v) := by
  intro v w
  have h := mul_le_mul_of_nonneg_left (hmtp v w) (sq_nonneg c)
  calc
    (c*f v)*(c*f w) = c^2*(f v*f w) := by ring
    _ ≤ c^2*(f (fun i => max (v i) (w i))*f (fun i => min (v i) (w i))) := h
    _ = (c*f (fun i => max (v i) (w i)))*(c*f (fun i => min (v i) (w i))) := by ring

end MinBuyingDensityConditioningProof

theorem solution (n : ℕ) (μ : JointLaw (n+1)) (hμ : IsProbabilityMeasure μ)
    (f : Valuations (n+1) → ℝ) (hm : Measurable f) (hf : ∀ v,0 ≤ f v) (hmtp : MTP2 f)
    (hden : μ = volume.withDensity (fun v => ENNReal.ofReal (f v))) (a : ℝ)
    (hB : 0 < μ {v : Valuations (n+1) | v 0 < a}) :
    ∃ g : Valuations (n+1) → ℝ, Measurable g ∧ (∀ v,0 ≤ g v) ∧ MTP2 g ∧
      Integrable g volume ∧
      ProbabilityTheory.cond μ {v : Valuations (n+1) | v 0 < a} =
        volume.withDensity (fun v => ENNReal.ofReal (g v)) := by
  classical
  letI : IsProbabilityMeasure μ := hμ
  let B : Set (Valuations (n+1)) := {v | v 0 < a}
  have hmB : MeasurableSet B := measurableSet_lt (measurable_pi_apply 0) measurable_const
  have hreal : 0 < (μ B).toReal := ENNReal.toReal_pos (ne_of_gt hB) (measure_ne_top μ B)
  let c : ℝ := (μ B).toReal⁻¹
  let g : Valuations (n+1) → ℝ := fun v => c*B.indicator f v
  have hgm : Measurable g := measurable_const.mul (hm.indicator hmB)
  have hgn : ∀ v,0 ≤ g v := by
    intro v
    apply mul_nonneg (inv_nonneg.mpr hreal.le)
    by_cases hv : v ∈ B <;> simp [hv,hf]
  have hgt : MTP2 g := by
    have hh := MinBuyingDensityConditioningProof.mtp2_scale _
      (MinBuyingDensityConditioningProof.mtp2_restrict n f hf hmtp a) c
    simpa only [g,B,Set.indicator,Set.mem_setOf_eq] using hh
  have hfinite : (∫⁻ v,ENNReal.ofReal (f v) ∂volume) < ∞ := by
    have hh := measure_lt_top μ Set.univ
    rw [hden,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at hh
    exact hh
  have hfi : Integrable f volume :=
    ⟨hm.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal (ae_of_all _ hf)).mpr hfinite⟩
  refine ⟨g,hgm,hgn,hgt,(hfi.indicator hmB).const_mul c,?_⟩
  have hc : ENNReal.ofReal c = (μ B)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hreal,ENNReal.ofReal_toReal (measure_ne_top μ B)]
  have hfun : (fun v => ENNReal.ofReal (g v)) =
      (μ B)⁻¹ • B.indicator (fun v => ENNReal.ofReal (f v)) := by
    funext v
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr hreal.le),hc]
    by_cases hv : v ∈ B <;> simp [hv]
  symm
  rw [hfun,withDensity_smul _ (hm.ennreal_ofReal.indicator hmB),
    withDensity_indicator hmB,← restrict_withDensity hmB,← hden]
  rfl
