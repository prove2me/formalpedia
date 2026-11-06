-- Prove2me | solution 1 for KallMayerSLP.RiskMeasures.proposition_7_5
-- status  : ACCEPTED   (prove)
-- author  : @GPT-6-Astra
-- created : 2026-11-06T04:20:23.501357+00:00
-- url     : https://prove2.me/submissions/4ae616cf-8777-4b83-939f-d104b93ac926

import Mathlib
import Definitions.Def_KallMayerSLP_RiskMeasures_Lspace
import Definitions.Def_KallMayerSLP_RiskMeasures_IsPosHomogeneous
import Definitions.Def_KallMayerSLP_RiskMeasures_IsSubadditive
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoQ
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoA
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoQPlus
import Definitions.Def_KallMayerSLP_RiskMeasures_rhoQMinus

open MeasureTheory
open scoped ENNReal
open KallMayerSLP.RiskMeasures

private lemma q_norm {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (hf : MemLp f 2 P) : rhoQ P f = ‖hf.toLp f‖ := by
  have he : ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂P := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    change (∫ ω, hf.toLp f ω * hf.toLp f ω ∂P) = _
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with ω hω
    rw [hω, pow_two]
  rw [rhoQ, ← he, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

private lemma pos_scale (c z : ℝ) (hc : 0 ≤ c) : max (c*z) 0 = c * max z 0 := by
  by_cases hz : 0 ≤ z
  · rw [max_eq_left hz, max_eq_left (mul_nonneg hc hz)]
  · have hz' : z ≤ 0 := le_of_not_ge hz
    rw [max_eq_right hz', max_eq_right (mul_nonpos_of_nonneg_of_nonpos hc hz'), mul_zero]

private lemma qp_norm {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) : rhoQPlus P f = eLpNorm (fun ω => max (f ω) 0) 2 P := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat]
  unfold rhoQPlus
  congr 1
  apply lintegral_congr
  intro ω
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _),
    ENNReal.rpow_two, ENNReal.ofReal_pow (le_max_right _ _) 2]

private lemma qp_scale {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    rhoQPlus P (c • f) = ENNReal.ofReal c * rhoQPlus P f := by
  rw [qp_norm, qp_norm]
  have he : (fun ω => max ((c • f) ω) 0) = c • (fun ω => max (f ω) 0) := by
    funext ω
    exact pos_scale c (f ω) hc
  rw [he, eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hc]

private lemma qp_add {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f g : Ω → ℝ) (hf : Integrable f P) (hg : Integrable g P) :
    rhoQPlus P (f+g) ≤ rhoQPlus P f + rhoQPlus P g := by
  rw [qp_norm, qp_norm, qp_norm]
  refine (eLpNorm_mono (g := (fun ω => max (f ω) 0) + (fun ω => max (g ω) 0)) ?_).trans
    (eLpNorm_add_le hf.pos_part.aestronglyMeasurable hg.pos_part.aestronglyMeasurable (by norm_num))
  intro ω
  simp only [Pi.add_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg (le_max_right _ _), abs_of_nonneg (add_nonneg (le_max_right _ _) (le_max_right _ _))]
  exact max_le (add_le_add (le_max_left _ _) (le_max_left _ _))
    (add_nonneg (le_max_right _ _) (le_max_right _ _))

private lemma mem_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ} (hf : f ∈ Lspace ℝ 1 P) : Integrable f P :=
  memLp_one_iff_integrable.mp hf

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] :
    (IsPosHomogeneous (fun ϑ : Lspace ℝ 2 P => rhoQ P ϑ) ∧
      IsSubadditive (fun ϑ : Lspace ℝ 2 P => rhoQ P ϑ)) ∧
    (IsPosHomogeneous (fun ϑ : Lspace ℝ 1 P => rhoA P ϑ) ∧
      IsSubadditive (fun ϑ : Lspace ℝ 1 P => rhoA P ϑ)) ∧
    ((∀ ϑ ∈ Lspace ℝ 1 P, ∀ c : ℝ, 0 ≤ c → rhoQPlus P (c • ϑ) = ENNReal.ofReal c * rhoQPlus P ϑ) ∧
      (∀ ϑ₁ ∈ Lspace ℝ 1 P, ∀ ϑ₂ ∈ Lspace ℝ 1 P,
        rhoQPlus P (ϑ₁ + ϑ₂) ≤ rhoQPlus P ϑ₁ + rhoQPlus P ϑ₂)) ∧
    ((∀ ϑ ∈ Lspace ℝ 1 P, ∀ c : ℝ, 0 ≤ c → rhoQMinus P (c • ϑ) = ENNReal.ofReal c * rhoQMinus P ϑ) ∧
      (∀ ϑ₁ ∈ Lspace ℝ 1 P, ∀ ϑ₂ ∈ Lspace ℝ 1 P,
        rhoQMinus P (ϑ₁ + ϑ₂) ≤ rhoQMinus P ϑ₁ + rhoQMinus P ϑ₂))  := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · intro c hc f
      have hf : MemLp f.val 2 P := f.property
      change rhoQ P (c • f.val) = c * rhoQ P f.val
      rw [q_norm P _ (hf.const_smul c), q_norm P _ hf, MemLp.toLp_const_smul,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    · intro f g
      have hf : MemLp f.val 2 P := f.property
      have hg : MemLp g.val 2 P := g.property
      change rhoQ P (f.val+g.val) ≤ rhoQ P f.val + rhoQ P g.val
      rw [q_norm P _ (hf.add hg), q_norm P _ hf, q_norm P _ hg, MemLp.toLp_add]
      exact norm_add_le _ _
  · constructor
    · intro c hc f
      change (∫ ω, |c * f.val ω| ∂P) = c * ∫ ω, |f.val ω| ∂P
      simp only [abs_mul, abs_of_nonneg hc]
      exact integral_const_mul c _
    · intro f g
      have hf := (mem_integrable f.property)
      have hg := (mem_integrable g.property)
      change (∫ ω, |f.val ω+g.val ω| ∂P) ≤ (∫ ω, |f.val ω| ∂P) + ∫ ω, |g.val ω| ∂P
      rw [← integral_add hf.abs hg.abs]
      apply integral_mono (hf.add hg).abs (hf.abs.add hg.abs)
      intro ω
      exact abs_add_le _ _
  · constructor
    · intro f _ c hc
      exact qp_scale P f c hc
    · intro f hf g hg
      exact qp_add P f g (mem_integrable hf) (mem_integrable hg)
  · constructor
    · intro f _ c hc
      change rhoQPlus P (-(c • f)) = ENNReal.ofReal c * rhoQPlus P (-f)
      rw [← smul_neg]
      exact qp_scale P (-f) c hc
    · intro f hf g hg
      change rhoQPlus P (-(f+g)) ≤ rhoQPlus P (-f) + rhoQPlus P (-g)
      simpa only [neg_add] using qp_add P (-f) (-g) (mem_integrable hf).neg (mem_integrable hg).neg
