-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_minorSection_gaussian3_of_weightZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/954e5516-d640-5e1a-a9e0-3f88bbaeb7f7

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Theorems.Thm_LanglandsTunnell_CubicInduction_archZeta30_one_eq_mul_integral_quasiChar_of_isArchCompAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_iotaGL_diagUnitGL2_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_of_minorSection_gaussian3_of_weightZero
import Theorems.Thm_Complex_mellinConvergent_cpow_mul_exp_neg_mul_and_mellin_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_minorSection_gaussian3_of_weightZero
p2m_attr_erase "simp" "LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 3200000

open MeasureTheory Real Set

namespace Z0MinorA

lemma mp_neg_Ioi : MeasurePreserving (fun x : ℝ => -x)
    ((volume : Measure ℝ).restrict (Ioi 0)) ((volume : Measure ℝ).restrict (Iio 0)) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (measurableSet_Iio (a := (0:ℝ)))
  have hpre : (Neg.neg ⁻¹' Iio (0:ℝ)) = Ioi 0 := by
    ext x; simp
  rw [hpre] at h
  exact h

lemma vol_eq_add : (volume : Measure ℝ) = volume.restrict (Ioi 0) + volume.restrict (Iio 0) := by
  have h := Measure.restrict_add_restrict_compl (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0:ℝ)))
  rw [compl_Ioi, Measure.restrict_congr_set (Iio_ae_eq_Iic (μ := (volume : Measure ℝ)) (a := 0)).symm] at h
  exact h.symm

lemma fold_fst {Z : Type*} [MeasurableSpace Z] (ν : Measure Z) [SFinite ν] (f : ℝ × Z → ℂ)
    (hf : Integrable f ((volume : Measure ℝ).prod ν)) :
    Integrable f (((volume : Measure ℝ).restrict (Ioi 0)).prod ν) ∧
    Integrable (fun p : ℝ × Z => f (-p.1, p.2)) (((volume : Measure ℝ).restrict (Ioi 0)).prod ν) ∧
    ∫ p, f p ∂((volume : Measure ℝ).prod ν) =
      ∫ p, (f p + f (-p.1, p.2)) ∂(((volume : Measure ℝ).restrict (Ioi 0)).prod ν) := by
  set μp : Measure (ℝ × Z) := ((volume : Measure ℝ).restrict (Ioi 0)).prod ν
  set μn : Measure (ℝ × Z) := ((volume : Measure ℝ).restrict (Iio 0)).prod ν
  have hsplit : (volume : Measure ℝ).prod ν = μp + μn := by
    conv_lhs => rw [vol_eq_add]
    rw [Measure.add_prod]
  rw [hsplit] at hf
  obtain ⟨hfp, hfn⟩ := integrable_add_measure.mp hf

  set e : ℝ × Z ≃ᵐ ℝ × Z := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl Z)
  have he : ∀ p : ℝ × Z, e p = (-p.1, p.2) := fun p => rfl
  have hmp : MeasurePreserving e μp μn := by
    have := mp_neg_Ioi.prod (MeasurePreserving.id ν)
    exact this
  have hfn' : Integrable (fun p : ℝ × Z => f (-p.1, p.2)) μp := by
    have := (hmp.integrable_comp_emb e.measurableEmbedding).mpr hfn
    simpa [Function.comp_def, he] using this
  refine ⟨hfp, hfn', ?_⟩
  rw [hsplit, integral_add_measure hfp hfn, integral_add hfp hfn']
  congr 1
  rw [← hmp.integral_comp' f]
  simp only [he]

lemma fold_mid {A Z : Type*} [MeasurableSpace A] [MeasurableSpace Z] (μa : Measure A) [SFinite μa]
    (ν : Measure Z) [SFinite ν] (f : A × ℝ × Z → ℂ)
    (hf : Integrable f (μa.prod ((volume : Measure ℝ).prod ν))) :
    Integrable f (μa.prod (((volume : Measure ℝ).restrict (Ioi 0)).prod ν)) ∧
    Integrable (fun p : A × ℝ × Z => f (p.1, -p.2.1, p.2.2)) (μa.prod (((volume : Measure ℝ).restrict (Ioi 0)).prod ν)) ∧
    ∫ p, f p ∂(μa.prod ((volume : Measure ℝ).prod ν)) =
      ∫ p, (f p + f (p.1, -p.2.1, p.2.2)) ∂(μa.prod (((volume : Measure ℝ).restrict (Ioi 0)).prod ν)) := by
  set μp : Measure (A × ℝ × Z) := μa.prod (((volume : Measure ℝ).restrict (Ioi 0)).prod ν)
  set μn : Measure (A × ℝ × Z) := μa.prod (((volume : Measure ℝ).restrict (Iio 0)).prod ν)
  have hsplit : μa.prod ((volume : Measure ℝ).prod ν) = μp + μn := by
    conv_lhs => rw [vol_eq_add]
    rw [Measure.add_prod, Measure.prod_add]
  rw [hsplit] at hf
  obtain ⟨hfp, hfn⟩ := integrable_add_measure.mp hf
  set e : A × ℝ × Z ≃ᵐ A × ℝ × Z :=
    (MeasurableEquiv.refl A).prodCongr ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl Z))
  have he : ∀ p : A × ℝ × Z, e p = (p.1, -p.2.1, p.2.2) := fun p => rfl
  have hmp : MeasurePreserving e μp μn := by
    have := (MeasurePreserving.id μa).prod (mp_neg_Ioi.prod (MeasurePreserving.id ν))
    exact this
  have hfn' : Integrable (fun p : A × ℝ × Z => f (p.1, -p.2.1, p.2.2)) μp := by
    have := (hmp.integrable_comp_emb e.measurableEmbedding).mpr hfn
    simpa [Function.comp_def, he] using this
  refine ⟨hfp, hfn', ?_⟩
  rw [hsplit, integral_add_measure hfp hfn, integral_add hfp hfn']
  congr 1
  rw [← hmp.integral_comp' f]
  simp only [he]

lemma subst_fst {Z : Type*} [MeasurableSpace Z] (ν : Measure Z) [SFinite ν] (f : ℝ × Z → ℂ)
    (hfm : Measurable f) (hf : Integrable f (((volume : Measure ℝ).restrict (Ioi 0)).prod ν))
    (c : Z → ℝ) (hcm : Measurable c) (hc : ∀ᵐ z ∂ν, 0 < c z) :
    Integrable (fun p : ℝ × Z => (c p.2 : ℂ) * f (c p.2 * p.1, p.2)) (((volume : Measure ℝ).restrict (Ioi 0)).prod ν) ∧
    ∫ p, f p ∂(((volume : Measure ℝ).restrict (Ioi 0)).prod ν) =
      ∫ p, (c p.2 : ℂ) * f (c p.2 * p.1, p.2) ∂(((volume : Measure ℝ).restrict (Ioi 0)).prod ν) := by
  set g : ℝ × Z → ℂ := fun p => (c p.2 : ℂ) * f (c p.2 * p.1, p.2) with hg
  have hgm : Measurable g := by
    have h1 : Measurable (fun p : ℝ × Z => (c p.2 * p.1, p.2)) :=
      ((hcm.comp measurable_snd).mul measurable_fst).prodMk measurable_snd
    exact (Complex.measurable_ofReal.comp (hcm.comp measurable_snd)).mul (hfm.comp h1)

  have hfib := (integrable_prod_iff' hf.aestronglyMeasurable).mp hf
  have key_int : ∀ z : Z, 0 < c z → IntegrableOn (fun x => f (x, z)) (Ioi 0) →
      Integrable (fun x => g (x, z)) ((volume : Measure ℝ).restrict (Ioi 0)) := by
    intro z hz hI
    have h1 : IntegrableOn (fun x => f (c z * x, z)) (Ioi 0) := by
      rw [integrableOn_Ioi_comp_mul_left_iff (fun x => f (x, z)) 0 hz, mul_zero]
      exact hI
    exact (h1.const_mul ((c z : ℝ) : ℂ))
  have key_norm : ∀ z : Z, 0 < c z →
      ∫ x in Ioi (0:ℝ), ‖g (x, z)‖ = ∫ x in Ioi (0:ℝ), ‖f (x, z)‖ := by
    intro z hz
    have h1 : (fun x => ‖g (x, z)‖) = fun x => c z * ‖f (c z * x, z)‖ := by
      funext x
      simp only [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz]
    rw [h1, integral_const_mul]
    have h2 := integral_comp_mul_left_Ioi (fun x => ‖f (x, z)‖) 0 hz
    rw [mul_zero] at h2
    rw [h2, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hz.ne', one_mul]
  have key_val : ∀ z : Z, 0 < c z →
      ∫ x in Ioi (0:ℝ), g (x, z) = ∫ x in Ioi (0:ℝ), f (x, z) := by
    intro z hz
    simp only [hg]
    rw [integral_const_mul]
    have h2 := integral_comp_mul_left_Ioi (fun x => f (x, z)) 0 hz
    rw [mul_zero] at h2
    rw [h2, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hz.ne',
      Complex.ofReal_one, one_mul]
  have hgi : Integrable g (((volume : Measure ℝ).restrict (Ioi 0)).prod ν) := by
    rw [integrable_prod_iff' hgm.aestronglyMeasurable]
    constructor
    · filter_upwards [hfib.1, hc] with z hz hcz
      exact key_int z hcz hz
    · refine hfib.2.congr ?_
      filter_upwards [hc] with z hcz
      exact (key_norm z hcz).symm
  refine ⟨hgi, ?_⟩
  rw [integral_prod_symm f hf, integral_prod_symm g hgi]
  refine integral_congr_ae ?_
  filter_upwards [hc] with z hcz
  exact (key_val z hcz).symm

end Z0MinorA

namespace Z0MinorB

lemma exp_neg_le_factorial_div_pow (u : ℝ) (hu : 0 < u) (m : ℕ) :
    Real.exp (-u) ≤ (m.factorial : ℝ) / u ^ m := by
  have h := Real.pow_div_factorial_le_exp (x := u) hu.le m
  have hm : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (div_pos hm (pow_pos hu m)), inv_div]
  exact h

lemma exists_bound_small (α : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 →
      |y| ^ α * Real.exp (-(Real.pi * (y ^ 2)⁻¹)) ≤ C := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, -α ≤ 2 * (m : ℝ) := by
    obtain ⟨m, hm⟩ := exists_nat_ge (-α)
    exact ⟨m, by nlinarith [hm, (Nat.cast_nonneg m : (0:ℝ) ≤ m)]⟩
  refine ⟨(m.factorial : ℝ) / Real.pi ^ m, by positivity, fun y hy hy1 => ?_⟩
  have hya : 0 < |y| := abs_pos.mpr hy
  have hu : 0 < Real.pi * (y ^ 2)⁻¹ := by positivity
  have h1 := exp_neg_le_factorial_div_pow _ hu m
  have h2 : (m.factorial : ℝ) / (Real.pi * (y ^ 2)⁻¹) ^ m
      = (m.factorial : ℝ) / Real.pi ^ m * |y| ^ (2 * (m : ℝ)) := by
    rw [mul_pow, inv_pow, Real.rpow_mul (abs_nonneg y), Real.rpow_two, sq_abs, Real.rpow_natCast]
    field_simp
  rw [h2] at h1
  have h4 : |y| ^ α * |y| ^ (2 * (m : ℝ)) = |y| ^ (α + 2 * (m : ℝ)) := by
    rw [← Real.rpow_add hya]
  have h5 : |y| ^ (α + 2 * (m : ℝ)) ≤ 1 := Real.rpow_le_one (abs_nonneg y) hy1 (by linarith)
  calc |y| ^ α * Real.exp (-(Real.pi * (y ^ 2)⁻¹))
      ≤ |y| ^ α * ((m.factorial : ℝ) / Real.pi ^ m * |y| ^ (2 * (m : ℝ))) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg (abs_nonneg y) α)
    _ = (m.factorial : ℝ) / Real.pi ^ m * (|y| ^ α * |y| ^ (2 * (m : ℝ))) := by ring
    _ ≤ (m.factorial : ℝ) / Real.pi ^ m * 1 := by
        rw [h4]; exact mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = _ := mul_one _

lemma bound_large_pow (α : ℝ) (hα : α ≤ -2) (y : ℝ) (hy1 : 1 ≤ |y|) :
    |y| ^ α ≤ 2 * (1 + y ^ 2)⁻¹ := by
  have hya : 0 < |y| := lt_of_lt_of_le one_pos hy1
  have hy0 : y ≠ 0 := abs_pos.mp hya
  have hy2 : 0 < y ^ 2 := by positivity
  have h5 : |y| ^ α ≤ |y| ^ (-(2:ℝ)) := Real.rpow_le_rpow_of_exponent_le hy1 hα
  have h6 : |y| ^ (-(2:ℝ)) = (y ^ 2)⁻¹ := by
    rw [Real.rpow_neg (abs_nonneg y), Real.rpow_two, sq_abs]
  have h7 : (y ^ 2)⁻¹ ≤ 2 * (1 + y ^ 2)⁻¹ := by
    rw [inv_le_comm₀ hy2 (by positivity), mul_inv, inv_inv]
    have : (1 : ℝ) ≤ y ^ 2 := by nlinarith [abs_nonneg y, sq_abs y]
    nlinarith
  exact h5.trans (h6.le.trans h7)

lemma ae_ne_zero : ∀ᵐ y : ℝ, y ≠ 0 := by
  rw [ae_iff]; simp

lemma integrable_pow (α : ℝ) (hα : α ≤ -2) :
    Integrable (fun y : ℝ => |y| ^ α * Real.exp (-(Real.pi * (y ^ 2)⁻¹))) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_bound_small α
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (2 * C₁ + 2)) ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop))
  · filter_upwards [ae_ne_zero] with y hy
    rw [Real.norm_of_nonneg (by positivity)]
    have hnn : 0 ≤ (1 + y ^ 2)⁻¹ := by positivity
    rcases le_total |y| 1 with hle | hge
    · have hA := h₁ y hy hle
      have hh : (1 : ℝ) ≤ 2 * (1 + y ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
        have : y ^ 2 ≤ 1 := by
          have := abs_nonneg y; nlinarith [sq_abs y]
        linarith
      nlinarith
    · have hA := bound_large_pow α hα y hge
      have hE : Real.exp (-(Real.pi * (y ^ 2)⁻¹)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ Real.pi * (y ^ 2)⁻¹ := by positivity
        linarith
      calc |y| ^ α * Real.exp (-(Real.pi * (y ^ 2)⁻¹))
          ≤ 2 * (1 + y ^ 2)⁻¹ * 1 := mul_le_mul hA hE (Real.exp_nonneg _) (by positivity)
        _ ≤ (2 * C₁ + 2) * (1 + y ^ 2)⁻¹ := by nlinarith

lemma integrableOn_gauss (α b : ℝ) (hb : 0 < b) :
    IntegrableOn (fun y : ℝ => y ^ α * Real.exp (-(Real.pi * (y ^ 2)⁻¹)) * Real.exp (-(b * y ^ 2)))
      (Ioi 0) := by
  obtain ⟨C₁, hC₁, h₁⟩ := exists_bound_small α

  have hg1 : IntegrableOn (fun y : ℝ => Real.exp (-(b * y ^ 2))) (Ioi 0) := by
    have := (integrable_exp_neg_mul_sq hb).integrableOn (s := Ioi 0)
    refine this.congr_fun (fun y _ => ?_) measurableSet_Ioi
    ring_nf
  have hg2 : IntegrableOn (fun y : ℝ => y ^ (max α 0) * Real.exp (-(b * y ^ 2))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_sq hb (s := max α 0) (by
      have := le_max_right α 0; linarith)
    refine this.congr_fun (fun y _ => ?_) measurableSet_Ioi
    ring_nf
  refine Integrable.mono' ((hg1.const_mul C₁).add hg2) ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : (0:ℝ) < y := hy
    rw [Real.norm_of_nonneg (by positivity)]
    have hG := Real.exp_nonneg (-(b * y ^ 2))
    rcases le_total y 1 with hle | hge
    · have hA := h₁ y hy0.ne' (by rwa [abs_of_pos hy0])
      rw [abs_of_pos hy0] at hA
      have h2 : 0 ≤ y ^ (max α 0) * Real.exp (-(b * y ^ 2)) := by positivity
      calc y ^ α * Real.exp (-(Real.pi * (y ^ 2)⁻¹)) * Real.exp (-(b * y ^ 2))
          ≤ C₁ * Real.exp (-(b * y ^ 2)) := mul_le_mul_of_nonneg_right hA hG
        _ ≤ C₁ * Real.exp (-(b * y ^ 2)) + y ^ (max α 0) * Real.exp (-(b * y ^ 2)) := by linarith
    · have hE : Real.exp (-(Real.pi * (y ^ 2)⁻¹)) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ Real.pi * (y ^ 2)⁻¹ := by positivity
        linarith
      have hp : y ^ α ≤ y ^ (max α 0) := Real.rpow_le_rpow_of_exponent_le hge (le_max_left _ _)
      have h1 : 0 ≤ C₁ * Real.exp (-(b * y ^ 2)) := by positivity
      calc y ^ α * Real.exp (-(Real.pi * (y ^ 2)⁻¹)) * Real.exp (-(b * y ^ 2))
          ≤ y ^ (max α 0) * 1 * Real.exp (-(b * y ^ 2)) := by
            apply mul_le_mul_of_nonneg_right _ hG
            exact mul_le_mul hp hE (Real.exp_nonneg _) (Real.rpow_nonneg hy0.le _)
        _ ≤ C₁ * Real.exp (-(b * y ^ 2)) + y ^ (max α 0) * Real.exp (-(b * y ^ 2)) := by linarith

lemma integrable_abs_rpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) :
    Integrable (fun x : ℝ => |x| ^ s * Real.exp (-(b * x ^ 2))) := by
  have hI : IntegrableOn (fun x : ℝ => |x| ^ s * Real.exp (-(b * x ^ 2))) (Ioi 0) := by
    refine (integrableOn_rpow_mul_exp_neg_mul_sq hb hs).congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [abs_of_pos (show (0:ℝ) < x from hx)]; ring_nf
  rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ)), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hI⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simp only [Function.comp_def, neg_sq, neg_preimage, neg_Iio, neg_zero, abs_neg]
  exact hI

noncomputable def μ₃ : Measure (ℝ × ℝ × ℝ) :=
  (volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0)))

scoped instance : SFinite μ₃ := by unfold μ₃; infer_instance

noncomputable def K (b α e l : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  (|p.1| ^ α * Real.exp (-(b * p.2.1 ^ 2 * p.1 ^ 2))) *
    (|p.2.1| ^ e * Real.exp (-(Real.pi * (p.2.1 ^ 2)⁻¹))) *
    (p.2.2 ^ l * Real.exp (-(Real.pi * (p.2.2 ^ 2)⁻¹)) * Real.exp (-(b * p.2.2 ^ 2)))

lemma K_nonneg (b α e l : ℝ) (p : ℝ × ℝ × ℝ) (hp : 0 < p.2.2) : 0 ≤ K b α e l p := by
  unfold K
  have : 0 ≤ |p.1| ^ α := Real.rpow_nonneg (abs_nonneg _) _
  have : 0 ≤ |p.2.1| ^ e := Real.rpow_nonneg (abs_nonneg _) _
  have : 0 ≤ p.2.2 ^ l := Real.rpow_nonneg hp.le _
  positivity

lemma measurable_K (b α e l : ℝ) : Measurable (K b α e l) := by
  unfold K; fun_prop

lemma integrable_u (b α e : ℝ) (hb : 0 < b) (hα : -1 < α) (he : e - α - 1 ≤ -2) :
    Integrable (fun q : ℝ × ℝ => (|q.1| ^ α * Real.exp (-(b * q.2 ^ 2 * q.1 ^ 2))) *
      (|q.2| ^ e * Real.exp (-(Real.pi * (q.2 ^ 2)⁻¹)))) ((volume : Measure ℝ).prod volume) := by
  set g : ℝ → ℝ := fun t => |t| ^ α * Real.exp (-(b * t ^ 2)) with hg
  have hgi : Integrable g := integrable_abs_rpow_mul_exp_neg_mul_sq hb hα
  set Cg : ℝ := ∫ t, g t with hCg

  have hslice : ∀ y₁ : ℝ, y₁ ≠ 0 → ∀ y : ℝ,
      |y| ^ α * Real.exp (-(b * y₁ ^ 2 * y ^ 2)) = |y₁| ^ (-α) * g (y₁ * y) := by
    intro y₁ hy₁ y
    have hya : 0 < |y₁| := abs_pos.mpr hy₁
    simp only [hg, abs_mul, Real.mul_rpow (abs_nonneg y₁) (abs_nonneg y)]
    rw [Real.rpow_neg hya.le]
    field_simp
  have hmeas : Measurable (fun q : ℝ × ℝ => (|q.1| ^ α * Real.exp (-(b * q.2 ^ 2 * q.1 ^ 2))) *
      (|q.2| ^ e * Real.exp (-(Real.pi * (q.2 ^ 2)⁻¹)))) := by fun_prop
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  constructor
  · filter_upwards [ae_ne_zero] with y₁ hy₁
    have h1 : Integrable (fun y : ℝ => g (y₁ * y)) := hgi.comp_mul_left' hy₁
    have h2 := (h1.const_mul (|y₁| ^ (-α))).mul_const (|y₁| ^ e * Real.exp (-(Real.pi * (y₁ ^ 2)⁻¹)))
    refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [hslice y₁ hy₁ y]
  · have hI : Integrable (fun y₁ : ℝ => Cg * (|y₁| ^ (e - α - 1) * Real.exp (-(Real.pi * (y₁ ^ 2)⁻¹)))) :=
      (integrable_pow (e - α - 1) he).const_mul Cg
    refine hI.congr ?_
    filter_upwards [ae_ne_zero] with y₁ hy₁
    have hya : 0 < |y₁| := abs_pos.mpr hy₁
    have hnn : ∀ y : ℝ, 0 ≤ (|y| ^ α * Real.exp (-(b * y₁ ^ 2 * y ^ 2))) *
        (|y₁| ^ e * Real.exp (-(Real.pi * (y₁ ^ 2)⁻¹))) := by
      intro y
      have : 0 ≤ |y| ^ α := Real.rpow_nonneg (abs_nonneg _) _
      have : 0 ≤ |y₁| ^ e := Real.rpow_nonneg (abs_nonneg _) _
      positivity
    simp_rw [Real.norm_of_nonneg (hnn _)]
    rw [integral_mul_const]
    simp_rw [hslice y₁ hy₁]
    rw [integral_const_mul, Measure.integral_comp_mul_left g y₁, smul_eq_mul, abs_inv]
    have h3 : |y₁| ^ (e - α - 1) = |y₁| ^ e * (|y₁| ^ (-α) * |y₁|⁻¹) := by
      rw [Real.rpow_sub hya, Real.rpow_sub hya, Real.rpow_one, Real.rpow_neg hya.le]
      field_simp
    rw [h3]; ring

lemma integrable_K (b α e l : ℝ) (hb : 0 < b) (hα : -1 < α) (he : e - α - 1 ≤ -2) :
    Integrable (K b α e l) μ₃ := by
  have hu := integrable_u b α e hb hα he
  have hv : Integrable (fun y : ℝ => y ^ l * Real.exp (-(Real.pi * (y ^ 2)⁻¹)) * Real.exp (-(b * y ^ 2)))
      ((volume : Measure ℝ).restrict (Ioi 0)) := integrableOn_gauss l b hb
  have huv := hu.mul_prod hv
  have hmp := MeasureTheory.measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ)
    ((volume : Measure ℝ).restrict (Ioi 0))
  have := (hmp.integrable_comp_emb (MeasurableEquiv.prodAssoc).measurableEmbedding (g := K b α e l)).mp
  refine this ?_
  refine huv.congr (Filter.Eventually.of_forall fun q => ?_)
  rfl

end Z0MinorB
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_minorSection_gaussian3_of_weightZero.Z0MinorB"

namespace Z0MinorEngine

open Complex

lemma subst_pointwise (w : ℂ) (x : ℝ) (hx : 0 < x) :
    ((|(-(1/2 : ℝ))| * x ^ ((-(1/2 : ℝ)) - 1)) : ℝ) •
        ((((x ^ (-(1/2 : ℝ)) : ℝ) : ℂ) ^ (-(w + 1))) *
          ((Real.exp (-(Real.pi * (((x ^ (-(1/2 : ℝ)) : ℝ)) ^ 2)⁻¹)) : ℝ) : ℂ)) =
      (1 / 2 : ℂ) * ((x : ℂ) ^ (w / 2 - 1) •
        (((x : ℂ) ^ ((0 : ℝ) : ℂ)) * Complex.exp (-((Real.pi : ℂ) * (x : ℂ))))) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'

  have hexp : (((x ^ (-(1/2 : ℝ)) : ℝ)) ^ 2)⁻¹ = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
    rw [Real.rpow_neg hx.le, Real.rpow_one, inv_inv]
  rw [hexp]

  have hlog : (Complex.log (x : ℂ) * ((-(1/2 : ℝ) : ℝ) : ℂ)).im = 0 := by
    rw [← Complex.ofReal_log hx.le, ← Complex.ofReal_mul, Complex.ofReal_im]
  have hp1 : (((x ^ (-(1/2 : ℝ)) : ℝ) : ℂ)) ^ (-(w + 1)) = (x : ℂ) ^ (((-(1/2 : ℝ) : ℝ) : ℂ) * (-(w + 1))) := by
    rw [Complex.ofReal_cpow hx.le, ← Complex.cpow_mul]
    · rw [hlog]; exact neg_lt_zero.mpr Real.pi_pos
    · rw [hlog]; exact Real.pi_pos.le
  have hp2 : ((|(-(1/2 : ℝ))| * x ^ ((-(1/2 : ℝ)) - 1) : ℝ) : ℂ) = (1 / 2 : ℂ) * (x : ℂ) ^ (((-(1/2 : ℝ) - 1 : ℝ)) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.le]
    congr 1
    rw [abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    push_cast; ring
  have hp0 : (x : ℂ) ^ ((0 : ℝ) : ℂ) = 1 := by simp
  have hE : ((Real.exp (-(Real.pi * x)) : ℝ) : ℂ) = Complex.exp (-((Real.pi : ℂ) * (x : ℂ))) := by
    push_cast; ring_nf
  rw [Complex.real_smul, hp1, hp2, hE, hp0, one_mul, smul_eq_mul]
  have hcomb : (x : ℂ) ^ (((-(1/2 : ℝ) - 1 : ℝ)) : ℂ) * (x : ℂ) ^ (((-(1/2 : ℝ) : ℝ) : ℂ) * (-(w + 1))) =
      (x : ℂ) ^ (w / 2 - 1) := by
    rw [← Complex.cpow_add _ _ hx0]
    congr 1
    push_cast; ring
  calc (1 / 2 : ℂ) * (x : ℂ) ^ (((-(1/2 : ℝ) - 1 : ℝ)) : ℂ) *
        ((x : ℂ) ^ (((-(1/2 : ℝ) : ℝ) : ℂ) * (-(w + 1))) * Complex.exp (-((Real.pi : ℂ) * (x : ℂ))))
      = (1 / 2 : ℂ) * ((x : ℂ) ^ (((-(1/2 : ℝ) - 1 : ℝ)) : ℂ) * (x : ℂ) ^ (((-(1/2 : ℝ) : ℝ) : ℂ) * (-(w + 1)))) *
          Complex.exp (-((Real.pi : ℂ) * (x : ℂ))) := by ring
    _ = _ := by rw [hcomb]; ring

theorem integrableOn_and_integral_cpow_neg_mul_exp_neg_pi_div_sq (w : ℂ) (hw : 0 < w.re) :
    IntegrableOn (fun y : ℝ => (y : ℂ) ^ (-(w + 1)) * ((Real.exp (-(Real.pi * (y ^ 2)⁻¹)) : ℝ) : ℂ)) (Ioi 0) ∧
    ∫ y in Ioi (0:ℝ), (y : ℂ) ^ (-(w + 1)) * ((Real.exp (-(Real.pi * (y ^ 2)⁻¹)) : ℝ) : ℂ) =
      Complex.Gammaℝ w / 2 := by
  set g : ℝ → ℂ := fun y => (y : ℂ) ^ (-(w + 1)) * ((Real.exp (-(Real.pi * (y ^ 2)⁻¹)) : ℝ) : ℂ) with hg
  set F : ℝ → ℂ := fun t : ℝ => ((t : ℂ) ^ ((0 : ℝ) : ℂ)) * Complex.exp (-((Real.pi : ℂ) * (t : ℂ))) with hF
  obtain ⟨hMC, hM⟩ := Complex.mellinConvergent_cpow_mul_exp_neg_mul_and_mellin_eq 0 Real.pi Real.pi_pos (w / 2)
    (by simpa using half_pos hw)
  have hp : (-(1/2 : ℝ)) ≠ 0 := by norm_num

  have hpt : ∀ x ∈ Ioi (0:ℝ),
      ((|(-(1/2 : ℝ))| * x ^ ((-(1/2 : ℝ)) - 1)) : ℝ) • g (x ^ (-(1/2 : ℝ))) =
        (1 / 2 : ℂ) * ((x : ℂ) ^ (w / 2 - 1) • F x) := by
    intro x hx
    rw [hg, hF]
    exact subst_pointwise w x hx
  have hint : IntegrableOn (fun x : ℝ => (1 / 2 : ℂ) * ((x : ℂ) ^ (w / 2 - 1) • F x)) (Ioi 0) := by
    have := hMC.const_mul (1 / 2 : ℂ)
    exact this
  have hint' : IntegrableOn (fun x : ℝ => ((|(-(1/2 : ℝ))| * x ^ ((-(1/2 : ℝ)) - 1)) : ℝ) • g (x ^ (-(1/2 : ℝ)))) (Ioi 0) :=
    hint.congr_fun (fun x hx => (hpt x hx).symm) measurableSet_Ioi
  refine ⟨(integrableOn_Ioi_comp_rpow_iff g hp).mp hint', ?_⟩
  rw [← integral_comp_rpow_Ioi g hp, setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  have hmel : ∫ x in Ioi (0:ℝ), (x : ℂ) ^ (w / 2 - 1) • F x = mellin F (w / 2) := rfl
  rw [hmel, hM, Complex.Gammaℝ_def]
  simp only [Complex.ofReal_zero, add_zero]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hinv : (1 / (Real.pi : ℂ)) ^ (w / 2) = (Real.pi : ℂ) ^ (-w / 2) := by
    rw [one_div, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_ne_zero.symm),
      neg_div, Complex.cpow_neg]
  rw [hinv]
  ring

end Z0MinorEngine
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_minorSection_gaussian3_of_weightZero.Z0MinorB"

open NumberField AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell LanglandsTunnell.CubicInduction

namespace Z0MinorC

lemma zmod2_cases : ∀ a₃ : ZMod 2, a₃ = 0 ∨ a₃ = 1 := by decide

lemma eps_of_he (a₃ : ZMod 2) (e : ℤ) (he : ((e : ZMod 2)) = a₃ + 1) :
    (if ((e : ZMod 2)) = 0 then (1:ℂ) else -1) = -(if a₃ = 0 then (1:ℂ) else -1) ∧
    ((-1 : ℂ) ^ a₃.val) = (if a₃ = 0 then (1:ℂ) else -1) := by
  rw [he]
  rcases zmod2_cases a₃ with rfl | rfl
  · simp
  · have h1 : ((1 : ZMod 2) + 1) = 0 := by decide
    have h2 : (1 : ZMod 2) ≠ 0 := by decide
    simp [h1, h2, ZMod.val_one]

lemma quasiChar_neg (u : ℂ) (a : ZMod 2) (x : ℝ) :
    ArchR.quasiChar u a (-x) = (if a = 0 then (1:ℂ) else -1) * ArchR.quasiChar u a x := by
  unfold ArchR.quasiChar
  rw [abs_neg, Left.sign_neg]
  split_ifs <;> push_cast <;> ring

lemma quasiChar_pos (u : ℂ) (a : ZMod 2) (x : ℝ) (hx : 0 < x) :
    ArchR.quasiChar u a x = (x : ℂ) ^ u := by
  unfold ArchR.quasiChar
  rw [abs_of_pos hx, sign_pos hx]
  split_ifs <;> simp

lemma quasiChar_zero_pos (a : ZMod 2) (x : ℝ) (hx : 0 < x) : ArchR.quasiChar 0 a x = 1 := by
  rw [quasiChar_pos 0 a x hx, Complex.cpow_zero]

lemma norm_quasiChar (u : ℂ) (a : ZMod 2) (t : ℝ) (ht : t ≠ 0) :
    ‖ArchR.quasiChar u a t‖ = |t| ^ u.re := by
  rw [ArchR.quasiChar, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.mpr ht)]
  have : ‖(if a = 0 then (1 : ℂ) else ((SignType.sign t : ℝ) : ℂ))‖ = 1 := by
    split_ifs
    · simp
    · rcases lt_or_gt_of_ne ht with h | h
      · rw [sign_neg h]; simp
      · rw [sign_pos h]; simp
  rw [this, mul_one]

lemma continuousOn_quasiChar (u : ℂ) (a : ZMod 2) :
    ContinuousOn (fun t : ℝ => ArchR.quasiChar u a t) {0}ᶜ := by
  intro t ht
  have ht' : t ≠ 0 := ht
  apply ContinuousAt.continuousWithinAt
  unfold ArchR.quasiChar
  apply ContinuousAt.mul
  · have h1 : ContinuousAt (fun t : ℝ => ((|t| : ℝ) : ℂ)) t :=
      (Complex.continuous_ofReal.comp continuous_abs).continuousAt
    have h2 : ContinuousAt (fun z : ℂ => z ^ u) ((|t| : ℝ) : ℂ) :=
      continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr (abs_pos.mpr ht'))
    exact ContinuousAt.comp (f := fun t : ℝ => ((|t| : ℝ) : ℂ)) (g := fun z : ℂ => z ^ u) h2 h1
  · split_ifs
    · exact continuousAt_const
    · have h3 : ContinuousAt (fun s : SignType => ((s : ℝ) : ℂ)) (SignType.sign t) :=
        continuous_of_discreteTopology.continuousAt
      exact h3.comp (continuousAt_sign_of_ne_zero ht')

lemma measurable_quasiChar (u : ℂ) (a : ZMod 2) :
    Measurable (fun t : ℝ => ArchR.quasiChar u a t) :=
  measurable_of_continuousOn_compl_singleton 0 (continuousOn_quasiChar u a)

lemma continuous_coords_diagOne :
    Continuous (fun t : ℝ => (Matrix.of.symm (ArchR.diagOne t) : Fin 2 → Fin 2 → ℝ)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [ArchR.diagOne] <;> fun_prop

lemma continuousOn_W_diagOne {P₂ : RealArchParam} (D : ArchDatumR P₂) :
    ContinuousOn (fun t : ℝ => D.W (ArchR.diagOne t)) {0}ᶜ := by
  have hW : ContinuousOn (ArchR.asPi D.W) ArchR.glSet := D.smooth.continuousOn
  have hcomp := hW.comp continuous_coords_diagOne.continuousOn (s := {0}ᶜ) ?_
  · refine hcomp.congr ?_
    intro t _
    simp [ArchR.asPi, Function.comp]
  · intro t ht
    have ht' : t ≠ 0 := ht
    show (Matrix.of (Matrix.of.symm (ArchR.diagOne t))).det ≠ 0
    rw [Equiv.apply_symm_apply, ArchR.diagOne, Matrix.det_fin_two_of]
    simpa using ht'

lemma measurable_W_diagOne {P₂ : RealArchParam} (D : ArchDatumR P₂) :
    Measurable (fun t : ℝ => D.W (ArchR.diagOne t)) :=
  measurable_of_continuousOn_compl_singleton 0 (continuousOn_W_diagOne D)

lemma exists_bound_W_top {P₂ : RealArchParam} (D : ArchDatumR P₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| → ‖D.W (ArchR.diagOne t)‖ ≤ C := by
  obtain ⟨C, hC⟩ := D.decay_top 0 0
  refine ⟨max C 0, le_max_right _ _, fun t ht => ?_⟩
  have h := hC t 1 (by simp [ArchR.IsK]) ht
  rw [norm_iteratedFDerivWithin_zero] at h
  have h' : ‖D.W (ArchR.diagOne t)‖ ≤ C * |t| ^ (-((0:ℕ) : ℝ)) := by
    simpa [ArchR.asPi, ArchR.diagOneMulCoords] using h
  simp only [CharP.cast_eq_zero, neg_zero, Real.rpow_zero, mul_one] at h'
  exact h'.trans (le_max_left _ _)

lemma exists_bound_W_zero {P₂ : RealArchParam} (D : ArchDatumR P₂) :
    ∃ C σ : ℝ, 0 ≤ C ∧ 0 ≤ σ ∧ ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
      ‖D.W (ArchR.diagOne t)‖ ≤ C * |t| ^ (-σ) := by
  obtain ⟨C, σ, hC⟩ := D.decay_zero 0
  refine ⟨max C 0, max σ 0, le_max_right _ _, le_max_right _ _, fun t ht ht1 => ?_⟩
  have h := hC t 1 (by simp [ArchR.IsK]) ht ht1
  rw [norm_iteratedFDerivWithin_zero] at h
  have h' : ‖D.W (ArchR.diagOne t)‖ ≤ C * |t| ^ (-σ) := by
    simpa [ArchR.asPi, ArchR.diagOneMulCoords] using h
  have hta : 0 < |t| := abs_pos.mpr ht
  have h1 : |t| ^ (-σ) ≤ |t| ^ (-(max σ 0)) :=
    Real.rpow_le_rpow_of_exponent_ge hta ht1 (by simp)
  calc ‖D.W (ArchR.diagOne t)‖ ≤ C * |t| ^ (-σ) := h'
    _ ≤ max C 0 * |t| ^ (-σ) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hta.le _)
    _ ≤ max C 0 * |t| ^ (-(max σ 0)) := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)

lemma exists_bound_W {P₂ : RealArchParam} (D : ArchDatumR P₂) :
    ∃ C σ : ℝ, 0 ≤ C ∧ 0 ≤ σ ∧ ∀ t : ℝ, t ≠ 0 →
      ‖D.W (ArchR.diagOne t)‖ ≤ C * (1 + |t| ^ (-σ)) := by
  obtain ⟨C₀, σ, hC₀, hσ, h₀⟩ := exists_bound_W_zero D
  obtain ⟨C₁, hC₁, h₁⟩ := exists_bound_W_top D
  refine ⟨max C₀ C₁, σ, le_max_of_le_left hC₀, hσ, fun t ht => ?_⟩
  have hta : 0 < |t| := abs_pos.mpr ht
  have hp : 0 ≤ |t| ^ (-σ) := Real.rpow_nonneg hta.le _
  rcases le_total |t| 1 with hle | hge
  · calc ‖D.W (ArchR.diagOne t)‖ ≤ C₀ * |t| ^ (-σ) := h₀ t ht hle
      _ ≤ max C₀ C₁ * |t| ^ (-σ) := mul_le_mul_of_nonneg_right (le_max_left _ _) hp
      _ ≤ max C₀ C₁ * (1 + |t| ^ (-σ)) := by
          apply mul_le_mul_of_nonneg_left _ (le_max_of_le_left hC₀); linarith
  · calc ‖D.W (ArchR.diagOne t)‖ ≤ C₁ := h₁ t hge
      _ ≤ max C₀ C₁ * 1 := by simp
      _ ≤ max C₀ C₁ * (1 + |t| ^ (-σ)) := by
          apply mul_le_mul_of_nonneg_left _ (le_max_of_le_left hC₀); linarith

variable {P₂ : RealArchParam}

noncomputable def Fk (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ) (y y₁ y₂ : ℝ) : ℂ :=
  ArchR.quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ *
    (((y₂ ^ 2 / y₁ * (1 - a * y * y₁ ^ 2)) : ℝ) : ℂ) *
    (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + a ^ 2 * y₂ ^ 2 + a ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
    (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
    D.W (ArchR.diagOne (a * y * y₁ / y₂))

noncomputable def wt (e : ℤ) (s : ℂ) (y : ℝ) : ℂ :=
  ArchR.quasiChar 0 (e : ZMod 2) y * ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹

noncomputable def Fw (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ) (e : ℤ) (s : ℂ)
    (p : ℝ × ℝ × ℝ) : ℂ :=
  Fk D u₃ a₃ a p.1 p.2.1 p.2.2 * wt e s p.1

noncomputable def gW (D : ArchDatumR P₂) (a₃ : ZMod 2) (a τ : ℝ) : ℂ :=
  D.W (ArchR.diagOne (a * τ)) - (-1 : ℂ) ^ a₃.val * D.W (ArchR.diagOne (-(a * τ)))

noncomputable def Q (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ) (s : ℂ) (y y₁ y₂ : ℝ) : ℂ :=
  ArchR.quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * (((y₂ ^ 2 / y₁ : ℝ)) : ℂ) *
    (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + a ^ 2 * y₂ ^ 2 + a ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
    (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
    gW D a₃ a (y * y₁ / y₂) *
    (((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹)

noncomputable def Hint (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ) (σ' w : ℝ) : ℂ :=
  (D.W (ArchR.diagOne (a * (σ' / w))) - (-1 : ℂ) ^ a₃.val * D.W (ArchR.diagOne (-(a * (σ' / w))))) *
    (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ (-u₃) *
    (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ)

noncomputable def φ₁ (u₃ s : ℂ) (y₁ : ℝ) : ℂ :=
  (y₁ : ℂ) ^ (-((s + u₃ + 1) + 1)) * ((Real.exp (-(Real.pi * (y₁ ^ 2)⁻¹)) : ℝ) : ℂ)

noncomputable def R₂ (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ) (s : ℂ) (σ' w : ℝ) : ℂ :=
  ((σ' : ℂ) ^ ((s - 1) - 1) * ((Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℝ) : ℂ)) * Hint D u₃ a₃ a σ' w

lemma fold_pointwise (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ) (e : ℤ) (s : ℂ)
    (he : ((e : ZMod 2)) = a₃ + 1) (y y₁ y₂ : ℝ) (hy : 0 < y) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) :
    (Fw D u₃ a₃ a e s (y, y₁, y₂) + Fw D u₃ a₃ a e s (y, -y₁, y₂)) +
      (Fw D u₃ a₃ a e s (-y, y₁, y₂) + Fw D u₃ a₃ a e s (-y, -y₁, y₂)) =
      2 * Q D u₃ a₃ a s y y₁ y₂ := by
  obtain ⟨hε, hε₃⟩ := eps_of_he a₃ e he
  set ε₃ : ℂ := (if a₃ = 0 then (1:ℂ) else -1) with hε₃def
  have hε₃sq : ε₃ * ε₃ = 1 := by
    rw [hε₃def]; split_ifs <;> norm_num
  simp only [Fw, Fk, wt, Q, gW]

  have r1 : (-y₁ * y₂)⁻¹ = -(y₁ * y₂)⁻¹ := by rw [neg_mul, inv_neg]
  have r2 : (y₂ ^ 2 / -y₁ * (1 - a * y * (-y₁) ^ 2)) = -(y₂ ^ 2 / y₁ * (1 - a * y * y₁ ^ 2)) := by ring
  have r3 : (y₂ ^ 2 / y₁ * (1 - a * -y * y₁ ^ 2)) = (y₂ ^ 2 / y₁ * (1 + a * y * y₁ ^ 2)) := by ring
  have r4 : (y₂ ^ 2 / -y₁ * (1 - a * -y * (-y₁) ^ 2)) = -(y₂ ^ 2 / y₁ * (1 + a * y * y₁ ^ 2)) := by ring
  have r5 : (-y₁) ^ 2 = y₁ ^ 2 := neg_sq y₁
  have r6 : (-y) ^ 2 = y ^ 2 := neg_sq y
  have r7 : a * y * -y₁ / y₂ = -(a * (y * y₁ / y₂)) := by ring
  have r8 : a * -y * y₁ / y₂ = -(a * (y * y₁ / y₂)) := by ring
  have r9 : a * -y * -y₁ / y₂ = a * (y * y₁ / y₂) := by ring
  have r10 : a * y * y₁ / y₂ = a * (y * y₁ / y₂) := by ring
  rw [r1, r2, r3, r4, quasiChar_neg, quasiChar_neg, quasiChar_zero_pos _ y hy, hε, hε₃, abs_neg]
  simp only [r5, r6, r7, r8, r9, r10]
  rw [← hε₃def]
  push_cast
  set χ := ArchR.quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹
  set Wp := D.W (ArchR.diagOne (a * (y * y₁ / y₂)))
  set Wm := D.W (ArchR.diagOne (-(a * (y * y₁ / y₂))))
  set Ω := ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)
  set E := Complex.exp (-((Real.pi : ℂ) * (((y₁ : ℂ) ^ 2)⁻¹ + ((y₂ : ℂ) ^ 2)⁻¹ + (a : ℂ) ^ 2 * (y₂ : ℂ) ^ 2 +
    (a : ℂ) ^ 2 * (y : ℂ) ^ 2 * (y₁ : ℂ) ^ 2)))
  set P := ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹
  linear_combination (χ * ((y₂ : ℂ) ^ 2 / (y₁ : ℂ) * (1 + (a : ℂ) * (y : ℂ) * (y₁ : ℂ) ^ 2)) * E * Ω * Wp *
    (((|y| : ℝ) : ℂ) ^ (s - 1)) * ((|y| : ℝ) : ℂ)⁻¹) * hε₃sq

lemma cpow_inv_ofReal_pos (x : ℝ) (hx : 0 < x) (r : ℂ) : ((x⁻¹ : ℝ) : ℂ) ^ r = (x : ℂ) ^ (-r) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow, Complex.cpow_neg]
  rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm

lemma subst_pointwise (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ) (s : ℂ)
    (σ' y₁ y₂ : ℝ) (hσ : 0 < σ') (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) :
    ((y₁⁻¹ : ℝ) : ℂ) * Q D u₃ a₃ a s (y₁⁻¹ * σ') y₁ y₂ = φ₁ u₃ s y₁ * R₂ D u₃ a₃ a s σ' y₂ := by
  have hy₁0 : y₁ ≠ 0 := hy₁.ne'
  have hy₂0 : y₂ ≠ 0 := hy₂.ne'
  have hσ0 : σ' ≠ 0 := hσ.ne'
  have cy₁ : (y₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy₁0
  have cy₂ : (y₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy₂0
  have cσ : (σ' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hσ0
  simp only [Q, φ₁, R₂, Hint, gW]

  have r1 : a * (y₁⁻¹ * σ' * y₁ / y₂) = a * (σ' / y₂) := by field_simp
  rw [r1]

  have hpos12 : 0 < (y₁ * y₂)⁻¹ := by positivity
  have hposy : 0 < y₁⁻¹ * σ' := by positivity
  rw [quasiChar_pos _ _ _ hpos12, abs_of_pos hposy]

  have p1 : (((y₁ * y₂)⁻¹ : ℝ) : ℂ) ^ (u₃ + 2) = (y₁ : ℂ) ^ (-(u₃ + 2)) * (y₂ : ℂ) ^ (-(u₃ + 2)) := by
    rw [mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
      cpow_inv_ofReal_pos y₁ hy₁, cpow_inv_ofReal_pos y₂ hy₂]
  have p2 : (((y₁⁻¹ * σ') : ℝ) : ℂ) ^ (s - 1) = (y₁ : ℂ) ^ (-(s - 1)) * (σ' : ℂ) ^ (s - 1) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by positivity) hσ.le, cpow_inv_ofReal_pos y₁ hy₁]
  have p3 : (y₁ : ℂ) ^ (-((s + u₃ + 1) + 1)) = (y₁ : ℂ) ^ (-(u₃ + 2)) * (y₁ : ℂ) ^ (-(s - 1)) * (y₁ : ℂ)⁻¹ := by
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _ cy₁, ← Complex.cpow_add _ _ cy₁]
    congr 1; ring
  have p4 : (y₂ : ℂ) ^ (-u₃) = (y₂ : ℂ) ^ (-(u₃ + 2)) * (y₂ : ℂ) ^ 2 := by
    rw [← Complex.cpow_two, ← Complex.cpow_add _ _ cy₂]
    congr 1; ring
  have p5 : (σ' : ℂ) ^ ((s - 1) - 1) = (σ' : ℂ) ^ (s - 1) * (σ' : ℂ)⁻¹ := by
    rw [Complex.cpow_sub _ _ cσ, Complex.cpow_one, div_eq_mul_inv]
  rw [p1, p2, p3, p4, p5, abs_of_pos hy₂]

  have e1 : ((Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + a ^ 2 * y₂ ^ 2 + a ^ 2 * (y₁⁻¹ * σ') ^ 2 * y₁ ^ 2))) : ℝ) : ℂ)
      = ((Real.exp (-(Real.pi * (y₁ ^ 2)⁻¹)) : ℝ) : ℂ) * ((Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℝ) : ℂ) *
        ((Real.exp (-(Real.pi * ((y₂ ^ 2)⁻¹ + a ^ 2 * y₂ ^ 2))) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
    congr 2
    field_simp
    ring
  rw [e1]
  push_cast
  field_simp

lemma measurable_Fk3 (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ) :
    Measurable (fun p : ℝ × ℝ × ℝ => Fk D u₃ a₃ a p.1 p.2.1 p.2.2) := by
  have m1 : Measurable (fun p : ℝ × ℝ × ℝ => ArchR.quasiChar (u₃ + 2) a₃ (p.2.1 * p.2.2)⁻¹) :=
    (measurable_quasiChar (u₃ + 2) a₃).comp (by fun_prop)
  have m2 : Measurable (fun p : ℝ × ℝ × ℝ => (((p.2.2 ^ 2 / p.2.1 * (1 - a * p.1 * p.2.1 ^ 2)) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (by fun_prop)
  have m3 : Measurable (fun p : ℝ × ℝ × ℝ => (Real.exp (-(Real.pi * ((p.2.1 ^ 2)⁻¹ + (p.2.2 ^ 2)⁻¹ +
      a ^ 2 * p.2.2 ^ 2 + a ^ 2 * p.1 ^ 2 * p.2.1 ^ 2))) : ℂ)) :=
    Complex.measurable_ofReal.comp (by fun_prop)
  have m4 : Measurable (fun p : ℝ × ℝ × ℝ => ArchR.centralChar P₂ p.2.2) :=
    (measurable_quasiChar P₂.centralExponent P₂.centralSign).comp (by fun_prop)
  have m5 : Measurable (fun p : ℝ × ℝ × ℝ => (((|p.2.2| : ℝ)) : ℂ)) :=
    Complex.measurable_ofReal.comp (by fun_prop)
  have m6 : Measurable (fun p : ℝ × ℝ × ℝ => D.W (ArchR.diagOne (a * p.1 * p.2.1 / p.2.2))) :=
    (measurable_W_diagOne D).comp (by fun_prop)
  exact ((((m1.mul m2).mul m3).mul (m4.mul m5)).mul m6)

lemma measurable_wt (e : ℤ) (s : ℂ) : Measurable (wt e s) := by
  unfold wt
  have m1 : Measurable (fun y : ℝ => ArchR.quasiChar 0 (e : ZMod 2) y) := measurable_quasiChar 0 _
  have m2 : Measurable (fun y : ℝ => ((|y| : ℝ) : ℂ) ^ (s - 1)) := by fun_prop
  have m3 : Measurable (fun y : ℝ => ((|y| : ℝ) : ℂ)⁻¹) := by fun_prop
  exact (m1.mul m2).mul m3

lemma measurable_Fw (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ) (e : ℤ) (s : ℂ) :
    Measurable (Fw D u₃ a₃ a e s) := by
  unfold Fw
  exact (measurable_Fk3 D u₃ a₃ a).mul ((measurable_wt e s).comp measurable_fst)

lemma measurable_Q3 (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ) (s : ℂ) :
    Measurable (fun p : ℝ × ℝ × ℝ => Q D u₃ a₃ a s p.1 p.2.1 p.2.2) := by
  have m1 : Measurable (fun p : ℝ × ℝ × ℝ => ArchR.quasiChar (u₃ + 2) a₃ (p.2.1 * p.2.2)⁻¹) :=
    (measurable_quasiChar (u₃ + 2) a₃).comp (by fun_prop)
  have m2 : Measurable (fun p : ℝ × ℝ × ℝ => (((p.2.2 ^ 2 / p.2.1) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (by fun_prop)
  have m3 : Measurable (fun p : ℝ × ℝ × ℝ => (Real.exp (-(Real.pi * ((p.2.1 ^ 2)⁻¹ + (p.2.2 ^ 2)⁻¹ +
      a ^ 2 * p.2.2 ^ 2 + a ^ 2 * p.1 ^ 2 * p.2.1 ^ 2))) : ℂ)) :=
    Complex.measurable_ofReal.comp (by fun_prop)
  have m4 : Measurable (fun p : ℝ × ℝ × ℝ => ArchR.centralChar P₂ p.2.2) :=
    (measurable_quasiChar P₂.centralExponent P₂.centralSign).comp (by fun_prop)
  have m5 : Measurable (fun p : ℝ × ℝ × ℝ => (((|p.2.2| : ℝ)) : ℂ)) :=
    Complex.measurable_ofReal.comp (by fun_prop)
  have m6 : Measurable (fun p : ℝ × ℝ × ℝ => D.W (ArchR.diagOne (a * (p.1 * p.2.1 / p.2.2)))) :=
    (measurable_W_diagOne D).comp (by fun_prop)
  have m7 : Measurable (fun p : ℝ × ℝ × ℝ => D.W (ArchR.diagOne (-(a * (p.1 * p.2.1 / p.2.2))))) :=
    (measurable_W_diagOne D).comp (by fun_prop)
  have m8 : Measurable (fun p : ℝ × ℝ × ℝ => gW D a₃ a (p.1 * p.2.1 / p.2.2)) := by
    unfold gW; exact m6.sub (m7.const_mul _)
  have m9 : Measurable (fun p : ℝ × ℝ × ℝ => ((|p.1| : ℝ) : ℂ) ^ (s - 1) * ((|p.1| : ℝ) : ℂ)⁻¹) := by fun_prop
  exact (((((m1.mul m2).mul m3).mul (m4.mul m5)).mul m8).mul m9)

open Z0MinorB

lemma abs_inv_mul_rpow (r : ℝ) (y₁ y₂ : ℝ) (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) :
    |(y₁ * y₂)⁻¹| ^ r = |y₁| ^ (-r) * y₂ ^ (-r) := by
  have hya : 0 < |y₁| := abs_pos.mpr hy₁
  rw [abs_inv, abs_mul, abs_of_pos hy₂, Real.inv_rpow (by positivity), Real.mul_rpow hya.le hy₂.le,
    Real.rpow_neg hya.le, Real.rpow_neg hy₂.le, mul_inv]

lemma merge_y₂ (r γ : ℝ) (y₂ : ℝ) (hy₂ : 0 < y₂) :
    y₂ ^ (-(r + 2)) * y₂ ^ 2 * (y₂ ^ γ * y₂) = y₂ ^ (γ - r + 1) := by
  have h3 : y₂ ^ 2 = y₂ ^ (2 : ℝ) := by rw [Real.rpow_two]
  rw [h3]
  conv_lhs => rw [show y₂ ^ γ * y₂ = y₂ ^ γ * y₂ ^ (1:ℝ) by rw [Real.rpow_one]]
  rw [← Real.rpow_add hy₂, ← Real.rpow_add hy₂, ← Real.rpow_add hy₂]
  congr 1; ring

lemma norm_Fw (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ) (e : ℤ) (s : ℂ)
    (y y₁ y₂ : ℝ) (hy : y ≠ 0) (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) :
    ‖Fw D u₃ a₃ a e s (y, y₁, y₂)‖ =
      K (Real.pi * a ^ 2) (s.re - 2) (-u₃.re - 3) (P₂.centralExponent.re - u₃.re + 1) (y, y₁, y₂) *
        |1 - a * y * y₁ ^ 2| * ‖D.W (ArchR.diagOne (a * y * y₁ / y₂))‖ := by
  have hya : 0 < |y| := abs_pos.mpr hy
  have hy1a : 0 < |y₁| := abs_pos.mpr hy₁
  have h12 : (y₁ * y₂)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero hy₁ hy₂.ne')
  simp only [Fw, Fk, wt, K, norm_mul, norm_inv]
  rw [norm_quasiChar _ _ _ h12, norm_quasiChar _ _ _ hy, ArchR.centralChar, norm_quasiChar _ _ _ hy₂.ne',
    Complex.norm_cpow_eq_rpow_re_of_pos hya]
  have hre : (u₃ + 2).re = u₃.re + 2 := by simp
  simp only [hre, Complex.zero_re, Real.rpow_zero, Complex.sub_re, Complex.one_re, Complex.norm_real,
    Real.norm_eq_abs, abs_abs, abs_of_pos hy₂, abs_of_pos (Real.exp_pos _)]
  rw [abs_inv_mul_rpow (u₃.re + 2) y₁ y₂ hy₁ hy₂]
  have n2 : |y₂ ^ 2 / y₁ * (1 - a * y * y₁ ^ 2)| = y₂ ^ 2 * |y₁|⁻¹ * |1 - a * y * y₁ ^ 2| := by
    rw [abs_mul, abs_div, abs_of_pos (pow_pos hy₂ 2), div_eq_mul_inv]
  rw [n2]
  have hE : Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + a ^ 2 * y₂ ^ 2 + a ^ 2 * y ^ 2 * y₁ ^ 2))) =
      Real.exp (-(Real.pi * a ^ 2 * y₁ ^ 2 * y ^ 2)) * Real.exp (-(Real.pi * (y₁ ^ 2)⁻¹)) *
        (Real.exp (-(Real.pi * (y₂ ^ 2)⁻¹)) * Real.exp (-(Real.pi * a ^ 2 * y₂ ^ 2))) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [hE]
  have m1 : |y₁| ^ (-u₃.re - 3) = |y₁| ^ (-(u₃.re + 2)) * |y₁|⁻¹ := by
    rw [show -u₃.re - 3 = -(u₃.re + 2) - 1 by ring, Real.rpow_sub_one hy1a.ne', div_eq_mul_inv]
  have m2 : |y| ^ (s.re - 2) = |y| ^ (s.re - 1) * |y|⁻¹ := by
    rw [show s.re - 2 = (s.re - 1) - 1 by ring, Real.rpow_sub_one hya.ne', div_eq_mul_inv]
  rw [m1, m2, ← merge_y₂ u₃.re P₂.centralExponent.re y₂ hy₂]
  ring

lemma K_shift (b s₀ r l σ : ℝ) (y y₁ y₂ : ℝ) (hy : y ≠ 0) (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) :
    K b (s₀ - 1) (-r - 1) l (y, y₁, y₂) = K b (s₀ - 2) (-r - 3) l (y, y₁, y₂) * (|y| * y₁ ^ 2) ∧
    K b (s₀ - 2 - σ) (-r - 3 - σ) (l + σ) (y, y₁, y₂) =
      K b (s₀ - 2) (-r - 3) l (y, y₁, y₂) * (|y| ^ (-σ) * |y₁| ^ (-σ) * y₂ ^ σ) ∧
    K b (s₀ - 1 - σ) (-r - 1 - σ) (l + σ) (y, y₁, y₂) =
      K b (s₀ - 2) (-r - 3) l (y, y₁, y₂) * (|y| * y₁ ^ 2) * (|y| ^ (-σ) * |y₁| ^ (-σ) * y₂ ^ σ) := by
  have hya : 0 < |y| := abs_pos.mpr hy
  have hy1a : 0 < |y₁| := abs_pos.mpr hy₁
  have e1 : |y| ^ (s₀ - 1) = |y| ^ (s₀ - 2) * |y| := by
    rw [show s₀ - 1 = (s₀ - 2) + 1 by ring, Real.rpow_add_one hya.ne']
  have e2 : |y₁| ^ (-r - 1) = |y₁| ^ (-r - 3) * y₁ ^ 2 := by
    rw [show -r - 1 = (-r - 3) + 2 by ring, Real.rpow_add hy1a, Real.rpow_two, sq_abs]
  have e3 : |y| ^ (s₀ - 2 - σ) = |y| ^ (s₀ - 2) * |y| ^ (-σ) := by
    rw [show s₀ - 2 - σ = (s₀ - 2) + (-σ) by ring, Real.rpow_add hya]
  have e4 : |y₁| ^ (-r - 3 - σ) = |y₁| ^ (-r - 3) * |y₁| ^ (-σ) := by
    rw [show -r - 3 - σ = (-r - 3) + (-σ) by ring, Real.rpow_add hy1a]
  have e5 : y₂ ^ (l + σ) = y₂ ^ l * y₂ ^ σ := Real.rpow_add hy₂ _ _
  have e6 : |y| ^ (s₀ - 1 - σ) = |y| ^ (s₀ - 2) * |y| * |y| ^ (-σ) := by
    rw [show s₀ - 1 - σ = (s₀ - 2) + 1 + (-σ) by ring, Real.rpow_add hya, Real.rpow_add_one hya.ne']
  have e7 : |y₁| ^ (-r - 1 - σ) = |y₁| ^ (-r - 3) * y₁ ^ 2 * |y₁| ^ (-σ) := by
    rw [show -r - 1 - σ = (-r - 3) + 2 + (-σ) by ring, Real.rpow_add hy1a, Real.rpow_add hy1a, Real.rpow_two,
      sq_abs]
  simp only [K]
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, e2]; ring
  · rw [e3, e4, e5]; ring
  · rw [e6, e7, e5]; ring

lemma norm_Fw_le (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ) (ha : a ≠ 0) (e : ℤ) (s : ℂ)
    (C σ : ℝ) (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hWb : ∀ t : ℝ, t ≠ 0 → ‖D.W (ArchR.diagOne t)‖ ≤ C * (1 + |t| ^ (-σ)))
    (y y₁ y₂ : ℝ) (hy : y ≠ 0) (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) :
    ‖Fw D u₃ a₃ a e s (y, y₁, y₂)‖ ≤
      C * (K (Real.pi * a ^ 2) (s.re - 2) (-u₃.re - 3) (P₂.centralExponent.re - u₃.re + 1) (y, y₁, y₂) +
        |a| * K (Real.pi * a ^ 2) (s.re - 1) (-u₃.re - 1) (P₂.centralExponent.re - u₃.re + 1) (y, y₁, y₂) +
        |a| ^ (-σ) * K (Real.pi * a ^ 2) (s.re - 2 - σ) (-u₃.re - 3 - σ)
          (P₂.centralExponent.re - u₃.re + 1 + σ) (y, y₁, y₂) +
        |a| * |a| ^ (-σ) * K (Real.pi * a ^ 2) (s.re - 1 - σ) (-u₃.re - 1 - σ)
          (P₂.centralExponent.re - u₃.re + 1 + σ) (y, y₁, y₂)) := by
  obtain ⟨k1, k2, k3⟩ := K_shift (Real.pi * a ^ 2) s.re u₃.re (P₂.centralExponent.re - u₃.re + 1) σ y y₁ y₂ hy hy₁ hy₂
  rw [norm_Fw D u₃ a₃ a e s y y₁ y₂ hy hy₁ hy₂, k1, k2, k3]
  set X := K (Real.pi * a ^ 2) (s.re - 2) (-u₃.re - 3) (P₂.centralExponent.re - u₃.re + 1) (y, y₁, y₂)
  have hX : 0 ≤ X := K_nonneg _ _ _ _ _ hy₂
  have hya : 0 < |y| := abs_pos.mpr hy
  have hy1a : 0 < |y₁| := abs_pos.mpr hy₁
  have haa : 0 < |a| := abs_pos.mpr ha
  set t : ℝ := a * y * y₁ / y₂ with ht
  have ht0 : t ≠ 0 := div_ne_zero (mul_ne_zero (mul_ne_zero ha hy) hy₁) hy₂.ne'
  have hw := hWb t ht0
  have htσ : |t| ^ (-σ) = |a| ^ (-σ) * (|y| ^ (-σ) * |y₁| ^ (-σ) * y₂ ^ σ) := by
    rw [ht, abs_div, abs_mul, abs_mul, abs_of_pos hy₂, Real.div_rpow (by positivity) hy₂.le,
      Real.mul_rpow (by positivity) hy1a.le, Real.mul_rpow haa.le hya.le, Real.rpow_neg hy₂.le, div_inv_eq_mul]
    ring
  rw [htσ] at hw
  have hc : |1 - a * y * y₁ ^ 2| ≤ 1 + |a| * (|y| * y₁ ^ 2) := by
    calc |1 - a * y * y₁ ^ 2| ≤ |(1:ℝ)| + |a * y * y₁ ^ 2| := abs_sub _ _
      _ = 1 + |a| * (|y| * y₁ ^ 2) := by rw [abs_one, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg y₁)]; ring
  have hm : 0 ≤ |y| ^ (-σ) * |y₁| ^ (-σ) * y₂ ^ σ := by positivity
  have h1 : X * |1 - a * y * y₁ ^ 2| * ‖D.W (ArchR.diagOne (a * y * y₁ / y₂))‖ ≤
      X * (1 + |a| * (|y| * y₁ ^ 2)) * (C * (1 + |a| ^ (-σ) * (|y| ^ (-σ) * |y₁| ^ (-σ) * y₂ ^ σ))) := by
    apply mul_le_mul _ hw (norm_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left hc hX
  refine h1.trans (le_of_eq ?_)
  ring

lemma ae_μ₃ : ∀ᵐ p ∂μ₃, p.1 ≠ 0 ∧ p.2.1 ≠ 0 ∧ 0 < p.2.2 := by
  unfold μ₃
  have h1 : ∀ᵐ p ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0)))),
      p.1 ≠ 0 := Measure.quasiMeasurePreserving_fst.ae ae_ne_zero
  have h2' : ∀ᵐ q ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))), q.1 ≠ 0 ∧ 0 < q.2 := by
    have a1 : ∀ᵐ q ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))), q.1 ≠ 0 :=
      Measure.quasiMeasurePreserving_fst.ae ae_ne_zero
    have a2 : ∀ᵐ q ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))), 0 < q.2 :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)
    exact a1.and a2
  have h2 := Measure.quasiMeasurePreserving_snd.ae h2'
    (μa := (volume : Measure ℝ).prod ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))))
  filter_upwards [h1, h2] with p hp hq
  exact ⟨hp, hq⟩

theorem integrable_Fw (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ) (ha : a ≠ 0) (e : ℤ) (s : ℂ)
    (C σ : ℝ) (hC : 0 ≤ C) (hσ : 0 ≤ σ)
    (hWb : ∀ t : ℝ, t ≠ 0 → ‖D.W (ArchR.diagOne t)‖ ≤ C * (1 + |t| ^ (-σ)))
    (hs : max (1 + σ) (1 - u₃.re) < s.re) :
    Integrable (Fw D u₃ a₃ a e s) μ₃ := by
  have hs1 : 1 + σ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs2 : 1 - u₃.re < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  have hb : 0 < Real.pi * a ^ 2 := by positivity
  set l : ℝ := P₂.centralExponent.re - u₃.re + 1
  have i1 := integrable_K (Real.pi * a ^ 2) (s.re - 2) (-u₃.re - 3) l hb (by linarith) (by linarith)
  have i2 := integrable_K (Real.pi * a ^ 2) (s.re - 1) (-u₃.re - 1) l hb (by linarith) (by linarith)
  have i3 := integrable_K (Real.pi * a ^ 2) (s.re - 2 - σ) (-u₃.re - 3 - σ) (l + σ) hb (by linarith) (by linarith)
  have i4 := integrable_K (Real.pi * a ^ 2) (s.re - 1 - σ) (-u₃.re - 1 - σ) (l + σ) hb (by linarith) (by linarith)
  have hmaj := (((i1.add (i2.const_mul |a|)).add (i3.const_mul (|a| ^ (-σ)))).add
    (i4.const_mul (|a| * |a| ^ (-σ)))).const_mul C
  refine Integrable.mono' hmaj (measurable_Fw D u₃ a₃ a e s).aestronglyMeasurable ?_
  filter_upwards [ae_μ₃] with p hp
  obtain ⟨y, y₁, y₂⟩ := p
  have h := norm_Fw_le D u₃ a₃ a ha e s C σ hC hσ hWb y y₁ y₂ hp.1 hp.2.1 hp.2.2
  simpa only [Pi.add_apply, Pi.mul_apply] using h

noncomputable def ρ₃ : Measure (ℝ × ℝ × ℝ) :=
  ((volume : Measure ℝ).restrict (Ioi 0)).prod
    (((volume : Measure ℝ).restrict (Ioi 0)).prod ((volume : Measure ℝ).restrict (Ioi 0)))

scoped instance : SFinite ρ₃ := by unfold ρ₃; infer_instance

lemma ae_ρ₃ : ∀ᵐ p ∂ρ₃, 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2 := by
  unfold ρ₃
  rw [Measure.prod_restrict, Measure.prod_restrict, ← Measure.volume_eq_prod, ← Measure.volume_eq_prod]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod (measurableSet_Ioi.prod measurableSet_Ioi))] with p hp
  exact ⟨hp.1, hp.2.1, hp.2.2⟩

lemma ae_ν₂ : ∀ᵐ z ∂(((volume : Measure ℝ).restrict (Ioi 0)).prod ((volume : Measure ℝ).restrict (Ioi 0))),
    0 < (z : ℝ × ℝ).1 :=
  Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)

theorem integral_Fw_eq (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ) (e : ℤ) (s : ℂ)
    (he : ((e : ZMod 2)) = a₃ + 1) (hint : Integrable (Fw D u₃ a₃ a e s) μ₃) :
    Integrable (fun p : ℝ × ℝ × ℝ => Q D u₃ a₃ a s p.1 p.2.1 p.2.2) ρ₃ ∧
    ∫ p, Fw D u₃ a₃ a e s p ∂μ₃ = 2 * ∫ p, Q D u₃ a₃ a s p.1 p.2.1 p.2.2 ∂ρ₃ := by

  obtain ⟨hA, hB, hAB⟩ := Z0MinorA.fold_mid (volume : Measure ℝ) ((volume : Measure ℝ).restrict (Ioi 0))
    (Fw D u₃ a₃ a e s) hint
  set f₁ : ℝ × ℝ × ℝ → ℂ := fun p => Fw D u₃ a₃ a e s p + Fw D u₃ a₃ a e s (p.1, -p.2.1, p.2.2)
  have hf₁ : Integrable f₁ ((volume : Measure ℝ).prod (((volume : Measure ℝ).restrict (Ioi 0)).prod
      ((volume : Measure ℝ).restrict (Ioi 0)))) := hA.add hB

  obtain ⟨hC, hD, hCD⟩ := Z0MinorA.fold_fst (((volume : Measure ℝ).restrict (Ioi 0)).prod
    ((volume : Measure ℝ).restrict (Ioi 0))) f₁ hf₁
  have hsum : Integrable (fun p : ℝ × ℝ × ℝ => f₁ p + f₁ (-p.1, p.2)) ρ₃ := hC.add hD
  have hpt : ∀ᵐ p ∂ρ₃, f₁ p + f₁ (-p.1, p.2) = 2 * Q D u₃ a₃ a s p.1 p.2.1 p.2.2 := by
    filter_upwards [ae_ρ₃] with p hp
    obtain ⟨y, y₁, y₂⟩ := p
    exact fold_pointwise D u₃ a₃ a e s he y y₁ y₂ hp.1 hp.2.1 hp.2.2
  have hQ2 : Integrable (fun p : ℝ × ℝ × ℝ => 2 * Q D u₃ a₃ a s p.1 p.2.1 p.2.2) ρ₃ := hsum.congr hpt
  have hQ : Integrable (fun p : ℝ × ℝ × ℝ => Q D u₃ a₃ a s p.1 p.2.1 p.2.2) ρ₃ := by
    have := hQ2.const_mul (1 / 2 : ℂ)
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only; ring
  refine ⟨hQ, ?_⟩
  unfold μ₃
  rw [hAB]
  change ∫ p, f₁ p ∂((volume : Measure ℝ).prod (((volume : Measure ℝ).restrict (Ioi 0)).prod
      ((volume : Measure ℝ).restrict (Ioi 0)))) = _
  rw [hCD]
  change ∫ p, (f₁ p + f₁ (-p.1, p.2)) ∂ρ₃ = _
  rw [integral_congr_ae hpt, integral_const_mul]

theorem integral_Q_eq (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (a : ℝ) (s : ℂ)
    (hQ : Integrable (fun p : ℝ × ℝ × ℝ => Q D u₃ a₃ a s p.1 p.2.1 p.2.2) ρ₃) :
    Integrable (fun p : ℝ × ℝ × ℝ => φ₁ u₃ s p.2.1 * R₂ D u₃ a₃ a s p.1 p.2.2) ρ₃ ∧
    ∫ p, Q D u₃ a₃ a s p.1 p.2.1 p.2.2 ∂ρ₃ = ∫ p, φ₁ u₃ s p.2.1 * R₂ D u₃ a₃ a s p.1 p.2.2 ∂ρ₃ := by
  have hc : ∀ᵐ z ∂(((volume : Measure ℝ).restrict (Ioi 0)).prod ((volume : Measure ℝ).restrict (Ioi 0))),
      0 < (fun z : ℝ × ℝ => z.1⁻¹) z := by
    filter_upwards [ae_ν₂] with z hz
    exact inv_pos.mpr hz
  obtain ⟨hI, hE⟩ := Z0MinorA.subst_fst (((volume : Measure ℝ).restrict (Ioi 0)).prod
      ((volume : Measure ℝ).restrict (Ioi 0)))
    (fun p : ℝ × ℝ × ℝ => Q D u₃ a₃ a s p.1 p.2.1 p.2.2) (measurable_Q3 D u₃ a₃ a s) hQ
    (fun z : ℝ × ℝ => z.1⁻¹) (by fun_prop) hc
  have hpt : ∀ᵐ p ∂ρ₃, ((p.2.1⁻¹ : ℝ) : ℂ) * Q D u₃ a₃ a s (p.2.1⁻¹ * p.1) p.2.1 p.2.2 =
      φ₁ u₃ s p.2.1 * R₂ D u₃ a₃ a s p.1 p.2.2 := by
    filter_upwards [ae_ρ₃] with p hp
    exact subst_pointwise D u₃ a₃ a s p.1 p.2.1 p.2.2 hp.1 hp.2.1 hp.2.2
  refine ⟨hI.congr hpt, ?_⟩
  have hE' : ∫ p, Q D u₃ a₃ a s p.1 p.2.1 p.2.2 ∂ρ₃ =
      ∫ p : ℝ × ℝ × ℝ, ((p.2.1⁻¹ : ℝ) : ℂ) * Q D u₃ a₃ a s (p.2.1⁻¹ * p.1) p.2.1 p.2.2 ∂ρ₃ := hE
  rw [hE']
  exact integral_congr_ae hpt

end Z0MinorC
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_minorSection_gaussian3_of_weightZero.Z0MinorB P2MW.S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_minorSection_gaussian3_of_weightZero.Z0MinorC"

open NumberField AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell LanglandsTunnell.CubicInduction Z0MinorB Z0MinorC in

theorem solution
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (u₃ : ℂ) (a₃ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 0 1 : ℝ) : ℂ)) * ((M 1 2 : ℝ) : ℂ) -
        (((M 1 0 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ)) * ((M 0 2 : ℝ) : ℂ)) * gaussian3 M)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (κ : ℝ)
    (hκ : MeasureTheory.Measure.map
        (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
      ENNReal.ofReal κ • (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
        fun y => ENNReal.ofReal |y|⁻¹)
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (e : ℤ)
    (hσ : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v 0 e)
    (he : ((e : ZMod 2)) = a₃ + 1)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (D.W (ArchR.diagOne ((a : ℝ) * (σ' / w))) - (-1 : ℂ) ^ a₃.val * D.W (ArchR.diagOne (-((a : ℝ) * (σ' / w))))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ (-u₃) *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ)) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      MellinConvergent H (s - 1) ∧
        archZeta30 ν_mul (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) (σ.comp E) s 1 =
          (κ : ℂ) * (2 * (Real.pi : ℂ) * (-Complex.I * (a : ℂ))) * Complex.Gammaℝ (s + u₃ + 1) * mellin H (s - 1) := by
  have ha' : (a : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr ha
  obtain ⟨CW, σW, hCW, hσW, hWb⟩ := exists_bound_W D
  refine ⟨max (1 + σW) (1 - u₃.re), fun s hs => ?_⟩
  have hs2 : 1 - u₃.re < s.re := lt_of_le_of_lt (le_max_right _ _) hs

  have hint : Integrable (Fw D u₃ a₃ (a : ℝ) e s) μ₃ :=
    integrable_Fw D u₃ a₃ (a : ℝ) ha' e s CW σW hCW hσW hWb hs

  obtain ⟨hQ, hFQ⟩ := integral_Fw_eq D u₃ a₃ (a : ℝ) e s he hint
  obtain ⟨hQ₂, hQQ₂⟩ := integral_Q_eq D u₃ a₃ (a : ℝ) s hQ

  obtain ⟨hφi, hφ⟩ := Z0MinorEngine.integrableOn_and_integral_cpow_neg_mul_exp_neg_pi_div_sq (s + u₃ + 1)
    (by simp only [Complex.add_re, Complex.one_re]; linarith)
  have hφ' : ∫ y₁ in Ioi (0:ℝ), φ₁ u₃ s y₁ = Complex.Gammaℝ (s + u₃ + 1) / 2 := hφ
  have hΓ : Complex.Gammaℝ (s + u₃ + 1) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp only [Complex.add_re, Complex.one_re]; linarith)

  have hR : ∀ σ' : ℝ, ∫ w in Ioi (0:ℝ), R₂ D u₃ a₃ (a : ℝ) s σ' w = ((σ' : ℂ) ^ ((s - 1) - 1)) • H σ' := by
    intro σ'
    simp only [R₂, Hint]
    rw [integral_const_mul, hH, smul_eq_mul]
    ring
  have hslice : ∀ σ' : ℝ, ∫ z, φ₁ u₃ s z.1 * R₂ D u₃ a₃ (a : ℝ) s σ' z.2
      ∂(((volume : Measure ℝ).restrict (Ioi 0)).prod ((volume : Measure ℝ).restrict (Ioi 0))) =
      (Complex.Gammaℝ (s + u₃ + 1) / 2) * (((σ' : ℂ) ^ ((s - 1) - 1)) • H σ') := by
    intro σ'
    rw [integral_prod_mul (fun y₁ : ℝ => φ₁ u₃ s y₁) (fun w : ℝ => R₂ D u₃ a₃ (a : ℝ) s σ' w), hφ', hR]
  have hQ₂val : ∫ p, φ₁ u₃ s p.2.1 * R₂ D u₃ a₃ (a : ℝ) s p.1 p.2.2 ∂ρ₃ =
      (Complex.Gammaℝ (s + u₃ + 1) / 2) * mellin H (s - 1) := by
    unfold ρ₃
    rw [integral_prod _ hQ₂]
    simp only []
    simp_rw [hslice]
    rw [integral_const_mul]
    rfl

  have hMC : MellinConvergent H (s - 1) := by
    have h1 := hQ₂.integral_prod_left
    have h2 : (fun σ' : ℝ => ∫ z, φ₁ u₃ s z.1 * R₂ D u₃ a₃ (a : ℝ) s σ' z.2
        ∂(((volume : Measure ℝ).restrict (Ioi 0)).prod ((volume : Measure ℝ).restrict (Ioi 0)))) =
        fun σ' : ℝ => (Complex.Gammaℝ (s + u₃ + 1) / 2) * (((σ' : ℂ) ^ ((s - 1) - 1)) • H σ') := funext hslice
    unfold ρ₃ at h1
    rw [h2] at h1
    have h3 := h1.const_mul ((Complex.Gammaℝ (s + u₃ + 1) / 2)⁻¹)
    refine h3.congr (Filter.Eventually.of_forall fun σ' => ?_)
    simp only
    rw [← mul_assoc, inv_mul_cancel₀ (div_ne_zero hΓ two_ne_zero), one_mul]
  refine ⟨hMC, ?_⟩

  set Φ : ℝ → ℂ := fun y => jacquetVector3 D u₃ a₃ ((a : ℝ) * y) psiInf S 1 with hΦdef
  set C₀ : ℂ := 2 * (Real.pi : ℂ) * (-Complex.I * (a : ℂ)) with hC₀
  have hW : ∀ z : (InfiniteAdeleRing ℚ)ˣ,
      jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S (iotaGL (diagUnitGL2 z) * 1) =
        Φ (StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) := fun z =>
    LanglandsTunnell.CubicInduction.jacquetVector3_iotaGL_diagUnitGL2_mul D u₃ a₃ (a : ℝ) psiInf S z 1

  have hΦeq : ∀ y : ℝ, y ≠ 0 → Φ y = C₀ * ∫ y₁ : ℝ, ∫ y₂ in Ioi (0:ℝ), Fk D u₃ a₃ (a : ℝ) y y₁ y₂ := by
    intro y hy
    have h := LanglandsTunnell.CubicInduction.jacquetVector3_one_eq_integral_of_minorSection_gaussian3_of_weightZero
      a ha psiInf hpsiInf D hDW0 u₃ a₃ S hS y hy
    simp only [hΦdef, hC₀, Fk]
    exact h

  have hΦm : AEStronglyMeasurable Φ volume := by
    have hg : Measurable (fun q : (ℝ × ℝ) × ℝ => (q.1.1, (q.1.2, q.2))) := by fun_prop
    have hm3 := (measurable_Fk3 D u₃ a₃ (a : ℝ)).comp hg
    have h1 : StronglyMeasurable (fun q : ℝ × ℝ => ∫ y₂, Fk D u₃ a₃ (a : ℝ) q.1 q.2 y₂
        ∂((volume : Measure ℝ).restrict (Ioi 0))) :=
      hm3.stronglyMeasurable.integral_prod_right'
    have h2 : StronglyMeasurable (fun y : ℝ => ∫ y₁, (fun q : ℝ × ℝ => ∫ y₂, Fk D u₃ a₃ (a : ℝ) q.1 q.2 y₂
        ∂((volume : Measure ℝ).restrict (Ioi 0))) (y, y₁) ∂(volume : Measure ℝ)) :=
      h1.integral_prod_right'
    have h3 : AEStronglyMeasurable (fun y : ℝ => C₀ * ∫ y₁ : ℝ, ∫ y₂ in Ioi (0:ℝ), Fk D u₃ a₃ (a : ℝ) y y₁ y₂)
        volume := (h2.const_mul C₀).aestronglyMeasurable
    refine h3.congr ?_
    filter_upwards [ae_ne_zero] with y hy
    exact (hΦeq y hy).symm
  obtain ⟨hκpos, hZ⟩ :=
    LanglandsTunnell.CubicInduction.archZeta30_one_eq_mul_integral_quasiChar_of_isArchCompAt ν_mul κ hκ σ 0 e hσ
      E hE (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) Φ hW hΦm s
  rw [hZ]

  have hfib := hint.prod_right_ae
  have hL : ∫ y : ℝ, Φ y * ArchR.quasiChar 0 (e : ZMod 2) y * ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹ =
      C₀ * ∫ p, Fw D u₃ a₃ (a : ℝ) e s p ∂μ₃ := by
    have h1 : ∀ᵐ y : ℝ, Φ y * ArchR.quasiChar 0 (e : ZMod 2) y * ((|y| : ℝ) : ℂ) ^ (s - 1) * ((|y| : ℝ) : ℂ)⁻¹ =
        C₀ * ∫ z, Fw D u₃ a₃ (a : ℝ) e s (y, z) ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Ioi 0))) := by
      unfold μ₃ at hfib
      filter_upwards [ae_ne_zero, hfib] with y hy hfy
      rw [integral_prod _ hfy]
      simp only [Fw]
      simp_rw [integral_mul_const]
      rw [hΦeq y hy, wt]
      ring
    rw [integral_congr_ae h1, integral_const_mul]
    unfold μ₃
    rw [integral_prod _ hint]
  rw [hL, hFQ, hQQ₂, hQ₂val]
  ring

end S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_minorSection_gaussian3_of_weightZero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_minorSection_gaussian3_of_weightZero (solution)
