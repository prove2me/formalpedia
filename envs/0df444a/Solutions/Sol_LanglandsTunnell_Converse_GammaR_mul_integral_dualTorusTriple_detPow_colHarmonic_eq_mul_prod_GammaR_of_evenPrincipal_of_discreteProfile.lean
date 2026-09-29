-- Prove2me | solution 1 for LanglandsTunnell.Converse.GammaR_mul_integral_dualTorusTriple_detPow_colHarmonic_eq_mul_prod_GammaR_of_evenPrincipal_of_discreteProfile
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/3c144c42-970c-52af-a9b0-734f6d93f49e

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Theorems.Thm_LanglandsTunnell_integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance
import Theorems.Thm_LanglandsTunnell_Converse_exists_forall_integrable_dualQuadruple_and_torusTriple_detPow_colHarmonic_of_evenSheet
import Theorems.Thm_LanglandsTunnell_mulConvGaussian_add_one_eq_two_mul_cpow_mul_exp_neg_two_pi_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_detPow_colHarmonic_eq_mul_prod_GammaR_of_evenPrincipal_of_discreteProfile

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

namespace KcDualEvalZeroDisc

open Complex

theorem quasiChar_zero_zero (y : ℝ) : ArchR.quasiChar 0 0 y = 1 := by
  simp [ArchR.quasiChar]

theorem quasiChar_zero_one_zero : ArchR.quasiChar 0 1 0 = 0 := by
  simp [ArchR.quasiChar]

@[scoped simp] theorem val_one_zmod2 : (1 : ZMod 2).val = 1 := rfl
@[scoped simp] theorem val_zero_zmod2 : (0 : ZMod 2).val = 0 := rfl

theorem quasiChar_zero_of_pos (a : ZMod 2) {y : ℝ} (hy : 0 < y) : ArchR.quasiChar 0 a y = 1 := by
  unfold ArchR.quasiChar
  rw [cpow_zero, one_mul, sign_pos hy]
  split_ifs <;> simp

theorem quasiChar_zero_of_neg (a : ZMod 2) {y : ℝ} (hy : y < 0) :
    ArchR.quasiChar 0 a y = (-1 : ℂ) ^ a.val := by
  unfold ArchR.quasiChar
  rw [cpow_zero, one_mul, sign_neg hy]
  have : a = 0 ∨ a = 1 := by revert a; decide
  rcases this with rfl | rfl <;> simp

theorem quasiChar_zero_one_mul_self {y : ℝ} (hy : y ≠ 0) : ArchR.quasiChar 0 1 y * ArchR.quasiChar 0 1 y = 1 := by
  rcases lt_or_gt_of_ne hy with h | h
  · rw [quasiChar_zero_of_neg 1 h, val_one_zmod2]; norm_num
  · rw [quasiChar_zero_of_pos 1 h, one_mul]

theorem neg_one_pow_val_cases (a₀ : ZMod 2) : ((-1 : ℂ) ^ a₀.val) = 1 ∨ ((-1 : ℂ) ^ a₀.val) = -1 := by
  have : a₀ = 0 ∨ a₀ = 1 := by revert a₀; decide
  rcases this with rfl | rfl <;> simp

theorem neg_one_pow_val_add_one (a₀ : ZMod 2) : ((-1 : ℂ) ^ (a₀ + 1).val) = -((-1 : ℂ) ^ a₀.val) := by
  have : a₀ = 0 ∨ a₀ = 1 := by revert a₀; decide
  rcases this with rfl | rfl
  · simp
  · simp; rfl

theorem sc_pp (a₀ e : ZMod 2) {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q) :
    ArchR.quasiChar 0 0 (-T) * ArchR.quasiChar 0 a₀ (-T) * ArchR.quasiChar 0 1 T *
        ArchR.quasiChar 0 e Q * ArchR.quasiChar 0 a₀ Q = (-1 : ℂ) ^ a₀.val := by
  rw [quasiChar_zero_zero, quasiChar_zero_of_neg a₀ (neg_neg_of_pos hT), quasiChar_zero_of_pos 1 hT,
    quasiChar_zero_of_pos e hQ, quasiChar_zero_of_pos a₀ hQ]
  ring

theorem sc_pn (a₀ e : ZMod 2) {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q) :
    ArchR.quasiChar 0 0 (-T) * ArchR.quasiChar 0 a₀ (-T) * ArchR.quasiChar 0 1 T *
        ArchR.quasiChar 0 e (-Q) * ArchR.quasiChar 0 a₀ (-Q) = (-1 : ℂ) ^ e.val := by
  rw [quasiChar_zero_zero, quasiChar_zero_of_neg a₀ (neg_neg_of_pos hT), quasiChar_zero_of_pos 1 hT,
    quasiChar_zero_of_neg e (neg_neg_of_pos hQ), quasiChar_zero_of_neg a₀ (neg_neg_of_pos hQ)]
  rcases neg_one_pow_val_cases a₀ with h | h <;> rw [h] <;> ring

theorem sc_np (a₀ e : ZMod 2) {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q) :
    ArchR.quasiChar 0 0 T * ArchR.quasiChar 0 a₀ T * ArchR.quasiChar 0 1 (-T) *
        ArchR.quasiChar 0 e Q * ArchR.quasiChar 0 a₀ Q = -1 := by
  rw [quasiChar_zero_zero, quasiChar_zero_of_pos a₀ hT, quasiChar_zero_of_neg 1 (neg_neg_of_pos hT),
    quasiChar_zero_of_pos e hQ, quasiChar_zero_of_pos a₀ hQ]
  simp

theorem sc_nn (a₀ e : ZMod 2) {T Q : ℝ} (hT : 0 < T) (hQ : 0 < Q) :
    ArchR.quasiChar 0 0 T * ArchR.quasiChar 0 a₀ T * ArchR.quasiChar 0 1 (-T) *
        ArchR.quasiChar 0 e (-Q) * ArchR.quasiChar 0 a₀ (-Q) = -((-1 : ℂ) ^ e.val * (-1 : ℂ) ^ a₀.val) := by
  rw [quasiChar_zero_zero, quasiChar_zero_of_pos a₀ hT, quasiChar_zero_of_neg 1 (neg_neg_of_pos hT),
    quasiChar_zero_of_neg e (neg_neg_of_pos hQ), quasiChar_zero_of_neg a₀ (neg_neg_of_pos hQ)]
  simp

theorem neg_preimage_Iic_zero : (Neg.neg : ℝ → ℝ) ⁻¹' Set.Iic 0 = Set.Ici 0 := by
  ext x; simp

theorem restrict_prod_le {Y : Type*} [MeasurableSpace Y] (μ : Measure ℝ) [SFinite μ] (ν : Measure Y) [SFinite ν]
    (s : Set ℝ) : (μ.restrict s).prod ν ≤ μ.prod ν := by
  rw [Measure.restrict_prod_eq_prod_univ]; exact Measure.restrict_le_self

theorem prod_restrict_prod_le {Z : Type*} [MeasurableSpace Z] (μ : Measure ℝ) [SFinite μ] (ρ : Measure Z) [SFinite ρ]
    (s : Set ℝ) : μ.prod (((volume : Measure ℝ).restrict s).prod ρ) ≤ μ.prod ((volume : Measure ℝ).prod ρ) := by
  have h1 : ((volume : Measure ℝ).restrict s).prod ρ = ((volume : Measure ℝ).prod ρ).restrict (s ×ˢ Set.univ) :=
    Measure.restrict_prod_eq_prod_univ _
  have h2 : μ.prod (((volume : Measure ℝ).prod ρ).restrict (s ×ˢ Set.univ)) =
      (μ.restrict Set.univ).prod (((volume : Measure ℝ).prod ρ).restrict (s ×ˢ Set.univ)) := by
    rw [Measure.restrict_univ]
  rw [h1, h2, Measure.prod_restrict]
  exact Measure.restrict_le_self

theorem integral_prod_eq_Ioi_add_reflect {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    (F : ℝ × Y → ℂ) (hF : Integrable F ((volume : Measure ℝ).prod ν)) :
    (∫ z, F z ∂((volume : Measure ℝ).prod ν)) =
      (∫ z, F z ∂(((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ν)) +
        ∫ z, F (-z.1, z.2) ∂(((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ν) := by
  have hsplit : (volume : Measure ℝ) =
      (volume : Measure ℝ).restrict (Set.Ioi 0) + (volume : Measure ℝ).restrict (Set.Iic 0) := by
    rw [← Set.compl_Ioi, Measure.restrict_add_restrict_compl measurableSet_Ioi]
  have hle1 : ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ν ≤ (volume : Measure ℝ).prod ν :=
    restrict_prod_le _ _ _
  have hle2 : ((volume : Measure ℝ).restrict (Set.Iic 0)).prod ν ≤ (volume : Measure ℝ).prod ν :=
    restrict_prod_le _ _ _
  conv_lhs => rw [hsplit]
  rw [Measure.add_prod, integral_add_measure (hF.mono_measure hle1) (hF.mono_measure hle2)]
  congr 1
  have hneg : MeasurePreserving (Neg.neg : ℝ → ℝ) ((volume : Measure ℝ).restrict (Set.Ici 0))
      ((volume : Measure ℝ).restrict (Set.Iic 0)) := by
    have := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
      (measurableSet_Iic (a := (0 : ℝ)))
    rwa [neg_preimage_Iic_zero] at this
  have hprod : MeasurePreserving (Prod.map (Neg.neg : ℝ → ℝ) (id : Y → Y))
      (((volume : Measure ℝ).restrict (Set.Ici 0)).prod ν) (((volume : Measure ℝ).restrict (Set.Iic 0)).prod ν) :=
    hneg.prod (MeasurePreserving.id ν)
  have hemb : MeasurableEmbedding (Prod.map (Neg.neg : ℝ → ℝ) (id : Y → Y)) :=
    ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl Y)).measurableEmbedding
  have := hprod.integral_comp hemb F
  rw [← this, Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)) (μ := volume))]
  rfl

theorem integral_prod_eq_Ioi_add_reflect_mid {Z : Type*} [MeasurableSpace Z] (μ : Measure ℝ) [SFinite μ]
    (ρ : Measure Z) [SFinite ρ]
    (F : ℝ × ℝ × Z → ℂ) (hF : Integrable F (μ.prod ((volume : Measure ℝ).prod ρ))) :
    (∫ z, F z ∂(μ.prod ((volume : Measure ℝ).prod ρ))) =
      (∫ z, F z ∂(μ.prod (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ρ))) +
        ∫ z, F (z.1, -z.2.1, z.2.2) ∂(μ.prod (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ρ)) := by
  have hsplit : (volume : Measure ℝ) =
      (volume : Measure ℝ).restrict (Set.Ioi 0) + (volume : Measure ℝ).restrict (Set.Iic 0) := by
    rw [← Set.compl_Ioi, Measure.restrict_add_restrict_compl measurableSet_Ioi]
  have hle1 : μ.prod (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ρ) ≤ μ.prod ((volume : Measure ℝ).prod ρ) :=
    prod_restrict_prod_le _ _ _
  have hle2 : μ.prod (((volume : Measure ℝ).restrict (Set.Iic 0)).prod ρ) ≤ μ.prod ((volume : Measure ℝ).prod ρ) :=
    prod_restrict_prod_le _ _ _
  conv_lhs => rw [hsplit]
  rw [Measure.add_prod, Measure.prod_add, integral_add_measure (hF.mono_measure hle1) (hF.mono_measure hle2)]
  congr 1
  have hneg : MeasurePreserving (Neg.neg : ℝ → ℝ) ((volume : Measure ℝ).restrict (Set.Ici 0))
      ((volume : Measure ℝ).restrict (Set.Iic 0)) := by
    have := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
      (measurableSet_Iic (a := (0 : ℝ)))
    rwa [neg_preimage_Iic_zero] at this
  have hprod : MeasurePreserving (Prod.map (id : ℝ → ℝ) (Prod.map (Neg.neg : ℝ → ℝ) (id : Z → Z)))
      (μ.prod (((volume : Measure ℝ).restrict (Set.Ici 0)).prod ρ))
      (μ.prod (((volume : Measure ℝ).restrict (Set.Iic 0)).prod ρ)) :=
    (MeasurePreserving.id μ).prod (hneg.prod (MeasurePreserving.id ρ))
  have hemb : MeasurableEmbedding (Prod.map (id : ℝ → ℝ) (Prod.map (Neg.neg : ℝ → ℝ) (id : Z → Z))) :=
    ((MeasurableEquiv.refl ℝ).prodCongr ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl Z))).measurableEmbedding
  have := hprod.integral_comp hemb F
  rw [← this, Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)) (μ := volume))]
  rfl

theorem integral_prod3_eq_sum_four {Z : Type*} [MeasurableSpace Z] (ρ : Measure Z) [SFinite ρ]
    (F : ℝ × ℝ × Z → ℂ) (hF : Integrable F ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ρ))) :
    (∫ z, F z ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ρ))) =
      (∫ z, F z ∂(((volume : Measure ℝ).restrict (Set.Ioi 0)).prod (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ρ))) +
      (∫ z, F (z.1, -z.2.1, z.2.2) ∂(((volume : Measure ℝ).restrict (Set.Ioi 0)).prod (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ρ))) +
      ((∫ z, F (-z.1, z.2) ∂(((volume : Measure ℝ).restrict (Set.Ioi 0)).prod (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ρ))) +
       (∫ z, F (-z.1, -z.2.1, z.2.2) ∂(((volume : Measure ℝ).restrict (Set.Ioi 0)).prod (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ρ)))) := by
  have hle : ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).prod ρ) ≤
      (volume : Measure ℝ).prod ((volume : Measure ℝ).prod ρ) :=
    restrict_prod_le _ _ _
  rw [integral_prod_eq_Ioi_add_reflect _ F hF]
  have hF1 : Integrable F (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod ((volume : Measure ℝ).prod ρ)) :=
    hF.mono_measure hle
  have hneg : MeasurePreserving (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ × Z → ℝ × Z))
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ρ)) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ρ)) :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id _)
  have hemb : MeasurableEmbedding (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ × Z → ℝ × Z)) :=
    ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl (ℝ × Z))).measurableEmbedding
  have hF2 : Integrable (fun z : ℝ × ℝ × Z => F (-z.1, z.2)) ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod ρ)) := by
    have := (hneg.integrable_comp_emb hemb).2 hF
    exact this
  rw [integral_prod_eq_Ioi_add_reflect_mid _ _ F hF1,
    integral_prod_eq_Ioi_add_reflect_mid _ _ (fun z : ℝ × ℝ × Z => F (-z.1, z.2)) (hF2.mono_measure hle)]

noncomputable def MCG4 (p₁ p₂ : ℂ) (x : ℝ) : ℂ :=
  (4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
    ((r : ℂ) ^ p₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
      (((x / r : ℝ) : ℂ) ^ p₂ * (Real.exp (-(Real.pi * (x / r) ^ 2)) : ℂ)) / (r : ℂ)

noncomputable def rowInt (p₁ p₂ q₁ q₂ α β γ : ℂ) (t y₁ y₂ : ℝ) : ℂ :=
  ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
      ((r : ℂ) ^ p₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
        (((t / r : ℝ) : ℂ) ^ p₂ * (Real.exp (-(Real.pi * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) *
    ((t : ℝ) : ℂ) ^ α *
    ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
      ((r : ℂ) ^ q₁ * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
        ((((t * y₁ / y₂) / r : ℝ) : ℂ) ^ q₂ * (Real.exp (-(Real.pi * ((t * y₁ / y₂) / r) ^ 2)) : ℂ)) / (r : ℂ)) *
    ((y₁ : ℝ) : ℂ) ^ β * ((y₂ : ℝ) : ℂ) ^ γ *
    (Real.exp (-(Real.pi / y₁ ^ 2)) : ℂ) * (Real.exp (-(Real.pi * t ^ 2 * y₁ ^ 2)) : ℂ) *
    (Real.exp (-(Real.pi / y₂ ^ 2)) : ℂ)

theorem row_balanced (p₁ p₂ q₁ q₂ α β γ : ℂ)
    (hbal : β - γ = 2 * α + 2 + p₁ + p₂)
    (hp₁ : 0 < (α - β + p₁).re) (hp₂ : 0 < (α - β + p₂).re)
    (h₁₁ : 0 < (α + 1 + p₁ + q₁).re) (h₁₂ : 0 < (α + 1 + p₁ + q₂).re)
    (h₂₁ : 0 < (α + 1 + p₂ + q₁).re) (h₂₂ : 0 < (α + 1 + p₂ + q₂).re) :
    (∫ t in Set.Ioi (0 : ℝ), ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ), rowInt p₁ p₂ q₁ q₂ α β γ t y₁ y₂)
      = (1 / 2 : ℂ) *
          (Complex.Gammaℝ (α - β + p₁) * Complex.Gammaℝ (α - β + p₂) *
            (Complex.Gammaℝ (α + 1 + p₁ + q₁) * Complex.Gammaℝ (α + 1 + p₁ + q₂) *
              Complex.Gammaℝ (α + 1 + p₂ + q₁) * Complex.Gammaℝ (α + 1 + p₂ + q₂))) /
          Complex.Gammaℝ (β - γ + q₁ + q₂) :=
  LanglandsTunnell.integral_mulConvGaussian_torusGauss_eq_GammaR_prod_div_of_balance p₁ p₂ q₁ q₂ α β γ
    hbal hp₁ hp₂ h₁₁ h₁₂ h₂₁ h₂₂

noncomputable abbrev μI : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ioi 0)

noncomputable abbrev V3 : Measure (ℝ × ℝ × ℝ) := (volume : Measure ℝ).prod ((volume : Measure ℝ).prod μI)

noncomputable abbrev M3 : Measure (ℝ × ℝ × ℝ) := μI.prod (μI.prod μI)

theorem M3_le_V3 : M3 ≤ V3 :=
  le_trans (restrict_prod_le (volume : Measure ℝ) (μI.prod μI) (Set.Ioi 0))
    (prod_restrict_prod_le (volume : Measure ℝ) μI (Set.Ioi 0))

theorem integral_prod3_perm_eq_iterated (f : ℝ → ℝ → ℝ → ℂ)
    (hf : Integrable (fun z : ℝ × ℝ × ℝ => f z.1 z.2.2 z.2.1) M3) :
    (∫ z, f z.1 z.2.2 z.2.1 ∂M3) =
      ∫ t in Set.Ioi (0 : ℝ), ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ), f t y₁ y₂ := by
  rw [integral_prod _ hf]
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae] with T hT
  have hsw : (∫ y, f T y.2 y.1 ∂(μI.prod μI)) = ∫ y, f T y.1 y.2 ∂(μI.prod μI) :=
    integral_prod_swap (μ := μI) (ν := μI) (fun y : ℝ × ℝ => f T y.1 y.2)
  rw [hsw]
  exact integral_prod (fun y : ℝ × ℝ => f T y.1 y.2) hT.swap

theorem integrable_reflects (F : ℝ × ℝ × ℝ → ℂ) (hF : Integrable F V3) :
    Integrable (fun z : ℝ × ℝ × ℝ => F (z.1, -z.2.1, z.2.2)) V3 ∧
      Integrable (fun z : ℝ × ℝ × ℝ => F (-z.1, z.2)) V3 ∧
      Integrable (fun z : ℝ × ℝ × ℝ => F (-z.1, -z.2.1, z.2.2)) V3 := by
  have h1 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ))) V3 V3 :=
    (MeasurePreserving.id _).prod ((Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id _))
  have e1 : MeasurableEmbedding (Prod.map (id : ℝ → ℝ) (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ))) :=
    ((MeasurableEquiv.refl ℝ).prodCongr ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ))).measurableEmbedding
  have h2 : MeasurePreserving (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ × ℝ → ℝ × ℝ)) V3 V3 :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id _)
  have e2 : MeasurableEmbedding (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ × ℝ → ℝ × ℝ)) :=
    ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl (ℝ × ℝ))).measurableEmbedding
  have h3 : MeasurePreserving (Prod.map (Neg.neg : ℝ → ℝ) (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ))) V3 V3 :=
    (Measure.measurePreserving_neg (volume : Measure ℝ)).prod
      ((Measure.measurePreserving_neg (volume : Measure ℝ)).prod (MeasurePreserving.id _))
  have e3 : MeasurableEmbedding (Prod.map (Neg.neg : ℝ → ℝ) (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ))) :=
    ((MeasurableEquiv.neg ℝ).prodCongr ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ))).measurableEmbedding
  exact ⟨(h1.integrable_comp_emb e1).2 hF, (h2.integrable_comp_emb e2).2 hF, (h3.integrable_comp_emb e3).2 hF⟩

theorem ae_pos_M3 : ∀ᵐ z : ℝ × ℝ × ℝ ∂M3, 0 < z.1 ∧ 0 < z.2.1 ∧ 0 < z.2.2 := by
  have h : M3 = ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ))).restrict
      (Set.Ioi 0 ×ˢ (Set.Ioi 0 ×ˢ Set.Ioi 0)) := by
    show μI.prod (μI.prod μI) = _
    rw [Measure.prod_restrict, Measure.prod_restrict]
  rw [h]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod (measurableSet_Ioi.prod measurableSet_Ioi))] with z hz
  exact ⟨hz.1, hz.2.1, hz.2.2⟩

theorem ae_pos_V3 : ∀ᵐ z : ℝ × ℝ × ℝ ∂V3, 0 < z.2.2 := by
  have h1 : Measure.QuasiMeasurePreserving (fun z : ℝ × ℝ × ℝ => z.2.2) V3 μI :=
    (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := μI)).comp
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ).prod μI))
  exact h1.ae (ae_restrict_mem measurableSet_Ioi)

noncomputable def comm (u₀ cP c₂ s : ℂ) (a : ℝ) (t q p : ℝ) : ℂ :=
  ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - c₂)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + c₂ - 2 * s - 1)) *
      (((p : ℝ) : ℂ) ^ (u₀ - c₂ - 3))) *
    ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) *
      (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))

noncomputable def Fk (W DW : ℝ → ℂ) (a : ℝ) (u₀ cP c₂ : ℂ) (a₀ sP : ZMod 2) (n δ : ℕ) (s : ℂ)
    (z : ℝ × ℝ × ℝ) : ℂ :=
  (ArchR.quasiChar 0 sP (-z.1) * ArchR.quasiChar 0 a₀ (-z.1) * ArchR.quasiChar 0 1 z.1 *
      ArchR.quasiChar 0 (n : ZMod 2) z.2.1 * ArchR.quasiChar 0 a₀ z.2.1) *
    (W (-z.1) * ((((z.2.2 : ℝ) : ℂ) * ArchR.quasiChar 0 1 z.1) *
        ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 z.1 * (((z.2.2 * z.2.1)⁻¹ : ℝ) : ℂ)) ^ δ) * DW (a * |z.1| * z.2.2 / z.2.1)) *
    ((((|z.1| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - c₂)) * (((|z.2.1| : ℝ) : ℂ) ^ (u₀ + cP + c₂ - 2 * s - 1)) *
      (((z.2.2 : ℝ) : ℂ) ^ (u₀ - c₂ - 3))) *
    ((Real.exp (-(Real.pi * z.1 ^ 2 * z.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / z.2.2 ^ 2)) : ℂ) *
      (Real.exp (-(Real.pi * a ^ 2 / z.2.1 ^ 2)) : ℂ))

noncomputable def Gw (W DW : ℝ → ℂ) (a : ℝ) (u₀ cP c₂ : ℂ) (a₀ sP : ZMod 2) (n : ℕ) (b₀ b₁ s : ℂ)
    (z : ℝ × ℝ × ℝ) : ℂ :=
  (ArchR.quasiChar 0 sP (-z.1) * ArchR.quasiChar 0 a₀ (-z.1) * ArchR.quasiChar 0 1 z.1 *
      ArchR.quasiChar 0 (n : ZMod 2) z.2.1 * ArchR.quasiChar 0 a₀ z.2.1) *
    (W (-z.1) * (b₀ * ((z.2.2 : ℂ) * ArchR.quasiChar 0 1 z.1) + b₁ * ((a : ℂ) ^ 2 * ((z.2.1⁻¹ : ℝ) : ℂ))) *
      DW (a * |z.1| * z.2.2 / z.2.1)) *
    ((((|z.1| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - c₂)) * (((|z.2.1| : ℝ) : ℂ) ^ (u₀ + cP + c₂ - 2 * s - 1)) *
      (((z.2.2 : ℝ) : ℂ) ^ (u₀ - c₂ - 3))) *
    ((Real.exp (-(Real.pi * z.1 ^ 2 * z.2.2 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / z.2.2 ^ 2)) : ℂ) *
      (Real.exp (-(Real.pi * a ^ 2 / z.2.1 ^ 2)) : ℂ))

theorem Fk_zero_eq_Gw (W DW : ℝ → ℂ) (a : ℝ) (u₀ cP c₂ : ℂ) (a₀ sP : ZMod 2) (n : ℕ) (s : ℂ) (z : ℝ × ℝ × ℝ) :
    Fk W DW a u₀ cP c₂ a₀ sP n 0 s z = Gw W DW a u₀ cP c₂ a₀ sP n 1 0 s z := by
  simp only [Fk, Gw, pow_zero, mul_one, one_mul, zero_mul, add_zero]

theorem Fk_one_eq_Gw (W DW : ℝ → ℂ) (a : ℝ) (u₀ cP c₂ : ℂ) (a₀ sP : ZMod 2) (n : ℕ) (s : ℂ) (z : ℝ × ℝ × ℝ)
    (hp : z.2.2 ≠ 0) :
    Fk W DW a u₀ cP c₂ a₀ sP n 1 s z = Gw W DW a u₀ cP c₂ a₀ sP n 0 1 s z := by
  by_cases ht : z.1 = 0
  · simp only [Fk, Gw, ht, quasiChar_zero_one_zero, mul_zero, zero_mul]
  · have hsq := quasiChar_zero_one_mul_self ht
    have hp' : ((z.2.2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp
    simp only [Fk, Gw, pow_one, zero_mul, one_mul, zero_add]
    have key : ((z.2.2 : ℝ) : ℂ) * ArchR.quasiChar 0 1 z.1 *
        ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 z.1 * (((z.2.2 * z.2.1)⁻¹ : ℝ) : ℂ)) =
        (a : ℂ) ^ 2 * ((z.2.1⁻¹ : ℝ) : ℂ) := by
      have e : ((z.2.2 : ℝ) : ℂ) * ArchR.quasiChar 0 1 z.1 *
          ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 z.1 * (((z.2.2 * z.2.1)⁻¹ : ℝ) : ℂ)) =
          (ArchR.quasiChar 0 1 z.1 * ArchR.quasiChar 0 1 z.1) * ((a : ℂ) ^ 2 * (((z.2.2 : ℝ) : ℂ) * (((z.2.2 * z.2.1)⁻¹ : ℝ) : ℂ))) := by
        ring
      rw [e, hsq, one_mul]
      push_cast
      rw [mul_inv, ← mul_assoc ((z.2.2 : ℝ) : ℂ), mul_inv_cancel₀ hp', one_mul]
    rw [key]

theorem integrable_Fk (W DW : ℝ → ℂ) (a : ℝ) (u₀ cP c₂ : ℂ) (a₀ sP : ZMod 2) (n δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (s : ℂ)
    (h : ∀ b₀ b₁ : ℂ, Integrable (Gw W DW a u₀ cP c₂ a₀ sP n b₀ b₁ s) V3) :
    Integrable (Fk W DW a u₀ cP c₂ a₀ sP n δ s) V3 := by
  rcases hδ with rfl | rfl
  · exact (h 1 0).congr (ae_of_all _ fun z => (Fk_zero_eq_Gw W DW a u₀ cP c₂ a₀ sP n s z).symm)
  · refine (h 0 1).congr ?_
    filter_upwards [ae_pos_V3] with z hz
    exact (Fk_one_eq_Gw W DW a u₀ cP c₂ a₀ sP n s z hz.ne').symm

theorem comm_eq (u₀ cP c₂ s : ℂ) (a : ℝ) (t q p : ℝ) :
    ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - c₂)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + c₂ - 2 * s - 1)) *
        (((p : ℝ) : ℂ) ^ (u₀ - c₂ - 3))) *
      ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) *
        (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ)) = comm u₀ cP c₂ s a t q p := rfl

noncomputable def bfac (δ : ℕ) (p Q : ℝ) : ℂ := if δ = 0 then ((p : ℝ) : ℂ) else ((Q⁻¹ : ℝ) : ℂ)

theorem four_point (W DW : ℝ → ℂ) (a : ℝ) (ha1 : a = -1) (u₀ cP c₂ : ℂ) (a₀ : ZMod 2) (n δ : ℕ) (hδ : δ = 0 ∨ δ = 1)
    (s : ℂ) {T Q p : ℝ} (hT : 0 < T) (hQ : 0 < Q) (hp : 0 < p) :
    Fk W DW a u₀ cP c₂ a₀ 0 n δ s (T, Q, p) + Fk W DW a u₀ cP c₂ a₀ 0 n δ s (T, -Q, p) +
      (Fk W DW a u₀ cP c₂ a₀ 0 n δ s (-T, Q, p) + Fk W DW a u₀ cP c₂ a₀ 0 n δ s (-T, -Q, p)) =
      comm u₀ cP c₂ s a T Q p * bfac δ p Q *
        ((-1 : ℂ) ^ a₀.val * (W (-T) * DW (-(T * p / Q))) +
          (-1 : ℂ) ^ δ * ((-1 : ℂ) ^ ((n : ZMod 2)).val * (W (-T) * DW (T * p / Q))) +
          (-1 : ℂ) ^ δ * (W T * DW (-(T * p / Q))) +
          (-1 : ℂ) ^ ((n : ZMod 2)).val * (-1 : ℂ) ^ a₀.val * (W T * DW (T * p / Q))) := by
  have hT0 : (T : ℂ) ≠ 0 := ofReal_ne_zero.mpr hT.ne'
  have hQ0 : (Q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hQ.ne'
  have hp0 : (p : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  have e1 : a * T * p / Q = -(T * p / Q) := by rw [ha1]; ring
  have e2 : a * T * p / -Q = T * p / Q := by rw [ha1, div_neg]; ring
  have e3 : ((p * -Q)⁻¹ : ℝ) = -((p * Q)⁻¹ : ℝ) := by rw [mul_neg, inv_neg]
  simp only [Fk, comm, bfac, abs_neg, neg_neg, even_two, Even.neg_pow]
  rw [sc_pp a₀ (n : ZMod 2) hT hQ, sc_pn a₀ (n : ZMod 2) hT hQ, sc_np a₀ (n : ZMod 2) hT hQ, sc_nn a₀ (n : ZMod 2) hT hQ]
  simp only [quasiChar_zero_of_pos 1 hT, quasiChar_zero_of_neg 1 (neg_neg_of_pos hT), val_one_zmod2,
    pow_one, abs_of_pos hT, e1, e2, e3]
  rcases hδ with rfl | rfl
  · simp only [pow_zero, mul_one, if_true]
    rw [ha1]
    push_cast
    ring
  · simp only [pow_one, if_false, one_ne_zero]
    rw [ha1]
    push_cast
    field_simp
    ring

theorem zmod2_eq_of_zero_eq_add {a₀ b : ZMod 2} (h : (0 : ZMod 2) = a₀ + b) : a₀ = b := by
  revert a₀ b; decide

theorem zmod2_eq_of_one_eq_add {a₀ b : ZMod 2} (h : (1 : ZMod 2) = a₀ + b) : a₀ = b + 1 := by
  revert a₀ b; decide

theorem zmod2_shift_of_ne {c₁ c₂ : ZMod 2} (h : c₁ ≠ c₂) (b : ZMod 2) : c₁ + (b + 1) = b + c₂ ∧ c₂ + (b + 1) = b + c₁ := by
  revert c₁ c₂ b; decide

theorem signShift_add_signShift_of_ne {c₁ c₂ : ZMod 2} (h : c₁ ≠ c₂) (b : ZMod 2) :
    signShift (c₁ + (b + 1)) + signShift (c₂ + (b + 1)) = 1 := by
  have key : (c₁ + (b + 1) = 0 ∧ c₂ + (b + 1) = 1) ∨ (c₁ + (b + 1) = 1 ∧ c₂ + (b + 1) = 0) := by
    revert c₁ c₂ b; decide
  rcases key with ⟨e₁, e₂⟩ | ⟨e₁, e₂⟩ <;> rw [e₁, e₂, signShift_zero, signShift_one] <;> norm_num

theorem eps_eq (a₀ b : ZMod 2) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = a₀ + b) :
    (-1 : ℂ) ^ a₀.val = (-1 : ℂ) ^ δ * (-1 : ℂ) ^ b.val := by
  rcases hδ with rfl | rfl
  · rw [Nat.cast_zero] at hδpar
    rw [zmod2_eq_of_zero_eq_add hδpar, pow_zero, one_mul]
  · rw [Nat.cast_one] at hδpar
    rw [zmod2_eq_of_one_eq_add hδpar, neg_one_pow_val_add_one, pow_one, neg_one_mul]

theorem fold_alg_disc (σ η ηb Wp Wm Dp Dm T G τ ρ H C B : ℂ)
    (hWm : Wm = ηb * Wp) (hWp : 2 * Wp = T * G) (hDm : Dm = 0) (hDp : Dp = ρ * τ * H) :
    C * B * ((σ * ηb) * (Wm * Dm) + σ * (η * (Wm * Dp)) + σ * (Wp * Dm) + η * (σ * ηb) * (Wp * Dp)) =
      (σ * η * ηb) * ρ * (B * (T * τ) * (G * H) * C) := by
  rw [hWm, hDm, hDp]
  linear_combination (σ * η * ηb * ρ * B * τ * H * C) * hWp

theorem neg_one_pow_natCast_val (n : ℕ) : (-1 : ℂ) ^ ((n : ZMod 2)).val = (-1 : ℂ) ^ n := by
  rw [ZMod.val_natCast]
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk, ← two_mul, Nat.mul_mod_right, pow_zero, pow_mul]; norm_num
  · rw [hk, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod, Nat.one_mod, pow_one, pow_add, pow_mul]; norm_num

theorem cpow_ofReal_add {x : ℝ} (hx : 0 < x) (a b : ℂ) : ((x : ℂ) ^ (a + b)) = (x : ℂ) ^ a * (x : ℂ) ^ b :=
  cpow_add _ _ (ofReal_ne_zero.mpr hx.ne')

theorem piece_eq (ν₁ ν₂ q₁ q₂ u₀ cP c₂ s : ℂ) (a : ℝ) (ha1 : a = -1) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1)
    {T Q p : ℝ} (hT : 0 < T) (hQ : 0 < Q) (hp : 0 < p) :
    bfac δ p Q * ((T : ℂ) * (((T * p / Q : ℝ) : ℂ))) * (MCG4 ν₁ ν₂ T * MCG4 q₁ q₂ (T * p / Q)) * comm u₀ cP c₂ s a T Q p =
      rowInt ν₁ ν₂ q₁ q₂ (s - 1 / 2 - cP - c₂) (u₀ - c₂ - 1 - δ) (u₀ + cP + c₂ - 2 * s - 2 - δ) T p Q := by
  have hT0 : (T : ℂ) ≠ 0 := ofReal_ne_zero.mpr hT.ne'
  have hQ0 : (Q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hQ.ne'
  have hp0 : (p : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  have eT : ((T : ℂ) ^ (s - 1 / 2 - cP - c₂)) = (T : ℂ) ^ (s - 5 / 2 - cP - c₂) * (T : ℂ) ^ 2 := by
    rw [show s - 1 / 2 - cP - c₂ = (s - 5 / 2 - cP - c₂) + 2 by ring, cpow_ofReal_add hT, cpow_two]
  have ea : Real.pi * a ^ 2 / p ^ 2 = Real.pi / p ^ 2 := by rw [ha1]; ring
  have ea' : Real.pi * a ^ 2 / Q ^ 2 = Real.pi / Q ^ 2 := by rw [ha1]; ring
  rcases hδ with rfl | rfl
  · have ep : ((p : ℂ) ^ (u₀ - c₂ - 1 - ((0 : ℕ) : ℂ))) = (p : ℂ) ^ (u₀ - c₂ - 3) * (p : ℂ) ^ 2 := by
      rw [show u₀ - c₂ - 1 - ((0 : ℕ) : ℂ) = (u₀ - c₂ - 3) + 2 by push_cast; ring, cpow_ofReal_add hp, cpow_two]
    have eQ : ((Q : ℂ) ^ (u₀ + cP + c₂ - 2 * s - 2 - ((0 : ℕ) : ℂ))) = (Q : ℂ) ^ (u₀ + cP + c₂ - 2 * s - 1) * (Q : ℂ)⁻¹ := by
      rw [show u₀ + cP + c₂ - 2 * s - 2 - ((0 : ℕ) : ℂ) = (u₀ + cP + c₂ - 2 * s - 1) + (-1) by push_cast; ring,
        cpow_ofReal_add hQ, cpow_neg_one]
    simp only [rowInt, MCG4, comm, bfac, if_true, abs_of_pos hT, abs_of_pos hQ, eT, ep, eQ, ea, ea']
    push_cast
    field_simp
  · have ep : ((p : ℂ) ^ (u₀ - c₂ - 1 - ((1 : ℕ) : ℂ))) = (p : ℂ) ^ (u₀ - c₂ - 3) * (p : ℂ) := by
      rw [show u₀ - c₂ - 1 - ((1 : ℕ) : ℂ) = (u₀ - c₂ - 3) + 1 by push_cast; ring, cpow_ofReal_add hp, cpow_one]
    have eQ : ((Q : ℂ) ^ (u₀ + cP + c₂ - 2 * s - 2 - ((1 : ℕ) : ℂ))) =
        (Q : ℂ) ^ (u₀ + cP + c₂ - 2 * s - 1) * ((Q : ℂ)⁻¹ * (Q : ℂ)⁻¹) := by
      rw [show u₀ + cP + c₂ - 2 * s - 2 - ((1 : ℕ) : ℂ) = (u₀ + cP + c₂ - 2 * s - 1) + ((-1) + (-1)) by push_cast; ring,
        cpow_ofReal_add hQ, cpow_ofReal_add hQ, cpow_neg_one]
    simp only [rowInt, MCG4, comm, bfac, one_ne_zero, if_false, abs_of_pos hT, abs_of_pos hQ, eT, ep, eQ, ea, ea']
    push_cast
    field_simp

theorem Gammaℝ_congr {x y : ℂ} (h : x = y) : Gammaℝ x = Gammaℝ y := by rw [h]

theorem re_pos_congr {x y : ℂ} (h : 0 < x.re) (e : y = x) : 0 < y.re := by rw [e]; exact h

theorem core (ν₁ ν₂ q₁ q₂ u₀ cP c₂ : ℂ) (n δ : ℕ) (s : ℂ) (hcP : cP = ν₁ + ν₂) (hq : q₁ + q₂ = c₂ + n)
    (hy₁ : 0 < (s + 1 / 2 - ν₁ - u₀ + δ).re) (hy₂ : 0 < (s + 1 / 2 - ν₂ - u₀ + δ).re)
    (h₁₁ : 0 < (s + 1 / 2 - cP - c₂ + ν₁ + q₁).re) (h₁₂ : 0 < (s + 1 / 2 - cP - c₂ + ν₁ + q₂).re)
    (h₂₁ : 0 < (s + 1 / 2 - cP - c₂ + ν₂ + q₁).re) (h₂₂ : 0 < (s + 1 / 2 - cP - c₂ + ν₂ + q₂).re)
    (hΓ : Gammaℝ (2 * s - cP - c₂ + n + 1) ≠ 0)
    (hI : Integrable (fun z : ℝ × ℝ × ℝ =>
      rowInt ν₁ ν₂ q₁ q₂ (s - 1 / 2 - cP - c₂) (u₀ - c₂ - 1 - δ) (u₀ + cP + c₂ - 2 * s - 2 - δ) z.1 z.2.2 z.2.1) M3) :
    Gammaℝ (2 * s - cP - c₂ + n + 1) *
        (∫ z, rowInt ν₁ ν₂ q₁ q₂ (s - 1 / 2 - cP - c₂) (u₀ - c₂ - 1 - δ) (u₀ + cP + c₂ - 2 * s - 2 - δ) z.1 z.2.2 z.2.1 ∂M3) =
      (1 / 2 : ℂ) * (Gammaℝ (s + 1 / 2 - ν₂ - u₀ + δ) * Gammaℝ (s + 1 / 2 - ν₁ - u₀ + δ)) *
        (Gammaℝ (s + 1 / 2 - cP - c₂ + ν₁ + q₁) * Gammaℝ (s + 1 / 2 - cP - c₂ + ν₁ + q₂) *
          Gammaℝ (s + 1 / 2 - cP - c₂ + ν₂ + q₁) * Gammaℝ (s + 1 / 2 - cP - c₂ + ν₂ + q₂)) := by
  set α : ℂ := s - 1 / 2 - cP - c₂ with hα
  set β : ℂ := u₀ - c₂ - 1 - δ with hβ
  set γ : ℂ := u₀ + cP + c₂ - 2 * s - 2 - δ with hγ
  rw [integral_prod3_perm_eq_iterated _ hI]
  rw [row_balanced ν₁ ν₂ q₁ q₂ α β γ (by rw [hα, hβ, hγ, hcP]; ring)
    (re_pos_congr hy₂ (by rw [hα, hβ, hcP]; ring)) (re_pos_congr hy₁ (by rw [hα, hβ, hcP]; ring))
    (re_pos_congr h₁₁ (by rw [hα]; ring)) (re_pos_congr h₁₂ (by rw [hα]; ring))
    (re_pos_congr h₂₁ (by rw [hα]; ring)) (re_pos_congr h₂₂ (by rw [hα]; ring))]
  rw [Gammaℝ_congr (show α - β + ν₁ = s + 1 / 2 - ν₂ - u₀ + δ by rw [hα, hβ, hcP]; ring),
    Gammaℝ_congr (show α - β + ν₂ = s + 1 / 2 - ν₁ - u₀ + δ by rw [hα, hβ, hcP]; ring),
    Gammaℝ_congr (show α + 1 + ν₁ + q₁ = s + 1 / 2 - cP - c₂ + ν₁ + q₁ by rw [hα]; ring),
    Gammaℝ_congr (show α + 1 + ν₁ + q₂ = s + 1 / 2 - cP - c₂ + ν₁ + q₂ by rw [hα]; ring),
    Gammaℝ_congr (show α + 1 + ν₂ + q₁ = s + 1 / 2 - cP - c₂ + ν₂ + q₁ by rw [hα]; ring),
    Gammaℝ_congr (show α + 1 + ν₂ + q₂ = s + 1 / 2 - cP - c₂ + ν₂ + q₂ by rw [hα]; ring),
    Gammaℝ_congr (show β - γ + q₁ + q₂ = 2 * s - cP - c₂ + n + 1 by
      rw [hβ, hγ, add_assoc, hq]; ring)]
  field_simp

theorem re_pos_of_norm_lt3 (s x y z : ℂ) (h : ‖x‖ + ‖y‖ + ‖z‖ < s.re) : 0 < (s + 1 / 2 - x - y + z).re := by
  have hx := (abs_le.1 (Complex.abs_re_le_norm x)).2
  have hy := (abs_le.1 (Complex.abs_re_le_norm y)).2
  have hz := (abs_le.1 (Complex.abs_re_le_norm z)).1
  simp only [sub_re, add_re, one_div, inv_re, re_ofNat, normSq_ofNat]
  norm_num
  linarith

theorem norm_signShift_le (e : ZMod 2) : ‖(signShift e : ℂ)‖ ≤ 1 := by
  unfold signShift; split_ifs <;> simp

theorem dualEvalZeroDisc
    (ν₁ ν₂ : ℂ) (b : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hWpar : ∀ t : ℝ, W (-t) = (-1 : ℂ) ^ b.val * W t)
    (hW : ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (b + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (b + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (u : ℂ) (m : ℕ) (hm : 1 ≤ m) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.discrete u m hm)
    (ρ : ℂ)
    (hρ : (∀ τ : ℝ, 0 < τ →
        D.W (ArchR.diagOne τ) = ρ * ((2 : ℂ) * ((τ : ℂ) ^ (u + (m : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * τ)) : ℂ)))) ∧
      (∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = 0))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (hcP : cP = ν₁ + ν₂) (a₀ sP : ZMod 2) (hsP : sP = b + b)
    (n : ℕ) (hn : n = m + 1) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = a₀ + b) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + n + 1) *
        (∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
          (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 (n : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * ((((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 t) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 t * (((p * q)⁻¹ : ℝ) : ℂ)) ^ δ) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))) =
      (-1 : ℂ) ^ (b.val + δ + m + 1) * ρ * (1 / 2 : ℂ) *
        ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₀) + signShift (b + a₀))) *
          Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₀) + signShift (b + a₀)))) *
          ((Complex.Gammaℝ (s + 1 / 2 + (-ν₁ + (-u + (m : ℂ) / 2))) *
            Complex.Gammaℝ (s + 1 / 2 + (-ν₁ + (-u + (m : ℂ) / 2)) + 1)) *
            (Complex.Gammaℝ (s + 1 / 2 + (-ν₂ + (-u + (m : ℂ) / 2))) *
              Complex.Gammaℝ (s + 1 / 2 + (-ν₂ + (-u + (m : ℂ) / 2)) + 1)))) := by
  have hc2 : P₂.centralExponent = 2 * u := by rw [hP₂]; rfl
  have hbb : b + b = 0 := CharTwo.add_self_eq_zero b
  obtain rfl : sP = 0 := hsP.trans hbb
  subst hn
  have ha : a ≠ 0 := by rw [ha1]; norm_num

  obtain ⟨σb, hB⟩ :=
    LanglandsTunnell.Converse.exists_forall_integrable_dualQuadruple_and_torusTriple_detPow_colHarmonic_of_evenSheet
      ν₁ ν₂ b W hWc hWpar hW D a ha u₀ cP a₀ 0 (m + 1) δ hδ

  set G : ℝ → ℂ := fun T => MCG4 ν₁ ν₂ T with hG
  set γ₀ : ℂ := u + (m : ℂ) / 2 with hγ₀
  set H : ℝ → ℂ := fun τ => MCG4 γ₀ (γ₀ + 1) τ with hH
  have hWp : ∀ T : ℝ, 0 < T → 2 * W T = (T : ℂ) * G T := fun T hT => by
    have h := hW T hT
    rw [hWpar T, hbb, signShift_zero, add_zero, add_zero] at h
    simp only [hG, MCG4]
    rw [← h]
    rcases neg_one_pow_val_cases b with e | e <;> rw [e] <;> ring
  have hHval : ∀ τ : ℝ, 0 < τ → H τ = 2 * ((τ : ℂ) ^ γ₀ * (Real.exp (-(2 * Real.pi * τ)) : ℂ)) := fun τ hτ => by
    simp only [hH, MCG4]
    exact LanglandsTunnell.mulConvGaussian_add_one_eq_two_mul_cpow_mul_exp_neg_two_pi_mul γ₀ τ hτ
  have hDp : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne τ) = ρ * (τ : ℂ) * H τ := fun τ hτ => by
    rw [hρ.1 τ hτ, hHval τ hτ, hγ₀, cpow_add _ _ (ofReal_ne_zero.mpr hτ.ne'), cpow_one]
    ring
  have hDm : ∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = 0 := hρ.2
  have hqsum : γ₀ + (γ₀ + 1) = P₂.centralExponent + ((m + 1 : ℕ) : ℂ) := by
    rw [hγ₀, hc2]; push_cast; ring

  refine ⟨max σb (‖u₀‖ + ‖ν₁‖ + ‖ν₂‖ + ‖u‖ + m + 4), fun s hs => ?_⟩
  have hsb : σb < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs0 : ‖u₀‖ + ‖ν₁‖ + ‖ν₂‖ + ‖u‖ + m + 4 < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  have n0 := norm_nonneg u₀; have n1 := norm_nonneg ν₁; have n2 := norm_nonneg ν₂
  have n3 := norm_nonneg u
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have nδ : ‖((δ : ℕ) : ℂ)‖ ≤ 1 := by
    rcases hδ with rfl | rfl <;> simp
  have nγ : ‖γ₀‖ ≤ ‖u‖ + m := by
    rw [hγ₀]
    refine (norm_add_le _ _).trans ?_
    have : ‖((m : ℂ)) / 2‖ ≤ (m : ℝ) := by
      rw [norm_div, Complex.norm_natCast, Complex.norm_ofNat]; linarith
    linarith
  have nγ1 : ‖γ₀ + 1‖ ≤ ‖u‖ + m + 1 := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
  have nm2 : ‖((m : ℂ)) / 2‖ ≤ (m : ℝ) := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_ofNat]; linarith
  have nm21 : ‖((m : ℂ)) / 2 + 1‖ ≤ (m : ℝ) + 1 := (norm_add_le _ _).trans (by rw [norm_one]; linarith)

  have hGw : ∀ b₀ b₁ : ℂ, Integrable (Gw W (fun x : ℝ => D.W (ArchR.diagOne x)) a u₀ cP P₂.centralExponent a₀ 0 (m + 1) b₀ b₁ s) V3 :=
    fun b₀ b₁ => (hB s hsb).2 b₀ b₁
  obtain ⟨F, hF⟩ : ∃ F : ℝ × ℝ × ℝ → ℂ, F = Fk W (fun x : ℝ => D.W (ArchR.diagOne x)) a u₀ cP P₂.centralExponent a₀ 0 (m + 1) δ s :=
    ⟨_, rfl⟩
  have hFint : Integrable F V3 := by
    rw [hF]; exact integrable_Fk W _ a u₀ cP P₂.centralExponent a₀ 0 (m + 1) δ hδ s hGw
  have hLHS : (∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
          (ArchR.quasiChar 0 0 (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 ((m + 1 : ℕ) : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * ((((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 t) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 t * (((p * q)⁻¹ : ℝ) : ℂ)) ^ δ) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))) =
      ∫ z, F z ∂V3 := by
    rw [integral_prod _ hFint]
    refine integral_congr_ae ?_
    filter_upwards [hFint.prod_right_ae] with t ht
    rw [integral_prod _ ht, hF]
    rfl

  obtain ⟨i1, i2, i3⟩ := integrable_reflects F hFint
  have j0 : Integrable F M3 := hFint.mono_measure M3_le_V3
  have j1 := i1.mono_measure M3_le_V3
  have j2 := i2.mono_measure M3_le_V3
  have j3 := i3.mono_measure M3_le_V3
  set S : ℝ × ℝ × ℝ → ℂ := fun z => F z + F (z.1, -z.2.1, z.2.2) + (F (-z.1, z.2) + F (-z.1, -z.2.1, z.2.2)) with hSdef
  have hSint : Integrable S M3 := (j0.add j1).add (j2.add j3)
  have hfold : (∫ z, F z ∂V3) = ∫ z, S z ∂M3 := by
    rw [integral_prod3_eq_sum_four μI F hFint]
    have eA : (∫ z, F z ∂M3) + (∫ z, F (z.1, -z.2.1, z.2.2) ∂M3) = ∫ z, (F z + F (z.1, -z.2.1, z.2.2)) ∂M3 :=
      (integral_add j0 j1).symm
    have eB : (∫ z, F (-z.1, z.2) ∂M3) + (∫ z, F (-z.1, -z.2.1, z.2.2) ∂M3) =
        ∫ z, (F (-z.1, z.2) + F (-z.1, -z.2.1, z.2.2)) ∂M3 := (integral_add j2 j3).symm
    rw [eA, eB]
    exact (integral_add (j0.add j1) (j2.add j3)).symm

  set Kc : ℂ := ((-1 : ℂ) ^ δ * (-1 : ℂ) ^ (((m + 1 : ℕ) : ZMod 2)).val * (-1 : ℂ) ^ b.val) * ρ with hKc
  have hSae : ∀ᵐ z : ℝ × ℝ × ℝ ∂M3, S z = Kc *
      rowInt ν₁ ν₂ γ₀ (γ₀ + 1) (s - 1 / 2 - cP - P₂.centralExponent) (u₀ - P₂.centralExponent - 1 - δ)
        (u₀ + cP + P₂.centralExponent - 2 * s - 2 - δ) z.1 z.2.2 z.2.1 := by
    filter_upwards [ae_pos_M3] with z hz
    obtain ⟨hT, hQ, hp⟩ := hz
    obtain ⟨T, Q, p⟩ := z
    simp only at hT hQ hp ⊢
    have hτ : 0 < T * p / Q := div_pos (mul_pos hT hp) hQ
    rw [hSdef]
    simp only
    rw [hF, four_point W _ a ha1 u₀ cP P₂.centralExponent a₀ (m + 1) δ hδ s hT hQ hp, eps_eq a₀ b δ hδ hδpar]
    rw [fold_alg_disc ((-1 : ℂ) ^ δ) ((-1 : ℂ) ^ (((m + 1 : ℕ) : ZMod 2)).val) ((-1 : ℂ) ^ b.val) (W T) (W (-T))
      (D.W (ArchR.diagOne (T * p / Q))) (D.W (ArchR.diagOne (-(T * p / Q)))) (T : ℂ) (G T) (((T * p / Q : ℝ) : ℂ)) ρ
      (H (T * p / Q)) (comm u₀ cP P₂.centralExponent s a T Q p) (bfac δ p Q)
      (hWpar T) (hWp T hT) (hDm _ hτ) (by have := hDp (T * p / Q) hτ; push_cast at this ⊢; exact this)]
    rw [← piece_eq ν₁ ν₂ γ₀ (γ₀ + 1) u₀ cP P₂.centralExponent s a ha1 δ hδ hT hQ hp]

  rw [hLHS, hfold, integral_congr_ae hSae, integral_const_mul]

  have hcore := core ν₁ ν₂ γ₀ (γ₀ + 1) u₀ cP P₂.centralExponent (m + 1) δ s hcP hqsum
    (re_pos_of_norm_lt3 s ν₁ u₀ δ (by linarith)) (re_pos_of_norm_lt3 s ν₂ u₀ δ (by linarith))
    (re_pos_congr (re_pos_of_norm_lt3 s ν₂ u ((m : ℂ) / 2) (by linarith)) (by rw [hcP, hc2, hγ₀]; ring))
    (re_pos_congr (re_pos_of_norm_lt3 s ν₂ u ((m : ℂ) / 2 + 1) (by linarith)) (by rw [hcP, hc2, hγ₀]; ring))
    (re_pos_congr (re_pos_of_norm_lt3 s ν₁ u ((m : ℂ) / 2) (by linarith)) (by rw [hcP, hc2, hγ₀]; ring))
    (re_pos_congr (re_pos_of_norm_lt3 s ν₁ u ((m : ℂ) / 2 + 1) (by linarith)) (by rw [hcP, hc2, hγ₀]; ring))
    (Gammaℝ_ne_zero_of_re_pos (by
      have b₅ := (abs_le.1 (Complex.abs_re_le_norm cP)).2
      have b₆ := (abs_le.1 (Complex.abs_re_le_norm u)).2
      have : ‖cP‖ ≤ ‖ν₁‖ + ‖ν₂‖ := by rw [hcP]; exact norm_add_le _ _
      rw [hc2]
      simp only [add_re, sub_re, mul_re, re_ofNat, im_ofNat, natCast_re, one_re, zero_mul, sub_zero]
      push_cast
      linarith))
  by_cases hK0 : Kc = 0
  · have hρ0 : ρ = 0 := by
      have h := hK0
      rw [hKc] at h
      rcases mul_eq_zero.mp h with h1 | h1
      · exfalso
        rcases mul_eq_zero.mp h1 with h2 | h2
        · rcases mul_eq_zero.mp h2 with h3 | h3
          · exact (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)) h3
          · exact (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)) h3
        · exact (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)) h2
      · exact h1
    rw [hK0, zero_mul, mul_zero, hρ0]
    ring
  have hIrow : Integrable (fun z : ℝ × ℝ × ℝ =>
      rowInt ν₁ ν₂ γ₀ (γ₀ + 1) (s - 1 / 2 - cP - P₂.centralExponent) (u₀ - P₂.centralExponent - 1 - δ)
        (u₀ + cP + P₂.centralExponent - 2 * s - 2 - δ) z.1 z.2.2 z.2.1) M3 := by
    have := (hSint.congr hSae).const_mul Kc⁻¹
    refine this.congr (ae_of_all _ fun z => ?_)
    simp only
    rw [← mul_assoc, inv_mul_cancel₀ hK0, one_mul]
  have key := hcore hIrow
  rw [← mul_assoc, mul_comm (Gammaℝ _) Kc, mul_assoc, key]

  have hshift : signShift (b + a₀) = ((δ : ℕ) : ℂ) := by
    rw [add_comm, ← hδpar]; rcases hδ with rfl | rfl <;> simp
  rw [hshift, hKc, neg_one_pow_natCast_val, hcP, hc2, hγ₀]
  rw [Gammaℝ_congr (show s + 1 / 2 + ((-ν₁ + -u₀) + ((δ : ℕ) : ℂ)) = s + 1 / 2 - ν₁ - u₀ + δ by ring),
    Gammaℝ_congr (show s + 1 / 2 + ((-ν₂ + -u₀) + ((δ : ℕ) : ℂ)) = s + 1 / 2 - ν₂ - u₀ + δ by ring),
    Gammaℝ_congr (show s + 1 / 2 + (-ν₁ + (-u + (m : ℂ) / 2)) =
      s + 1 / 2 - (ν₁ + ν₂) - 2 * u + ν₂ + (u + (m : ℂ) / 2) by ring),
    Gammaℝ_congr (show s + 1 / 2 + (-ν₁ + (-u + (m : ℂ) / 2)) + 1 =
      s + 1 / 2 - (ν₁ + ν₂) - 2 * u + ν₂ + (u + (m : ℂ) / 2 + 1) by ring),
    Gammaℝ_congr (show s + 1 / 2 + (-ν₂ + (-u + (m : ℂ) / 2)) =
      s + 1 / 2 - (ν₁ + ν₂) - 2 * u + ν₁ + (u + (m : ℂ) / 2) by ring),
    Gammaℝ_congr (show s + 1 / 2 + (-ν₂ + (-u + (m : ℂ) / 2)) + 1 =
      s + 1 / 2 - (ν₁ + ν₂) - 2 * u + ν₁ + (u + (m : ℂ) / 2 + 1) by ring)]
  simp only [pow_add, pow_one]
  ring

end KcDualEvalZeroDisc
p2m_reactivate "P2MW.S_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_detPow_colHarmonic_eq_mul_prod_GammaR_of_evenPrincipal_of_discreteProfile.KcDualEvalZeroDisc"

theorem solution
    (ν₁ ν₂ : ℂ) (b : ZMod 2)
    (W : ℝ → ℂ) (hWc : ContinuousOn W {t : ℝ | t ≠ 0})
    (hWpar : ∀ t : ℝ, W (-t) = (-1 : ℂ) ^ b.val * W t)
    (hW : ∀ t : ℝ, 0 < t →
      W t + (-1 : ℂ) ^ b.val * W (-t) =
        (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (ν₁ + signShift (b + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              ((((t) / r : ℝ) : ℂ) ^ (ν₂ + signShift (b + b)) * (Real.exp (-(Real.pi * ((t) / r) ^ 2)) : ℂ)) / (r : ℂ)))
    (u : ℂ) (m : ℕ) (hm : 1 ≤ m) {P₂ : RealArchParam} (D : ArchDatumR P₂) (hP₂ : P₂ = RealArchParam.discrete u m hm)
    (ρ : ℂ)
    (hρ : (∀ τ : ℝ, 0 < τ →
        D.W (ArchR.diagOne τ) = ρ * ((2 : ℂ) * ((τ : ℂ) ^ (u + (m : ℂ) / 2 + 1) * (Real.exp (-(2 * Real.pi * τ)) : ℂ)))) ∧
      (∀ τ : ℝ, 0 < τ → D.W (ArchR.diagOne (-τ)) = 0))
    (a : ℝ) (ha1 : a = -1) (u₀ cP : ℂ) (hcP : cP = ν₁ + ν₂) (a₀ sP : ZMod 2) (hsP : sP = b + b)
    (n : ℕ) (hn : n = m + 1) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1) (hδpar : ((δ : ℕ) : ZMod 2) = a₀ + b) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Complex.Gammaℝ (2 * s - cP - P₂.centralExponent + n + 1) *
        (∫ t : ℝ, ∫ q : ℝ, ∫ p in Set.Ioi (0 : ℝ),
          (ArchR.quasiChar 0 sP (-t) * ArchR.quasiChar 0 a₀ (-t) * ArchR.quasiChar 0 1 t * ArchR.quasiChar 0 (n : ZMod 2) q * ArchR.quasiChar 0 a₀ q) *
          (W (-t) * ((((p : ℝ) : ℂ) * ArchR.quasiChar 0 1 t) * ((a : ℂ) ^ 2 * ArchR.quasiChar 0 1 t * (((p * q)⁻¹ : ℝ) : ℂ)) ^ δ) * D.W (ArchR.diagOne (a * |t| * p / q))) *
          ((((|t| : ℝ) : ℂ) ^ (s - 5 / 2 - cP - P₂.centralExponent)) * (((|q| : ℝ) : ℂ) ^ (u₀ + cP + P₂.centralExponent - 2 * s - 1)) *
            (((p : ℝ) : ℂ) ^ (u₀ - P₂.centralExponent - 3))) *
          ((Real.exp (-(Real.pi * t ^ 2 * p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / p ^ 2)) : ℂ) * (Real.exp (-(Real.pi * a ^ 2 / q ^ 2)) : ℂ))) =
      (-1 : ℂ) ^ (b.val + δ + m + 1) * ρ * (1 / 2 : ℂ) *
        ((Complex.Gammaℝ (s + 1 / 2 + ((-ν₁ + -u₀) + signShift (b + a₀))) *
          Complex.Gammaℝ (s + 1 / 2 + ((-ν₂ + -u₀) + signShift (b + a₀)))) *
          ((Complex.Gammaℝ (s + 1 / 2 + (-ν₁ + (-u + (m : ℂ) / 2))) *
            Complex.Gammaℝ (s + 1 / 2 + (-ν₁ + (-u + (m : ℂ) / 2)) + 1)) *
            (Complex.Gammaℝ (s + 1 / 2 + (-ν₂ + (-u + (m : ℂ) / 2))) *
              Complex.Gammaℝ (s + 1 / 2 + (-ν₂ + (-u + (m : ℂ) / 2)) + 1)))) := by
  exact KcDualEvalZeroDisc.dualEvalZeroDisc ν₁ ν₂ b W hWc hWpar hW u m hm D hP₂ ρ hρ a ha1 u₀ cP hcP a₀ sP hsP n hn δ hδ hδpar

end S_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_detPow_colHarmonic_eq_mul_prod_GammaR_of_evenPrincipal_of_discreteProfile
end P2MW
export P2MW.S_LanglandsTunnell_Converse_GammaR_mul_integral_dualTorusTriple_detPow_colHarmonic_eq_mul_prod_GammaR_of_evenPrincipal_of_discreteProfile (solution)
