-- Prove2me | solution 1 for NumberField.TateGlobal.exists_norm_partialEulerProduct_continuation_le_mul_exp_mul_im_sq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/046ca69e-8ea9-5cb5-be5f-c963e974a291

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_LanglandsTunnell_HeckeTate
import Theorems.Thm_LanglandsTunnell_HeckeTate_isNicePinned_heckeDatum
import Theorems.Thm_LanglandsTunnell_Converse_exists_isArchCompAt_of_isReal
import Theorems.Thm_LanglandsTunnell_Converse_exists_isArchCompAt_of_isComplex
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_norm_partialEulerProduct_continuation_le_mul_exp_mul_im_sq
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_1 IsDedekindDomain.HeightOneSpectrum.instMulActionHomClassAlgHomTensorProductAdicCompletionForallValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.Extension.instAlgebraAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteForallValEqUnderOfFiniteDimensional_definitions IsDedekindDomain.HeightOneSpectrum.instIsBiscalarSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersTensorProductCoeAlgHomTensorAdicCompletionIntegersTo IsDedekindDomain.HeightOneSpectrum.Extension.instContinuousSMulAdicCompletionValEqUnder IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopology IsDedekindDomain.HeightOneSpectrum.Extension.instFiniteSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnderOfFiniteDimensional IsDedekindDomain.HeightOneSpectrum.adicCompletion.instFiniteValEqUnderOfFiniteDimensional_definitions instIsBiscalarTensorProductCoeAlgHomBaseChange_of_algebraMap IsDedekindDomain.HeightOneSpectrum.instIsScalarTowerSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersValEqUnder_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsModuleTopologyPi Submodule.instIsTopologicalModuleSubtypeMem Pi.instTopologicalModule IsTopologicalModule.toContinuousSMul IsTopologicalModule.toContinuousAdd instFunLike SemialgHomClass.toSemilinearMapClass instCoeTCSemialgHom SemialgHomClass.toRingHomClass SemialgHomClass.instSemialgHom"
p2m_attr_erase "simp" "LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent SemialgHom.baseChange_of_algebraMap_tmul_left SemialgHom.baseChangeRightOfAlgebraMap_apply Pi.semialgHomPi_apply Pi.semialgHom_apply Module.Basis.rightBaseChange_apply LinearEquiv.coe_mulLeft LinearEquiv.coe_mulRight WithVal.semialgebraMap_toFun_ofVal Module.Basis.rightBaseChange_repr IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.tensorCoe_tmul IsDedekindDomain.HeightOneSpectrum.tensorAdicCompletionIntegersTo_tmul SemialgHom.baseChangeRightOfAlgebraMap_coe IsDedekindDomain.HeightOneSpectrum.adicCompletion.integerBaseChangeLinearEquiv_tmul_apply SemialgHom.baseChange_of_algebraMap_tmul_right IsLocalization.map_moduleTensorEquiv_symm_tmul IsLocalization.leftModuleTensorEquiv_apply IsLocalization.moduleLid_symm_apply IsLocalization.leftModuleTensorEquiv_symm_apply IsLocalization.map_moduleTensorEquiv_tmul IsModuleTopology.continuousLinearEquiv_apply AlgEquiv.extendScalars_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_symm_apply IsModuleTopology.Module.Basis.equivFun_homeo_apply IsModuleTopology.continuousAlgEquivOfIsBiscalar_apply AlgEquiv.extendScalars_apply IsModuleTopology.continuousLinearEquiv_symm_apply SemialgHom.restrictScalars_toFun SemialgHom.mk.sizeOf_spec"
p2m_attr_erase "simp" "SemialgHom.mk.injEq SemialgHom.coe_coe coe_mk TensorProduct.RightActions.smul_def TensorProduct.RightActions.Module.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.LinearMap.baseChange_id TensorProduct.RightActions.algebraMap_eval TensorProduct.RightActions.Module.TensorProduct.comm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_symm_apply_tmul TensorProduct.RightActions.Algebra.TensorProduct.comm_apply_tmul M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal NumberField.InfinitePlace
open LanglandsTunnell LanglandsTunnell.Converse LanglandsTunnell.HeckeTate LanglandsTunnell.TateLocal
open Complex Filter Set Polynomial
open scoped Topology

namespace R4G2a

theorem norm_sin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-z * I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]; congr 1; simp
  have h2 : ‖Complex.exp (z * I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]; congr 1; simp
  have hle1 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
  have hle2 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  calc ‖(Complex.exp (-z * I) - Complex.exp (z * I)) * I / 2‖
      = ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ / 2 := by
        rw [norm_div, norm_mul, Complex.norm_I, mul_one]; simp
    _ ≤ (‖Complex.exp (-z * I)‖ + ‖Complex.exp (z * I)‖) / 2 := by
        gcongr; exact norm_sub_le _ _
    _ ≤ Real.exp |z.im| := by rw [h1, h2]; linarith

theorem norm_Gamma_le_real_Gamma (w : ℂ) (hw : 0 < w.re) : ‖Gamma w‖ ≤ Real.Gamma w.re := by
  rw [Complex.Gamma_eq_integral hw, Complex.GammaIntegral, Real.Gamma_eq_integral hw]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx' : 0 < x := hx
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx', sub_re, one_re]

theorem norm_Gamma_le_norm_Gamma_add_nat (w : ℂ) (hw : 1 ≤ |w.im|) (m : ℕ) :
    ‖Gamma w‖ ≤ ‖Gamma (w + m)‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hne : w + m ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      rw [this] at hw; norm_num at hw
    have hnorm : 1 ≤ ‖w + m‖ := by
      calc (1 : ℝ) ≤ |w.im| := hw
        _ = |(w + m).im| := by simp
        _ ≤ ‖w + m‖ := abs_im_le_norm _
    have hstep : Gamma (w + (m + 1 : ℕ)) = (w + m) * Gamma (w + m) := by
      rw [show w + ((m + 1 : ℕ) : ℂ) = (w + m) + 1 by push_cast; ring]
      exact Complex.Gamma_add_one _ hne
    rw [hstep, norm_mul]
    calc ‖Gamma w‖ ≤ ‖Gamma (w + m)‖ := ih
      _ = 1 * ‖Gamma (w + m)‖ := (one_mul _).symm
      _ ≤ ‖w + m‖ * ‖Gamma (w + m)‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

theorem real_Gamma_le_max (x X : ℝ) (h1 : 1 ≤ x) (h2 : x ≤ X) : Real.Gamma x ≤ max 1 (Real.Gamma X) := by
  have hX : 1 ≤ X := h1.trans h2
  have hseg : x ∈ segment ℝ (1 : ℝ) X := by rw [segment_eq_Icc hX]; exact ⟨h1, h2⟩
  have h := Real.convexOn_Gamma.le_on_segment (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
    (show X ∈ Set.Ioi (0 : ℝ) from lt_of_lt_of_le one_pos hX) hseg
  rwa [Real.Gamma_one] at h

theorem norm_inv_Gamma_le (a b : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖(Gamma s)⁻¹‖ ≤ B * Real.exp (Real.pi * |s.im|) := by
  set m : ℕ := Nat.ceil b with hm
  set X : ℝ := 1 + m - a with hX
  refine ⟨max 1 (Real.Gamma X), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro s hsa hsb hsi
  have hmb : b ≤ m := Nat.le_ceil b
  have him0 : s.im ≠ 0 := by
    intro h; rw [h] at hsi; norm_num at hsi
  have hsin : Complex.sin (Real.pi * s) ≠ 0 := by
    rw [Ne, Complex.sin_eq_zero_iff, not_exists]
    intro k hk
    have := congrArg Complex.im hk
    simp at this
    exact him0 this
  have hΓ : Gamma s ≠ 0 := by
    refine Complex.Gamma_ne_zero fun n h => ?_
    have := congrArg Complex.im h
    simp at this
    exact him0 this
  have hrefl := Complex.Gamma_mul_Gamma_one_sub s
  have hπ0 : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hinv : (Gamma s)⁻¹ = Gamma (1 - s) * Complex.sin (Real.pi * s) / Real.pi := by
    have h1 : Gamma s * (Gamma (1 - s) * Complex.sin (Real.pi * s) / Real.pi) = 1 := by
      rw [← mul_div_assoc, ← mul_assoc, hrefl]
      field_simp
    exact (eq_inv_of_mul_eq_one_right h1).symm
  have h1s_im : 1 ≤ |(1 - s).im| := by simpa using hsi
  have hshift := norm_Gamma_le_norm_Gamma_add_nat (1 - s) h1s_im m
  have hre : (1 - s + m).re = 1 + m - s.re := by simp; ring
  have hre_pos : 0 < (1 - s + m).re := by rw [hre]; linarith
  have hreal := norm_Gamma_le_real_Gamma (1 - s + m) hre_pos
  rw [hre] at hreal
  have hmax := real_Gamma_le_max (1 + m - s.re) X (by linarith) (by rw [hX]; linarith)
  have hΓ1s : ‖Gamma (1 - s)‖ ≤ max 1 (Real.Gamma X) := hshift.trans (hreal.trans hmax)
  have hsinle : ‖Complex.sin (Real.pi * s)‖ ≤ Real.exp (Real.pi * |s.im|) := by
    have := norm_sin_le_exp_abs_im (Real.pi * s)
    have him : |((Real.pi : ℂ) * s).im| = Real.pi * |s.im| := by
      simp [abs_mul, abs_of_pos Real.pi_pos]
    rwa [him] at this
  rw [hinv, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hπ1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  calc ‖Gamma (1 - s)‖ * ‖Complex.sin (Real.pi * s)‖ / Real.pi
      ≤ ‖Gamma (1 - s)‖ * ‖Complex.sin (Real.pi * s)‖ / 1 :=
        div_le_div_of_nonneg_left (by positivity) one_pos hπ1
    _ ≤ max 1 (Real.Gamma X) * Real.exp (Real.pi * |s.im|) := by
        rw [div_one]
        exact mul_le_mul hΓ1s hsinle (norm_nonneg _) (zero_le_one.trans (le_max_left _ _))

theorem differentiable_Gammaℂ_inv : Differentiable ℂ (fun s : ℂ => (Gammaℂ s)⁻¹) := by
  have : (fun s : ℂ => (Gammaℂ s)⁻¹) = fun s => (Gammaℝ s)⁻¹ * (Gammaℝ (s + 1))⁻¹ := by
    funext s; rw [← Gammaℝ_mul_Gammaℝ_add_one, mul_inv]
  rw [this]
  exact differentiable_Gammaℝ_inv.mul (differentiable_Gammaℝ_inv.comp (differentiable_id.add_const 1))

theorem Gammaℂ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) : Gammaℂ s ≠ 0 := by
  rw [← Gammaℝ_mul_Gammaℝ_add_one]
  refine mul_ne_zero (Gammaℝ_ne_zero_of_re_pos hs) (Gammaℝ_ne_zero_of_re_pos ?_)
  simp only [add_re, one_re]; linarith

def GB (f : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, ∃ B C : ℝ, 0 ≤ B ∧ 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ B * Real.exp (C * s.im ^ 2)

theorem GB.mul {f g : ℂ → ℂ} (hf : GB f) (hg : GB g) : GB (fun s => f s * g s) := by
  intro a b
  obtain ⟨B₁, C₁, hB₁, hC₁, h₁⟩ := hf a b
  obtain ⟨B₂, C₂, hB₂, hC₂, h₂⟩ := hg a b
  refine ⟨B₁ * B₂, C₁ + C₂, mul_nonneg hB₁ hB₂, add_nonneg hC₁ hC₂, fun s hsa hsb => ?_⟩
  rw [norm_mul, add_mul, Real.exp_add]
  calc ‖f s‖ * ‖g s‖ ≤ (B₁ * Real.exp (C₁ * s.im ^ 2)) * (B₂ * Real.exp (C₂ * s.im ^ 2)) :=
        mul_le_mul (h₁ s hsa hsb) (h₂ s hsa hsb) (norm_nonneg _) (by positivity)
    _ = B₁ * B₂ * (Real.exp (C₁ * s.im ^ 2) * Real.exp (C₂ * s.im ^ 2)) := by ring

theorem GB.finset_prod {ι : Type} (S : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i ∈ S, GB (f i)) :
    GB (fun s => ∏ i ∈ S, f i s) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro a b
    exact ⟨1, 0, zero_le_one, le_rfl, fun s _ _ => by simp⟩
  | insert i S hi ih =>
    have h := (hf i (Finset.mem_insert_self i S)).mul (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
    intro a b
    obtain ⟨B, C, hB, hC, hh⟩ := h a b
    refine ⟨B, C, hB, hC, fun s hsa hsb => ?_⟩
    have := hh s hsa hsb
    simp only at this ⊢
    rw [Finset.prod_insert hi]
    exact this

theorem gb_of_norm_le {f : ℂ → ℂ} (h : ∀ a b : ℝ, ∃ M : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ M) : GB f := by
  intro a b
  obtain ⟨M, hM⟩ := h a b
  refine ⟨max M 0, 0, le_max_right _ _, le_rfl, fun s hsa hsb => ?_⟩
  simpa using (hM s hsa hsb).trans (le_max_left M 0)

theorem GB.shift {f : ℂ → ℂ} (hf : GB f) (μ : ℂ) : GB (fun s => f (s + μ)) := by
  intro a b
  obtain ⟨B, C, hB, hC, h⟩ := hf (a + μ.re) (b + μ.re)
  refine ⟨B * Real.exp (2 * C * μ.im ^ 2), 2 * C, by positivity, by positivity, fun s hsa hsb => ?_⟩
  have h1 := h (s + μ) (by simp; linarith) (by simp; linarith)
  refine h1.trans ?_
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
  have : (s + μ).im = s.im + μ.im := by simp
  rw [this]
  nlinarith [sq_nonneg (s.im - μ.im)]

theorem abs_le_one_add_sq (t : ℝ) : |t| ≤ 1 + t ^ 2 := by
  rcases le_or_gt |t| 1 with h | h
  · nlinarith [sq_nonneg t]
  · have : |t| ≤ |t| ^ 2 := by nlinarith
    rw [sq_abs] at this; linarith

theorem isCompact_rect (a b : ℝ) : IsCompact (Set.Icc a b ×ℂ Set.Icc (-2 : ℝ) 2) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.reProdIm isClosed_Icc)
    ((Metric.isBounded_Icc a b).reProdIm (Metric.isBounded_Icc _ _))

theorem gb_of_norm_le_exp {f : ℂ → ℂ} (hf : Continuous f)
    (h : ∀ a b : ℝ, ∃ M c : ℝ, 0 ≤ M ∧ 0 ≤ c ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 2 ≤ |s.im| → ‖f s‖ ≤ M * Real.exp (c * |s.im|)) : GB f := by
  intro a b
  obtain ⟨M, c, hM, hc, hh⟩ := h a b
  obtain ⟨B₀, hB₀⟩ := (isCompact_rect a b).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max B₀ (M * Real.exp c), c, le_max_of_le_right (by positivity), hc, fun s hsa hsb => ?_⟩
  have hexp1 : 1 ≤ Real.exp (c * s.im ^ 2) := Real.one_le_exp (by positivity)
  rcases le_or_gt 2 |s.im| with hbig | hsmall
  · refine (hh s hsa hsb hbig).trans ?_
    have hle : M * Real.exp (c * |s.im|) ≤ M * Real.exp c * Real.exp (c * s.im ^ 2) := by
      rw [mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM
      have := abs_le_one_add_sq s.im
      nlinarith
    exact hle.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
  · have hmem : s ∈ (Set.Icc a b ×ℂ Set.Icc (-2 : ℝ) 2) := by
      refine ⟨⟨hsa, hsb⟩, ?_⟩
      have := abs_lt.mp hsmall
      exact ⟨this.1.le, this.2.le⟩
    have h0 := hB₀ s hmem
    have hB₀0 : 0 ≤ B₀ := (norm_nonneg _).trans h0
    calc ‖f s‖ ≤ B₀ := h0
      _ ≤ max B₀ (M * Real.exp c) := le_max_left _ _
      _ = max B₀ (M * Real.exp c) * 1 := (mul_one _).symm
      _ ≤ max B₀ (M * Real.exp c) * Real.exp (c * s.im ^ 2) :=
          mul_le_mul_of_nonneg_left hexp1 (hB₀0.trans (le_max_left _ _))

theorem gb_Gammaℝ_inv : GB (fun s => (Gammaℝ s)⁻¹) := by
  refine gb_of_norm_le_exp differentiable_Gammaℝ_inv.continuous fun a b => ?_
  obtain ⟨B, hB, hΓ⟩ := norm_inv_Gamma_le (a / 2) (b / 2)
  set P : ℝ := Real.pi ^ ((|a| + |b|) / 2) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg Real.pi_pos.le _
  refine ⟨P * B, Real.pi / 2, by positivity, by positivity, fun s hsa hsb hsi => ?_⟩
  have hs2 : (s / 2).re = s.re / 2 := by simp
  have hs2i : (s / 2).im = s.im / 2 := by simp
  have h1 : a / 2 ≤ (s / 2).re := by rw [hs2]; linarith
  have h2 : (s / 2).re ≤ b / 2 := by rw [hs2]; linarith
  have h3 : 1 ≤ |(s / 2).im| := by rw [hs2i, abs_div, abs_two]; linarith
  have hΓs := hΓ (s / 2) h1 h2 h3
  rw [hs2i, abs_div, abs_two] at hΓs
  rw [Gammaℝ_def, mul_inv, norm_mul, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, ← Real.rpow_neg Real.pi_pos.le]
  have hexp : (-(-s / 2)).re ≤ (|a| + |b|) / 2 := by
    have : (-(-s / 2)).re = s.re / 2 := by simp [neg_div]
    rw [this]
    linarith [le_abs_self b, abs_nonneg a]
  have hπ1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hpow : Real.pi ^ (-(-s / 2)).re ≤ P := Real.rpow_le_rpow_of_exponent_le hπ1 hexp
  calc Real.pi ^ (-(-s / 2)).re * ‖(Gamma (s / 2))⁻¹‖ ≤ P * (B * Real.exp (Real.pi * (|s.im| / 2))) :=
        mul_le_mul hpow hΓs (norm_nonneg _) hP0
    _ = P * B * Real.exp (Real.pi / 2 * |s.im|) := by ring_nf

theorem gb_Gammaℂ_inv : GB (fun s => (Gammaℂ s)⁻¹) := by
  have : (fun s : ℂ => (Gammaℂ s)⁻¹) = fun s => (Gammaℝ s)⁻¹ * (Gammaℝ (s + 1))⁻¹ := by
    funext s; rw [← Gammaℝ_mul_Gammaℝ_add_one, mul_inv]
  rw [this]
  exact gb_Gammaℝ_inv.mul (gb_Gammaℝ_inv.shift 1)

section euler
variable {K : Type} [Field K] [NumberField K]

theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

def nC (v : HeightOneSpectrum (𝓞 K)) : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)

theorem nC_pos (v : HeightOneSpectrum (𝓞 K)) : 0 < Ideal.absNorm v.asIdeal :=
  lt_of_lt_of_le (by norm_num) (two_le_absNorm v)

theorem norm_nC_cpow_neg (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    ‖nC v ^ (-s)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
  unfold nC
  rw [Complex.norm_natCast_cpow_of_pos (nC_pos v) (-s), Complex.neg_re]

theorem one_le_nR (v : HeightOneSpectrum (𝓞 K)) : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
  have := two_le_absNorm v
  exact_mod_cast (by omega : 1 ≤ Ideal.absNorm v.asIdeal)

theorem norm_nC_cpow_neg_le_half {s : ℂ} (hs : 1 ≤ s.re) (v : HeightOneSpectrum (𝓞 K)) :
    ‖nC v ^ (-s)‖ ≤ 1 / 2 := by
  rw [norm_nC_cpow_neg]
  have h2 : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast two_le_absNorm v
  calc (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (one_le_nR v) (by linarith)
    _ ≤ (2 : ℝ) ^ (-(1 : ℝ)) := by
        rw [Real.rpow_neg (by positivity), Real.rpow_neg (by norm_num), Real.rpow_one, Real.rpow_one]
        exact inv_anti₀ (by norm_num) h2
    _ = 1 / 2 := by rw [Real.rpow_neg (by norm_num), Real.rpow_one, one_div]

theorem norm_nC_cpow_neg_le {s : ℂ} (hs : -1 / 2 ≤ s.re) (v : HeightOneSpectrum (𝓞 K)) :
    ‖nC v ^ (-s)‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ) := by
  rw [norm_nC_cpow_neg]
  exact Real.rpow_le_rpow_of_exponent_le (one_le_nR v) (by linarith)

open scoped Classical in

def coef (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0

open scoped Classical in

def coefD (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if IsUnramifiedCharAt χ v then (((χ (uniformizerIdele K v))⁻¹ : ℂˣ) : ℂ) else 0

theorem norm_coef_le_one {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 K) K χ)
    (v : HeightOneSpectrum (𝓞 K)) : ‖coef χ v‖ ≤ 1 := by
  unfold coef; split_ifs
  · exact (hχu _).le
  · simp

theorem norm_coefD_le_one {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 K) K χ)
    (v : HeightOneSpectrum (𝓞 K)) : ‖coefD χ v‖ ≤ 1 := by
  unfold coefD; split_ifs
  · have h := hχu (uniformizerIdele K v)
    rw [Units.val_inv_eq_inv_val, norm_inv, h, inv_one]
  · simp

def corr (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ :=
  ∏ v ∈ T, (1 - coef χ v * nC v ^ (-s))

theorem differentiable_corr (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    Differentiable ℂ (corr χ T) := by
  unfold corr
  refine Differentiable.fun_finsetProd fun v _ => ?_
  refine (differentiable_const _).sub ((differentiable_const _).mul ?_)
  refine Differentiable.const_cpow differentiable_neg (Or.inl ?_)
  unfold nC
  exact_mod_cast (nC_pos v).ne'

def PT (T : Finset (HeightOneSpectrum (𝓞 K))) : ℝ :=
  ∏ v ∈ T, (1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ))

theorem PT_pos (T : Finset (HeightOneSpectrum (𝓞 K))) : 0 < PT (K := K) T := by
  unfold PT
  exact Finset.prod_pos fun v _ => by positivity

theorem norm_corr_le {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 K) K χ)
    (T : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : -1 / 2 ≤ s.re) :
    ‖corr χ T s‖ ≤ PT (K := K) T := by
  unfold corr PT
  refine (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => ?_)
  calc ‖(1 : ℂ) - coef χ v * nC v ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖coef χ v * nC v ^ (-s)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 * (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ) := by
        rw [norm_one, norm_mul]
        gcongr
        · exact norm_coef_le_one hχu v
        · exact norm_nC_cpow_neg_le hs v
    _ = 1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ) := by rw [one_mul]

theorem norm_term_le_half {c : HeightOneSpectrum (𝓞 K) → ℂ} (hc : ∀ v, ‖c v‖ ≤ 1) {s : ℂ}
    (hs : 1 ≤ s.re) (v : HeightOneSpectrum (𝓞 K)) : ‖c v * nC v ^ (-s)‖ ≤ 1 / 2 := by
  rw [norm_mul]
  calc ‖c v‖ * ‖nC v ^ (-s)‖ ≤ 1 * (1 / 2) :=
        mul_le_mul (hc v) (norm_nC_cpow_neg_le_half hs v) (norm_nonneg _) zero_le_one
    _ = 1 / 2 := one_mul _

theorem one_sub_term_ne_zero {c : HeightOneSpectrum (𝓞 K) → ℂ} (hc : ∀ v, ‖c v‖ ≤ 1) {s : ℂ}
    (hs : 1 ≤ s.re) (v : HeightOneSpectrum (𝓞 K)) : (1 : ℂ) - c v * nC v ^ (-s) ≠ 0 := by
  intro h
  rw [sub_eq_zero] at h
  have := norm_term_le_half hc hs v
  rw [← h, norm_one] at this
  norm_num at this

theorem summable_norm_term {c : HeightOneSpectrum (𝓞 K) → ℂ} (hc : ∀ v, ‖c v‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) : Summable fun v : HeightOneSpectrum (𝓞 K) => ‖c v * nC v ^ (-s)‖ := by
  refine Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_)
    (NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K hs)
  rw [norm_mul, ← norm_nC_cpow_neg]
  calc ‖c v‖ * ‖nC v ^ (-s)‖ ≤ 1 * ‖nC v ^ (-s)‖ :=
        mul_le_mul_of_nonneg_right (hc v) (norm_nonneg _)
    _ = ‖nC v ^ (-s)‖ := one_mul _

theorem hasProd_subtype {c : HeightOneSpectrum (𝓞 K) → ℂ} (hc : ∀ v, ‖c v‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) (S : Set (HeightOneSpectrum (𝓞 K))) :
    HasProd (fun v : S => (1 - c v.1 * nC v.1 ^ (-s))⁻¹)
      (cexp (∑' v : S, -log (1 - c v.1 * nC v.1 ^ (-s)))) := by
  have hne : ∀ v : HeightOneSpectrum (𝓞 K), (1 : ℂ) - c v * nC v ^ (-s) ≠ 0 :=
    one_sub_term_ne_zero hc hs.le
  have hsub : Summable fun v : S => c v.1 * nC v.1 ^ (-s) :=
    ((summable_norm_term hc hs).subtype S).of_norm
  have hg : Summable fun v : S => -log (1 - c v.1 * nC v.1 ^ (-s)) := hsub.clog_one_sub.neg
  have H := hg.hasSum.cexp
  have hcongr : (cexp ∘ fun v : S => -log (1 - c v.1 * nC v.1 ^ (-s))) =
      fun v => (1 - c v.1 * nC v.1 ^ (-s))⁻¹ := by
    funext v
    simp only [Function.comp_apply, exp_neg, exp_log (hne v.1)]
  rw [hcongr] at H
  exact H

theorem tprod_compl_eq {c : HeightOneSpectrum (𝓞 K) → ℂ} (hc : ∀ v, ‖c v‖ ≤ 1) {s : ℂ}
    (hs : 1 < s.re) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, (1 - c v.1 * nC v.1 ^ (-s))⁻¹) =
      (∏ v ∈ T, (1 - c v * nC v ^ (-s))) *
        ∏' v : HeightOneSpectrum (𝓞 K), (1 - c v * nC v ^ (-s))⁻¹ := by
  set f : HeightOneSpectrum (𝓞 K) → ℂ := fun v => (1 - c v * nC v ^ (-s))⁻¹ with hf
  set E : ℂ := cexp (∑' v : ((↑T : Set (HeightOneSpectrum (𝓞 K)))ᶜ : Set (HeightOneSpectrum (𝓞 K))),
    -log (1 - c v.1 * nC v.1 ^ (-s))) with hE
  have hP : HasProd (f ∘ (↑) : ((↑T : Set (HeightOneSpectrum (𝓞 K)))ᶜ : Set _) → ℂ) E :=
    hasProd_subtype hc hs _
  have hEq : (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, (1 - c v.1 * nC v.1 ^ (-s))⁻¹) = E :=
    hP.tprod_eq
  have hG : HasProd (f ∘ (↑) : (↑T : Set (HeightOneSpectrum (𝓞 K))) → ℂ) (∏ v ∈ T, f v) :=
    Finset.hasProd T _
  have hall : HasProd f ((∏ v ∈ T, f v) * E) := hG.mul_isCompl isCompl_compl hP
  have htot : (∏' v : HeightOneSpectrum (𝓞 K), f v) = (∏ v ∈ T, f v) * E := hall.tprod_eq
  have hne : (∏ v ∈ T, (1 - c v * nC v ^ (-s))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun v _ => one_sub_term_ne_zero hc hs.le v
  have hinv : (∏ v ∈ T, f v) = (∏ v ∈ T, (1 - c v * nC v ^ (-s)))⁻¹ := by
    simp only [hf]; exact Finset.prod_inv_distrib _
  rw [hEq]
  show E = (∏ v ∈ T, (1 - c v * nC v ^ (-s))) * ∏' v : HeightOneSpectrum (𝓞 K), f v
  rw [htot, hinv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

end euler

section datum
open scoped Classical
variable {K : Type} [Field K] [NumberField K]
variable (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
  (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
  (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)

theorem euler_eval (v : HeightOneSpectrum (𝓞 K)) (q : ℂ) :
    ((heckeDatum K χ uR aR uC kC).euler v).eval q = 1 - coef χ v * q := by
  classical
  simp only [heckeDatum, coef]
  split_ifs <;> simp

theorem dual_eval (v : HeightOneSpectrum (𝓞 K)) (q : ℂ) :
    ((heckeDatum K χ uR aR uC kC).dual v).eval q = 1 - coefD χ v * q := by
  classical
  simp only [heckeDatum, coefD]
  split_ifs <;> simp

theorem LFun_eq (s : ℂ) :
    (heckeDatum K χ uR aR uC kC).LFun s =
      ∏' v : HeightOneSpectrum (𝓞 K), (1 - coef χ v * nC v ^ (-s))⁻¹ := by
  unfold LDatum.LFun
  refine tprod_congr fun v => ?_
  rw [euler_eval]
  rfl

theorem LFunDual_eq (s : ℂ) :
    (heckeDatum K χ uR aR uC kC).LFunDual s =
      ∏' v : HeightOneSpectrum (𝓞 K), (1 - coefD χ v * nC v ^ (-s))⁻¹ := by
  unfold LDatum.LFunDual
  refine tprod_congr fun v => ?_
  rw [dual_eval]
  rfl

def μR (w : {w : InfinitePlace K // w.IsReal}) : ℂ := uR w.1 w.2 + signShift (aR w.1 w.2)

def μC (w : {w : InfinitePlace K // w.IsComplex}) : ℂ := uC w.1 w.2 + ((kC w.1 w.2).natAbs : ℂ) / 2

theorem prod_map_sum_singleton {ι : Type} (S : Finset ι) (x : ι → ℂ) (g : ℂ → ℂ) :
    ((∑ i ∈ S, ({x i} : Multiset ℂ)).map g).prod = ∏ i ∈ S, g (x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, Multiset.map_add,
      Multiset.prod_add, ih, Multiset.map_singleton, Multiset.prod_singleton]

theorem archFactor_eq (s : ℂ) :
    (heckeDatum K χ uR aR uC kC).archFactor s =
      (∏ w : {w : InfinitePlace K // w.IsReal}, Gammaℝ (s + μR uR aR w)) *
        ∏ w : {w : InfinitePlace K // w.IsComplex}, Gammaℂ (s + μC uC kC w) := by
  simp only [LDatum.archFactor, heckeDatum]
  rw [prod_map_sum_singleton, prod_map_sum_singleton]
  rfl

theorem archFactorDual_eq (s : ℂ) :
    (heckeDatum K χ uR aR uC kC).archFactorDual s =
      (∏ w : {w : InfinitePlace K // w.IsReal}, Gammaℝ (s + (-uR w.1 w.2 + signShift (aR w.1 w.2)))) *
        ∏ w : {w : InfinitePlace K // w.IsComplex},
          Gammaℂ (s + (-uC w.1 w.2 + ((-kC w.1 w.2).natAbs : ℂ) / 2)) := by
  simp only [LDatum.archFactorDual, heckeDatum]
  rw [prod_map_sum_singleton, prod_map_sum_singleton]

def invArch (s : ℂ) : ℂ :=
  (∏ w : {w : InfinitePlace K // w.IsReal}, (Gammaℝ (s + μR uR aR w))⁻¹) *
    ∏ w : {w : InfinitePlace K // w.IsComplex}, (Gammaℂ (s + μC uC kC w))⁻¹

theorem differentiable_invArch : Differentiable ℂ (invArch uR aR uC kC) := by
  unfold invArch
  refine (Differentiable.fun_finsetProd fun w _ => ?_).mul (Differentiable.fun_finsetProd fun w _ => ?_)
  · exact differentiable_Gammaℝ_inv.comp (differentiable_id.add_const _)
  · exact differentiable_Gammaℂ_inv.comp (differentiable_id.add_const _)

theorem archFactor_mul_invArch {s : ℂ}
    (hR : ∀ w : {w : InfinitePlace K // w.IsReal}, Gammaℝ (s + μR uR aR w) ≠ 0)
    (hC : ∀ w : {w : InfinitePlace K // w.IsComplex}, Gammaℂ (s + μC uC kC w) ≠ 0) :
    (heckeDatum K χ uR aR uC kC).archFactor s * invArch uR aR uC kC s = 1 := by
  rw [archFactor_eq, invArch, mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    Finset.prod_eq_one fun w _ => mul_inv_cancel₀ (hR w), Finset.prod_eq_one fun w _ => mul_inv_cancel₀ (hC w),
    one_mul]

end datum

theorem eq_of_agree_of_one_lt_re (L G : ℂ → ℂ) (hL : Differentiable ℂ L) (hG : Differentiable ℂ G)
    (h : ∀ s : ℂ, 1 < s.re → L s = G s) : L = G := by
  have hLa : AnalyticOnNhd ℂ L univ := hL.differentiableOn.analyticOnNhd isOpen_univ
  have hGa : AnalyticOnNhd ℂ G univ := hG.differentiableOn.analyticOnNhd isOpen_univ
  have hVopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have hev : L =ᶠ[𝓝 (2 : ℂ)] G :=
    Filter.eventuallyEq_of_mem (hVopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)) fun z hz => h z hz
  exact hLa.eq_of_eventuallyEq hGa hev

section main
open scoped Classical
variable {K : Type} [Field K] [NumberField K]

theorem gb_corr {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχu : IsUnitaryChar (𝓞 K) K χ)
    (T : Finset (HeightOneSpectrum (𝓞 K))) : GB (corr χ T) := by
  refine gb_of_norm_le fun a b => ⟨∏ v ∈ T, (1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (|a|)), fun s hsa hsb => ?_⟩
  unfold corr
  refine (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => ?_)
  calc ‖(1 : ℂ) - coef χ v * nC v ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖coef χ v * nC v ^ (-s)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 * (Ideal.absNorm v.asIdeal : ℝ) ^ (|a|) := by
        rw [norm_one, norm_mul]
        gcongr
        · exact norm_coef_le_one hχu v
        · rw [norm_nC_cpow_neg]
          exact Real.rpow_le_rpow_of_exponent_le (one_le_nR v) (by linarith [neg_abs_le a])
    _ = 1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (|a|) := by rw [one_mul]

theorem gb_invArch (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ) :
    GB (invArch uR aR uC kC) := by
  unfold invArch
  exact (GB.finset_prod _ fun w _ => gb_Gammaℝ_inv.shift (μR uR aR w)).mul
    (GB.finset_prod _ fun w _ => gb_Gammaℂ_inv.shift (μC uC kC w))

theorem main (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 K) K χ) (hχc : Continuous χ)
    (hχu : IsUnitaryChar (𝓞 K) K χ) (hχ1 : ∃ x ∈ normOneIdeles K, χ x ≠ 1)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (L : ℂ → ℂ) (hL : Differentiable ℂ L)
    (hLT : ∀ s : ℂ, 1 < s.re →
      L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
    (a b : ℝ) :
    ∃ B C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖L s‖ ≤ B * Real.exp (C * s.im ^ 2) := by

  have hRex := fun (w : InfinitePlace K) (hw : w.IsReal) =>
    LanglandsTunnell.Converse.exists_isArchCompAt_of_isReal K χ hχc w hw
  have hCex := fun (w : InfinitePlace K) (hw : w.IsComplex) =>
    LanglandsTunnell.Converse.exists_isArchCompAt_of_isComplex K χ hχc w hw
  choose uR aR hR using hRex
  choose uC kC hC using hCex
  have hadm : IsAdmissibleTwist K χ := ⟨hχ, hχc, hχu⟩
  obtain ⟨hWF, hConv, hNpos, Λ, Λd, hΛ, hΛd, hBΛ, hBΛd, hΛeq, hΛdeq, hFE⟩ :=
    LanglandsTunnell.HeckeTate.isNicePinned_heckeDatum K χ hadm hχ1 uR aR uC kC hR hC
  set D := heckeDatum K χ uR aR uC kC with hD
  have habs : D.abscissa = 1 := rfl

  obtain ⟨-, -, hWR, hWC, -, -⟩ := hWF
  have hμR : ∀ w : {w : InfinitePlace K // w.IsReal}, -1 ≤ (μR uR aR w).re := fun w => by
    have hmem : μR uR aR w ∈ D.gammaR := by
      show μR uR aR w ∈ (Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).sum
        fun w => ({uR w.1 w.2 + signShift (aR w.1 w.2)} : Multiset ℂ)
      exact Multiset.mem_sum.mpr ⟨w, Finset.mem_univ w, Multiset.mem_singleton_self _⟩
    have := hWR _ hmem
    rw [habs] at this; linarith
  have hμC : ∀ w : {w : InfinitePlace K // w.IsComplex}, -1 ≤ (μC uC kC w).re := fun w => by
    have hmem : μC uC kC w ∈ D.gammaC := by
      show μC uC kC w ∈ (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).sum
        fun w => ({uC w.1 w.2 + ((kC w.1 w.2).natAbs : ℂ) / 2} : Multiset ℂ)
      exact Multiset.mem_sum.mpr ⟨w, Finset.mem_univ w, Multiset.mem_singleton_self _⟩
    have := hWC _ hmem
    rw [habs] at this; linarith

  have hcoef : ∀ v, ‖coef χ v‖ ≤ 1 := norm_coef_le_one hχu
  have hLid : L = fun z => Λ z * invArch uR aR uC kC z * corr χ T z := by
    refine eq_of_agree_of_one_lt_re L _ hL
      ((hΛ.mul (differentiable_invArch uR aR uC kC)).mul (differentiable_corr χ T)) fun z hz => ?_
    have h1 : Λ z = D.archFactor z * D.LFun z := by
      have := hΛeq z (by rw [habs]; exact hz); simpa using this
    have h2 : D.LFun z = ∏' v : HeightOneSpectrum (𝓞 K), (1 - coef χ v * nC v ^ (-z))⁻¹ := LFun_eq χ uR aR uC kC z
    have h3 : L z = corr χ T z * ∏' v : HeightOneSpectrum (𝓞 K), (1 - coef χ v * nC v ^ (-z))⁻¹ := by
      rw [hLT z hz]; exact tprod_compl_eq hcoef hz T
    have hΓR : ∀ w : {w : InfinitePlace K // w.IsReal}, Gammaℝ (z + μR uR aR w) ≠ 0 := fun w =>
      Gammaℝ_ne_zero_of_re_pos (by have := hμR w; simp only [add_re]; linarith)
    have hΓC : ∀ w : {w : InfinitePlace K // w.IsComplex}, Gammaℂ (z + μC uC kC w) ≠ 0 := fun w =>
      Gammaℂ_ne_zero_of_re_pos (by have := hμC w; simp only [add_re]; linarith)
    have h4 := archFactor_mul_invArch χ uR aR uC kC hΓR hΓC
    show L z = Λ z * invArch uR aR uC kC z * corr χ T z
    rw [h3, h1, h2]
    calc corr χ T z * ∏' v : HeightOneSpectrum (𝓞 K), (1 - coef χ v * nC v ^ (-z))⁻¹
        = (D.archFactor z * invArch uR aR uC kC z) *
            (∏' v : HeightOneSpectrum (𝓞 K), (1 - coef χ v * nC v ^ (-z))⁻¹) * corr χ T z := by
          rw [h4, one_mul, mul_comm]
      _ = _ := by ring

  have hGΛ : GB Λ := gb_of_norm_le fun a' b' => hBΛ a' b'
  have hG : GB (fun z => Λ z * invArch uR aR uC kC z * corr χ T z) :=
    (hGΛ.mul (gb_invArch uR aR uC kC)).mul (gb_corr hχu T)
  obtain ⟨B, C, -, -, hBC⟩ := hG a b
  refine ⟨B, C, fun s hsa hsb => ?_⟩
  rw [hLid]
  exact hBC s hsa hsb

end main

end R4G2a

end

open NumberField IsDedekindDomain AutomorphicForm NumberField.TateGlobal in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 K) K χ) (hχc : Continuous χ)
    (hχu : IsUnitaryChar (𝓞 K) K χ) (hχ1 : ∃ x ∈ normOneIdeles K, χ x ≠ 1)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (L : ℂ → ℂ) (hL : Differentiable ℂ L)
    (hLT : ∀ s : ℂ, 1 < s.re →
      L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
    (a b : ℝ) :
    ∃ B C : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖L s‖ ≤ B * Real.exp (C * s.im ^ 2) :=
  R4G2a.main χ hχ hχc hχu hχ1 T L hL hLT a b

end S_NumberField_TateGlobal_exists_norm_partialEulerProduct_continuation_le_mul_exp_mul_im_sq
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_norm_partialEulerProduct_continuation_le_mul_exp_mul_im_sq (solution)
