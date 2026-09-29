-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_integral_twoSheet_hermiteBracket_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/bff4d585-61de-5d99-877a-8cfd5d13a82e

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_iotaGL_diagUnitGL2_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_archZeta30_one_eq_mul_integral_quasiChar_of_isArchCompAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.MvPolynomial
import Theorems.Thm_LanglandsTunnell_integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv
import Theorems.Thm_LanglandsTunnell_CubicInduction_godementInner3_eq_mul_exp_of_blockPoly_mul_colLinear_gaussian3
import Theorems.Thm_LanglandsTunnell_CubicInduction_godementInner3_eq_mul_exp_of_blockPoly_mul_colHarmonic_gaussian3
import Theorems.Thm_LanglandsTunnell_RankinSelberg_integral_matrixTwo_eq_setIntegral_iwasawaInv_unconditional
import Theorems.Thm_LanglandsTunnell_integral_exp_neg_pi_sq_div_sq_mul_affine_pow_mul_cexp_eq_mul_hermiteMoment
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_xMoment_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_integral_twoSheet_hermiteBracket_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
p2m_attr_erase "simp" "LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NumberField AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell LanglandsTunnell.CubicInduction MeasureTheory

namespace Ws23Z0

open LanglandsTunnell.Converse.ArchR Set

section Torus

variable (a : ℚ) (ha : a ≠ 0) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
  (hpsiInf : ∀ x : InfiniteAdeleRing ℚ, psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
  {P : RealArchParam} (D : ArchDatumR P) (u₃ : ℂ) (a₃ : ZMod 2)
  (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ) (hS : S ∈ polyGauss3)

noncomputable def Phi (y : ℝ) : ℂ := jacquetVector3 D u₃ a₃ ((a : ℝ) * y) psiInf S 1

theorem Phi_eq_integral (y : ℝ) :
    Phi a psiInf D u₃ a₃ S y = ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ ((a : ℝ) * y) psiInf S 1 e := by
  rw [Phi, jacquetVector3_eq, AutomorphicForm.StandardKernel.realMat_one, Matrix.det_one]
  have hq1 : quasiChar (u₃ + 1) a₃ (1 : ℝ) = 1 := by
    unfold quasiChar; rw [abs_one, Complex.ofReal_one, Complex.one_cpow, one_mul]; split_ifs <;> simp
  rw [hq1, one_mul]

noncomputable def c₀ (P : RealArchParam) : ℝ :=
  (((P.twist 0 0).gammaR.map (fun z => ‖z‖)).sum + ((P.twist 0 0).gammaC.map (fun z => ‖z‖)).sum) +
    (((P.twist 0 1).gammaR.map (fun z => ‖z‖)).sum + ((P.twist 0 1).gammaC.map (fun z => ‖z‖)).sum) + 1

theorem neg_re_le_sum_of_mem {M : Multiset ℂ} {μ : ℂ} (h : μ ∈ M) : -μ.re ≤ (M.map (fun z => ‖z‖)).sum := by
  have h1 : -μ.re ≤ ‖μ‖ := by have := Complex.abs_re_le_norm μ; have := neg_abs_le μ.re; linarith
  have h2 : ‖μ‖ ≤ (M.map (fun z => ‖z‖)).sum :=
    Multiset.single_le_sum (fun x hx => by obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 hx; exact norm_nonneg z) _
      (Multiset.mem_map_of_mem _ h)
  linarith

theorem sum_norm_nonneg (M : Multiset ℂ) : 0 ≤ (M.map (fun z => ‖z‖)).sum :=
  Multiset.sum_nonneg fun x hx => by obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 hx; exact norm_nonneg z

theorem hc₀ (P : RealArchParam) : ∀ b : ZMod 2,
    (∀ μ ∈ (P.twist 0 b).gammaR, -μ.re < c₀ P) ∧ (∀ ν ∈ (P.twist 0 b).gammaC, -ν.re < c₀ P) := by
  intro b
  have h00 := sum_norm_nonneg (P.twist 0 0).gammaR; have h01 := sum_norm_nonneg (P.twist 0 0).gammaC
  have h10 := sum_norm_nonneg (P.twist 0 1).gammaR; have h11 := sum_norm_nonneg (P.twist 0 1).gammaC
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b with rfl | rfl <;>
  · refine ⟨fun μ hμ => ?_, fun ν hν => ?_⟩
    · have := neg_re_le_sum_of_mem hμ; simp only [c₀]; linarith
    · have := neg_re_le_sum_of_mem hν; simp only [c₀]; linarith

noncomputable def q₀ (P : RealArchParam) (u₃ : ℂ) : ℝ := max (c₀ P) (-u₃.re)

include ha hpsiInf hS in

theorem aestronglyMeasurable_Phi : AEStronglyMeasurable (Phi a psiInf D u₃ a₃ S) volume := by
  obtain ⟨-, hjm, -, -⟩ := LanglandsTunnell.CubicInduction.exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod
    (P := P) u₃ a₃ a psiInf hpsiInf ha D S hS (c₀ P) (hc₀ P)
  have hV : AEStronglyMeasurable (fun A : ℝ => ∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ A psiInf S 1 e) volume :=
    (hjm 1).integral_prod_right'
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hqmp : Measure.QuasiMeasurePreserving (fun y : ℝ => (a : ℝ) * y) volume volume := by
    refine ⟨measurable_const_mul _, ?_⟩
    rw [Real.map_volume_mul_left ha']
    exact Measure.smul_absolutelyContinuous
  have h := hV.comp_quasiMeasurePreserving hqmp
  refine h.congr (ae_of_all _ fun y => ?_)
  simp only [Function.comp, Phi_eq_integral]

include ha hpsiInf hS in

theorem exists_bound_Phi (q : ℝ) (hq : q₀ P u₃ < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, y ≠ 0 → ‖Phi a psiInf D u₃ a₃ S y‖ ≤ C * |y| ^ (1 - q) := by
  obtain ⟨hmaj, -, -, -⟩ := LanglandsTunnell.CubicInduction.exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod
    (P := P) u₃ a₃ a psiInf hpsiInf ha D S hS (c₀ P) (hc₀ P)
  obtain ⟨V, hV, F, hF, hbound⟩ := hmaj 1 q hq
  have h1 : (1 : GL (Fin 3) (InfiniteAdeleRing ℚ)) ∈ V := mem_of_mem_nhds hV
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  refine ⟨|(a : ℝ)| ^ (1 - q) * ∫ e, F e, ?_, fun y hy => ?_⟩
  · refine mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (integral_nonneg_of_ae (ae_of_all _ fun e => ?_))
    have := hbound 1 h1 1 one_ne_zero e
    have h0 : (0 : ℝ) ≤ |(1 : ℝ)| ^ (1 - q) * F e := le_trans (norm_nonneg _) this
    simpa using h0
  · have hA : (a : ℝ) * y ≠ 0 := mul_ne_zero ha' hy
    rw [Phi_eq_integral]
    calc ‖∫ e : Fin 2 → Fin 2 → ℝ, jacquetIntegrand3 D u₃ a₃ ((a : ℝ) * y) psiInf S 1 e‖
        ≤ ∫ e : Fin 2 → Fin 2 → ℝ, ‖jacquetIntegrand3 D u₃ a₃ ((a : ℝ) * y) psiInf S 1 e‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ e : Fin 2 → Fin 2 → ℝ, |(a : ℝ) * y| ^ (1 - q) * F e := by
          refine integral_mono_of_nonneg (ae_of_all _ fun e => norm_nonneg _) (hF.const_mul _) (ae_of_all _ fun e => ?_)
          exact hbound 1 h1 _ hA e
      _ = |(a : ℝ)| ^ (1 - q) * (∫ e, F e) * |y| ^ (1 - q) := by
          rw [integral_const_mul, abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]; ring

theorem measurable_charFactor (t s : ℂ) (e : ZMod 2) :
    Measurable fun y : ℝ => quasiChar t e y * ((|y| : ℝ) : ℂ) ^ (s - 1) * (((|y| : ℝ) : ℂ))⁻¹ := by
  have hsign : Measurable fun y : ℝ => (((SignType.sign y : SignType) : ℝ) : ℂ) := by
    have : (fun y : ℝ => (((SignType.sign y : SignType) : ℝ) : ℂ)) =
        fun y => if 0 < y then (1 : ℂ) else if y < 0 then -1 else 0 := by
      funext y; rw [sign_apply]; split_ifs <;> simp
    rw [this]
    exact Measurable.ite measurableSet_Ioi measurable_const
      (Measurable.ite measurableSet_Iio measurable_const measurable_const)
  have habs : Measurable fun y : ℝ => ((|y| : ℝ) : ℂ) := Complex.measurable_ofReal.comp measurable_abs
  unfold quasiChar
  refine (((habs.pow_const t).mul ?_).mul (habs.pow_const _)).mul habs.inv
  split_ifs
  · exact measurable_const
  · exact hsign

theorem norm_charFactor {y : ℝ} (hy : y ≠ 0) (s : ℂ) (e : ZMod 2) :
    ‖quasiChar 0 e y * ((|y| : ℝ) : ℂ) ^ (s - 1) * (((|y| : ℝ) : ℂ))⁻¹‖ = |y| ^ (s.re - 2) := by
  have hy' : 0 < |y| := abs_pos.2 hy
  have hq : ‖quasiChar 0 e y‖ = 1 := by
    unfold quasiChar
    rw [Complex.cpow_zero, one_mul]
    split_ifs
    · simp
    · rcases lt_or_gt_of_ne hy with h | h
      · rw [sign_neg h]; simp
      · rw [sign_pos h]; simp
  rw [norm_mul, norm_mul, hq, one_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hy', Complex.sub_re, Complex.one_re,
    ← Real.rpow_neg_one, ← Real.rpow_add hy']
  ring_nf

noncomputable def Lf (s : ℂ) (e : ZMod 2) (y : ℝ) : ℂ :=
  Phi a psiInf D u₃ a₃ S y * quasiChar 0 e y * ((|y| : ℝ) : ℂ) ^ (s - 1) * (((|y| : ℝ) : ℂ))⁻¹

include ha hpsiInf hS in
theorem aestronglyMeasurable_Lf (s : ℂ) (e : ZMod 2) : AEStronglyMeasurable (Lf a psiInf D u₃ a₃ S s e) volume := by
  have h := (aestronglyMeasurable_Phi a ha psiInf hpsiInf D u₃ a₃ S hS).mul (measurable_charFactor 0 s e).aestronglyMeasurable
  refine h.congr (ae_of_all _ fun y => ?_)
  simp only [Lf, Pi.mul_apply]; ring

include ha hpsiInf hS in

theorem integrableOn_Lf_Ioi (s : ℂ) (e : ZMod 2) (hs : q₀ P u₃ < s.re) :
    IntegrableOn (Lf a psiInf D u₃ a₃ S s e) (Ioi 0) := by

  obtain ⟨C₁, hC₁, hb₁⟩ := exists_bound_Phi a ha psiInf hpsiInf D u₃ a₃ S hS ((q₀ P u₃ + s.re) / 2) (by linarith)
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_bound_Phi a ha psiInf hpsiInf D u₃ a₃ S hS (s.re + 1) (by linarith)
  have hmeas := aestronglyMeasurable_Lf a ha psiInf hpsiInf D u₃ a₃ S hS s e
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  ·
    have hp : -1 < 1 - (q₀ P u₃ + s.re) / 2 + (s.re - 2) := by linarith
    have hdom : IntegrableOn (fun y : ℝ => C₁ * y ^ (1 - (q₀ P u₃ + s.re) / 2 + (s.re - 2))) (Ioc 0 1) := by
      have h := (intervalIntegral.intervalIntegrable_rpow' hp (a := 0) (b := 1))
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
      exact h.const_mul C₁
    refine Integrable.mono' hdom hmeas.restrict ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun y hy => ?_))
    have hy0 : 0 < y := hy.1
    rw [Lf, mul_assoc, mul_assoc, norm_mul, ← mul_assoc (quasiChar 0 e y), norm_charFactor hy0.ne', Real.rpow_add hy0,
      abs_of_pos hy0]
    have := hb₁ y hy0.ne'
    rw [abs_of_pos hy0] at this
    have hpos : 0 ≤ y ^ (s.re - 2) := Real.rpow_nonneg hy0.le _
    calc ‖Phi a psiInf D u₃ a₃ S y‖ * y ^ (s.re - 2) ≤ C₁ * y ^ (1 - (q₀ P u₃ + s.re) / 2) * y ^ (s.re - 2) :=
          mul_le_mul_of_nonneg_right this hpos
      _ = C₁ * (y ^ (1 - (q₀ P u₃ + s.re) / 2) * y ^ (s.re - 2)) := by ring
  ·
    have hp : 1 - (s.re + 1) + (s.re - 2) < -1 := by linarith
    have hdom : IntegrableOn (fun y : ℝ => C₂ * y ^ (1 - (s.re + 1) + (s.re - 2))) (Ioi 1) :=
      ((integrableOn_Ioi_rpow_iff zero_lt_one).2 hp).const_mul C₂
    refine Integrable.mono' hdom hmeas.restrict ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun y (hy : 1 < y) => ?_))
    have hy0 : 0 < y := one_pos.trans hy
    rw [Lf, mul_assoc, mul_assoc, norm_mul, ← mul_assoc (quasiChar 0 e y), norm_charFactor hy0.ne', Real.rpow_add hy0,
      abs_of_pos hy0]
    have := hb₂ y hy0.ne'
    rw [abs_of_pos hy0] at this
    have hpos : 0 ≤ y ^ (s.re - 2) := Real.rpow_nonneg hy0.le _
    calc ‖Phi a psiInf D u₃ a₃ S y‖ * y ^ (s.re - 2) ≤ C₂ * y ^ (1 - (s.re + 1)) * y ^ (s.re - 2) :=
          mul_le_mul_of_nonneg_right this hpos
      _ = C₂ * (y ^ (1 - (s.re + 1)) * y ^ (s.re - 2)) := by ring

include ha hpsiInf hS in

theorem integrableOn_Lf_neg_Ioi (s : ℂ) (e : ZMod 2) (hs : q₀ P u₃ < s.re) :
    IntegrableOn (fun y : ℝ => Lf a psiInf D u₃ a₃ S s e (-y)) (Ioi 0) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_bound_Phi a ha psiInf hpsiInf D u₃ a₃ S hS ((q₀ P u₃ + s.re) / 2) (by linarith)
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_bound_Phi a ha psiInf hpsiInf D u₃ a₃ S hS (s.re + 1) (by linarith)
  have hmeas : AEStronglyMeasurable (fun y : ℝ => Lf a psiInf D u₃ a₃ S s e (-y)) volume :=
    (aestronglyMeasurable_Lf a ha psiInf hpsiInf D u₃ a₃ S hS s e).comp_quasiMeasurePreserving
      (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have hp : -1 < 1 - (q₀ P u₃ + s.re) / 2 + (s.re - 2) := by linarith
    have hdom : IntegrableOn (fun y : ℝ => C₁ * y ^ (1 - (q₀ P u₃ + s.re) / 2 + (s.re - 2))) (Ioc 0 1) := by
      have h := (intervalIntegral.intervalIntegrable_rpow' hp (a := 0) (b := 1))
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
      exact h.const_mul C₁
    refine Integrable.mono' hdom hmeas.restrict ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun y hy => ?_))
    have hy0 : 0 < y := hy.1
    have hny : -y ≠ 0 := by linarith
    rw [Lf, mul_assoc, mul_assoc, norm_mul, ← mul_assoc (quasiChar 0 e (-y)), norm_charFactor hny, Real.rpow_add hy0,
      abs_neg, abs_of_pos hy0]
    have := hb₁ (-y) hny
    rw [abs_neg, abs_of_pos hy0] at this
    have hpos : 0 ≤ y ^ (s.re - 2) := Real.rpow_nonneg hy0.le _
    calc ‖Phi a psiInf D u₃ a₃ S (-y)‖ * y ^ (s.re - 2) ≤ C₁ * y ^ (1 - (q₀ P u₃ + s.re) / 2) * y ^ (s.re - 2) :=
          mul_le_mul_of_nonneg_right this hpos
      _ = C₁ * (y ^ (1 - (q₀ P u₃ + s.re) / 2) * y ^ (s.re - 2)) := by ring
  · have hp : 1 - (s.re + 1) + (s.re - 2) < -1 := by linarith
    have hdom : IntegrableOn (fun y : ℝ => C₂ * y ^ (1 - (s.re + 1) + (s.re - 2))) (Ioi 1) :=
      ((integrableOn_Ioi_rpow_iff zero_lt_one).2 hp).const_mul C₂
    refine Integrable.mono' hdom hmeas.restrict ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun y (hy : 1 < y) => ?_))
    have hy0 : 0 < y := one_pos.trans hy
    have hny : -y ≠ 0 := by linarith
    rw [Lf, mul_assoc, mul_assoc, norm_mul, ← mul_assoc (quasiChar 0 e (-y)), norm_charFactor hny, Real.rpow_add hy0,
      abs_neg, abs_of_pos hy0]
    have := hb₂ (-y) hny
    rw [abs_neg, abs_of_pos hy0] at this
    have hpos : 0 ≤ y ^ (s.re - 2) := Real.rpow_nonneg hy0.le _
    calc ‖Phi a psiInf D u₃ a₃ S (-y)‖ * y ^ (s.re - 2) ≤ C₂ * y ^ (1 - (s.re + 1)) * y ^ (s.re - 2) :=
          mul_le_mul_of_nonneg_right this hpos
      _ = C₂ * (y ^ (1 - (s.re + 1)) * y ^ (s.re - 2)) := by ring

include ha hpsiInf hS in
theorem integrableOn_Lf_Iic (s : ℂ) (e : ZMod 2) (hs : q₀ P u₃ < s.re) :
    IntegrableOn (Lf a psiInf D u₃ a₃ S s e) (Iic 0) := by
  have h := integrableOn_Lf_neg_Ioi a ha psiInf hpsiInf D u₃ a₃ S hS s e hs
  have h' : IntegrableOn (Lf a psiInf D u₃ a₃ S s e) (Iio 0) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simpa only [Function.comp_def, neg_preimage, neg_Iio, neg_zero] using h
  exact h'.congr_set_ae Iio_ae_eq_Iic.symm

include ha hpsiInf hS in
theorem integrable_Lf (s : ℂ) (e : ZMod 2) (hs : q₀ P u₃ < s.re) : Integrable (Lf a psiInf D u₃ a₃ S s e) := by
  have h := (integrableOn_Lf_Iic a ha psiInf hpsiInf D u₃ a₃ S hS s e hs).union
    (integrableOn_Lf_Ioi a ha psiInf hpsiInf D u₃ a₃ S hS s e hs)
  rwa [Iic_union_Ioi, integrableOn_univ] at h

theorem quasiChar_zero_neg' {e : ZMod 2} {t : ℝ} (ht : 0 < t) : quasiChar 0 e (-t) = (-1 : ℂ) ^ e.val := by
  unfold quasiChar
  rw [Complex.cpow_zero, one_mul]
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) e with h | h <;> subst h
  · simp
  · rw [if_neg (by decide)]
    have hs : SignType.sign (-t) = -1 := by rw [Left.sign_neg, sign_pos ht]
    rw [hs]
    simp [show (1 : ZMod 2).val = 1 from rfl]

theorem quasiChar_zero_pos' {e : ZMod 2} {t : ℝ} (ht : 0 < t) : quasiChar 0 e t = 1 := by
  unfold quasiChar
  rw [Complex.cpow_zero, one_mul]
  split_ifs
  · rfl
  · rw [sign_pos ht]; simp

include ha hpsiInf hS in

theorem integral_Lf_eq (s : ℂ) (e : ZMod 2) (hs : q₀ P u₃ < s.re) :
    ∫ y : ℝ, Lf a psiInf D u₃ a₃ S s e y =
      ∫ y in Ioi (0 : ℝ), (Phi a psiInf D u₃ a₃ S y + (-1 : ℂ) ^ e.val * Phi a psiInf D u₃ a₃ S (-y)) *
        ((y : ℝ) : ℂ) ^ (s - 2) := by
  have hI := integrableOn_Lf_Ioi a ha psiInf hpsiInf D u₃ a₃ S hS s e hs
  have hIn := integrableOn_Lf_neg_Ioi a ha psiInf hpsiInf D u₃ a₃ S hS s e hs
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (integrableOn_Lf_Iic a ha psiInf hpsiInf D u₃ a₃ S hS s e hs) hI
  rw [← hsplit, ← neg_zero, ← integral_comp_neg_Ioi 0 (Lf a psiInf D u₃ a₃ S s e), neg_zero, ← integral_add hIn hI]
  refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) => ?_
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  have hpow : ((|y| : ℝ) : ℂ) ^ (s - 1) * (((|y| : ℝ) : ℂ))⁻¹ = (y : ℂ) ^ (s - 2) := by
    rw [abs_of_pos hy, show s - 2 = (s - 1) + (-1 : ℂ) by ring, Complex.cpow_add _ _ hy0, Complex.cpow_neg_one]
  simp only [Lf, abs_neg, quasiChar_zero_pos' hy, quasiChar_zero_neg' hy]
  rw [mul_one, mul_assoc, hpow, mul_assoc, mul_assoc, hpow]
  ring

include ha hpsiInf hS in

theorem archZeta30_jacquetVector3_eq
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (κ : ℝ)
    (hκ : MeasureTheory.Measure.map
        (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
      ENNReal.ofReal κ • (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
        fun y => ENNReal.ofReal |y|⁻¹)
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (e : ℤ)
    (hσ : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v 0 e)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ, M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (s : ℂ) (hs : q₀ P u₃ < s.re) :
    0 < κ ∧
      archZeta30 ν_mul (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) (σ.comp E) s 1 =
        (κ : ℂ) * ∫ y in Ioi (0 : ℝ), (Phi a psiInf D u₃ a₃ S y + (-1 : ℂ) ^ (e : ZMod 2).val * Phi a psiInf D u₃ a₃ S (-y)) *
          ((y : ℝ) : ℂ) ^ (s - 2) := by
  have hW : ∀ z : (InfiniteAdeleRing ℚ)ˣ,
      jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S (iotaGL (diagUnitGL2 z) * 1) =
        Phi a psiInf D u₃ a₃ S (StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) := fun z => by
    rw [LanglandsTunnell.CubicInduction.jacquetVector3_iotaGL_diagUnitGL2_mul]; rfl
  obtain ⟨hpos, hZ⟩ := LanglandsTunnell.CubicInduction.archZeta30_one_eq_mul_integral_quasiChar_of_isArchCompAt ν_mul κ hκ σ 0 e hσ
    E hE (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) (Phi a psiInf D u₃ a₃ S) hW
    (aestronglyMeasurable_Phi a ha psiInf hpsiInf D u₃ a₃ S hS) s
  refine ⟨hpos, ?_⟩
  rw [hZ, ← integral_Lf_eq a ha psiInf hpsiInf D u₃ a₃ S hS s (e : ZMod 2) hs]
  rfl

end Torus

end Ws23Z0

namespace Ws23PhiFlatM

open LanglandsTunnell.Converse.ArchR Set

noncomputable def gM (x y₁ y₂ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
     y₂ * Real.sin θ, y₂ * Real.cos θ]

noncomputable def rotM (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]

theorem det_rotM (θ : ℝ) : (rotM θ).det = 1 := by
  rw [rotM, Matrix.det_fin_two_of]; have := Real.sin_sq_add_cos_sq θ; nlinarith [this]

noncomputable def rotGL (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotM θ) (by rw [det_rotM]; exact one_ne_zero)

theorem rotGL_coe (θ : ℝ) : ((rotGL θ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = rotM θ := rfl

theorem rotGL_mem (θ : ℝ) : rotGL θ ∈ rowIsometrySubgroup₀ ℝ := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨by rw [rotGL_coe, det_rotM], ?_, ?_⟩
  · rw [rotGL_coe, det_rotM, norm_one]
  · intro x y
    simp only [rotGL_coe, rotM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Real.norm_eq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * h

theorem diagOne_mul_gM (c x y₁ y₂ θ : ℝ) (hy₂ : y₂ ≠ 0) :
    diagOne c * gM x y₁ y₂ θ = unip (c * x) * (y₂ • (diagOne (c * y₁ / y₂) * rotM θ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagOne, gM, unip, rotM, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp

theorem W_diagOne_mul_gM {P : RealArchParam} (D : ArchDatumR P)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    {c : ℝ} (hc : c ≠ 0) (x : ℝ) {y₁ y₂ : ℝ} (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) (θ : ℝ) :
    D.W (diagOne c * gM x y₁ y₂ θ) = psi (c * x) * (centralChar P y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (diagOne (c * y₁ / y₂)) := by
  have hτ : c * y₁ / y₂ ≠ 0 := div_ne_zero (mul_ne_zero hc hy₁) hy₂.ne'
  set X : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagOne (c * y₁ / y₂))
    (by rw [diagOne, Matrix.det_fin_two_of]; simpa using hτ) with hX
  have hXc : ((X : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = diagOne (c * y₁ / y₂) := rfl
  have hK : D.W (diagOne (c * y₁ / y₂) * rotM θ) = D.W (diagOne (c * y₁ / y₂)) := by
    have h := hDW0 ⟨rotGL θ, rotGL_mem θ⟩ X
    rw [Units.val_mul, hXc] at h
    exact h
  rw [diagOne_mul_gM c x y₁ y₂ θ hy₂.ne', D.unip_law, D.central_law y₂ _ hy₂.ne', hK]
  ring

theorem archWeightCharℝ_coe (m : ℕ) {κ : GL (Fin 2) ℝ} (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) :
    ((archWeightCharℝ (m : ℤ) ⟨κ, hκ⟩ : ℂˣ) : ℂ) =
      ((((κ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℝ) : ℂ) + Complex.I * (((κ : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℝ) : ℂ)) ^ m := by
  have h1 : ((archWeightCharℝ (m : ℤ) ⟨κ, hκ⟩ : ℂˣ) : ℂ) = ((archWeightOneℝ ⟨κ, hκ⟩ : ℂˣ) : ℂ) ^ m := by
    show (((archWeightOneℝ ⟨κ, hκ⟩) ^ (m : ℤ) : ℂˣ) : ℂ) = _
    rw [zpow_natCast, Units.val_pow_eq_pow_val]
  have h2 : ((archWeightOneℝ ⟨κ, hκ⟩ : ℂˣ) : ℂ) = firstRowℂ κ := rfl
  rw [h1, h2]
  congr 1
  apply Complex.ext <;> simp [firstRowℂ]

theorem W_diagOne_mul_gM_weight {P : RealArchParam} (D : ArchDatumR P) (m : ℕ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ (m : ℤ) r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    {c : ℝ} (hc : c ≠ 0) (x : ℝ) {y₁ y₂ : ℝ} (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) (θ : ℝ) :
    D.W (diagOne c * gM x y₁ y₂ θ) =
      psi (c * x) * (centralChar P y₂ * ((|y₂| : ℝ) : ℂ)) *
        ((((Real.cos θ : ℝ) : ℂ) - Complex.I * ((Real.sin θ : ℝ) : ℂ)) ^ m * D.W (diagOne (c * y₁ / y₂))) := by
  have hτ : c * y₁ / y₂ ≠ 0 := div_ne_zero (mul_ne_zero hc hy₁) hy₂.ne'
  set X : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagOne (c * y₁ / y₂))
    (by rw [diagOne, Matrix.det_fin_two_of]; simpa using hτ) with hX
  have hXc : ((X : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = diagOne (c * y₁ / y₂) := rfl
  have hK : D.W (diagOne (c * y₁ / y₂) * rotM θ) =
      (((Real.cos θ : ℝ) : ℂ) - Complex.I * ((Real.sin θ : ℝ) : ℂ)) ^ m * D.W (diagOne (c * y₁ / y₂)) := by
    have h := hDW ⟨rotGL θ, rotGL_mem θ⟩ X
    rw [Units.val_mul, hXc, archWeightCharℝ_coe m (rotGL_mem θ), rotGL_coe] at h
    rw [h]
    congr 2
    simp only [rotM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    push_cast
    ring
  rw [diagOne_mul_gM c x y₁ y₂ θ hy₂.ne', D.unip_law, D.central_law y₂ _ hy₂.ne', hK]
  ring

theorem Gc_def : (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ)) = fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ) := rfl

theorem deriv_Gc (η : ℝ) :
    deriv (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ)) η = -(2 * Real.pi * η) * (Real.exp (-(Real.pi * η ^ 2)) : ℂ) := by
  have h1 : HasDerivAt (fun y : ℝ => -(Real.pi * y ^ 2)) (-(Real.pi * (2 * η))) η := by
    have h := ((hasDerivAt_pow 2 η).const_mul Real.pi).fun_neg
    simp [pow_one] at h
    exact h
  have h3 : HasDerivAt (fun η : ℝ => (Real.exp (-(Real.pi * η ^ 2)) : ℂ))
      (((Real.exp (-(Real.pi * η ^ 2)) * -(Real.pi * (2 * η)) : ℝ) : ℂ)) η :=
    ((Real.hasDerivAt_exp _).comp η h1).ofReal_comp
  rw [h3.deriv]
  push_cast
  ring

theorem moment_zero (ξ : ℝ) :
    ∫ u : ℝ, (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) =
      (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) := by
  have h := LanglandsTunnell.integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv 0 ξ
  simp only [pow_zero, one_mul, iteratedDeriv_zero] at h
  exact h

theorem moment_one (ξ : ℝ) :
    ∫ u : ℝ, ((u : ℝ) : ℂ) * (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) =
      Complex.I * (ξ : ℂ) * (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) := by
  have h := LanglandsTunnell.integral_ofReal_pow_mul_exp_neg_pi_mul_sq_mul_cexp_eq_iteratedDeriv 1 ξ
  simp only [pow_one, iteratedDeriv_one] at h
  rw [h, deriv_Gc]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem integrable_pow_mul_G_mul (k : ℕ) (ξ : ℝ) :
    Integrable (fun u : ℝ => ((u : ℂ) ^ k * (Real.exp (-(Real.pi * u ^ 2)) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ))) := by
  have h0 := (integrable_rpow_mul_exp_neg_mul_sq Real.pi_pos (s := k)
    (by have := k.cast_nonneg (α := ℝ); linarith)).ofReal (𝕜 := ℂ)
  have h : Integrable (fun x : ℝ => (((x ^ (k : ℝ) * Real.exp (-Real.pi * x ^ 2) : ℝ)) : ℂ)) := h0
  have h' : Integrable (fun u : ℝ => (u : ℂ) ^ k * (Real.exp (-(Real.pi * u ^ 2)) : ℂ)) := by
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [Real.rpow_natCast, Complex.ofReal_mul, Complex.ofReal_pow, neg_mul]
  refine h'.mul_bdd (c := 1) (by fun_prop : Continuous fun u : ℝ => Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ))).aestronglyMeasurable
    (ae_of_all _ fun u => ?_)
  rw [Complex.norm_exp]
  have : (2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ) * (u : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_zero]

theorem x_moment (c : ℝ) {y₁ : ℝ} (hy₁ : y₁ ≠ 0) :
    ∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (1 + Complex.I * (x : ℂ)) * psi (c * x) =
      ((|y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (c ^ 2 * y₁ ^ 2))) : ℂ) * (1 - ((c * y₁ ^ 2 : ℝ) : ℂ)) := by
  have hy : 0 < |y₁| := abs_pos.2 hy₁
  set ξ : ℝ := c * |y₁| with hξ
  set f : ℝ → ℂ := fun x => (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (1 + Complex.I * (x : ℂ)) * psi (c * x) with hf

  have hpt : ∀ u : ℝ, f (|y₁| * u) =
      (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) +
        (Complex.I * ((|y₁| : ℝ) : ℂ)) *
          (((u : ℝ) : ℂ) * (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ))) := by
    intro u
    have hsq : (|y₁| * u) ^ 2 / y₁ ^ 2 = u ^ 2 := by rw [mul_pow, sq_abs]; field_simp
    have hpsi : psi (c * (|y₁| * u)) = Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) := by
      rw [psi, hξ]; congr 1; push_cast; ring
    simp only [hf, hsq, hpsi]
    push_cast
    ring
  have hint1 := integrable_pow_mul_G_mul 0 ξ
  have hint2 := integrable_pow_mul_G_mul 1 ξ
  simp only [pow_zero, one_mul] at hint1
  simp only [pow_one] at hint2
  have hscaled : ∫ u : ℝ, f (|y₁| * u) =
      (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) * (1 - ((|y₁| : ℝ) : ℂ) * (ξ : ℂ)) := by
    simp_rw [hpt]
    rw [integral_add hint1 (hint2.const_mul _), integral_const_mul, moment_zero, moment_one]
    linear_combination (((|y₁| : ℝ) : ℂ) * (ξ : ℂ) * (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ)) * Complex.I_sq
  have hsub := Measure.integral_comp_mul_left f |y₁|
  rw [abs_inv, abs_abs, hscaled, Complex.real_smul] at hsub

  have hne : (((|y₁| : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  have key : ∫ x, f x = ((|y₁| : ℝ) : ℂ) * ((Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) * (1 - ((|y₁| : ℝ) : ℂ) * (ξ : ℂ))) := by
    rw [hsub]
    push_cast
    field_simp
  rw [show (∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (1 + Complex.I * (x : ℂ)) * psi (c * x)) = ∫ x, f x from rfl,
    key, hξ]
  have habs : (|y₁| : ℝ) * (c * |y₁|) = c * y₁ ^ 2 := by rw [← sq_abs y₁]; ring
  have hξ2 : (c * |y₁|) ^ 2 = c ^ 2 * y₁ ^ 2 := by rw [mul_pow, sq_abs]
  rw [hξ2]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  have habs' : ((|y₁| : ℝ) : ℂ) * ((c : ℂ) * ((|y₁| : ℝ) : ℂ)) = (c : ℂ) * (y₁ : ℂ) ^ 2 := by exact_mod_cast habs
  linear_combination ((Real.exp (-(Real.pi * (c ^ 2 * y₁ ^ 2))) : ℂ) * (-( ((|y₁| : ℝ) : ℂ)))) * habs'

theorem x_moment_gen (c : ℝ) {y₁ : ℝ} (hy₁ : y₁ ≠ 0) (α β : ℂ) :
    ∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (α + β * (x : ℂ)) * psi (c * x) =
      ((|y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (c ^ 2 * y₁ ^ 2))) : ℂ) * (α + Complex.I * β * ((c * y₁ ^ 2 : ℝ) : ℂ)) := by
  have hy : 0 < |y₁| := abs_pos.2 hy₁
  set ξ : ℝ := c * |y₁| with hξ
  set f : ℝ → ℂ := fun x => (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (α + β * (x : ℂ)) * psi (c * x) with hf
  have hpt : ∀ u : ℝ, f (|y₁| * u) =
      α * ((Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ))) +
        (β * ((|y₁| : ℝ) : ℂ)) *
          (((u : ℝ) : ℂ) * (Real.exp (-(Real.pi * u ^ 2)) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ))) := by
    intro u
    have hsq : (|y₁| * u) ^ 2 / y₁ ^ 2 = u ^ 2 := by rw [mul_pow, sq_abs]; field_simp
    have hpsi : psi (c * (|y₁| * u)) = Complex.exp (2 * Real.pi * Complex.I * (ξ : ℂ) * (u : ℂ)) := by
      rw [psi, hξ]; congr 1; push_cast; ring
    simp only [hf, hsq, hpsi]
    push_cast
    ring
  have hint1 := integrable_pow_mul_G_mul 0 ξ
  have hint2 := integrable_pow_mul_G_mul 1 ξ
  simp only [pow_zero, one_mul] at hint1
  simp only [pow_one] at hint2
  have hscaled : ∫ u : ℝ, f (|y₁| * u) =
      (Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) * (α + Complex.I * β * ((|y₁| : ℝ) : ℂ) * (ξ : ℂ)) := by
    simp_rw [hpt]
    rw [integral_add (hint1.const_mul _) (hint2.const_mul _), integral_const_mul, integral_const_mul, moment_zero, moment_one]
    ring
  have hsub := Measure.integral_comp_mul_left f |y₁|
  rw [abs_inv, abs_abs, hscaled, Complex.real_smul] at hsub
  have hne : (((|y₁| : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
  have key : ∫ x, f x = ((|y₁| : ℝ) : ℂ) * ((Real.exp (-(Real.pi * ξ ^ 2)) : ℂ) * (α + Complex.I * β * ((|y₁| : ℝ) : ℂ) * (ξ : ℂ))) := by
    rw [hsub]
    push_cast
    field_simp
  rw [show (∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) * (α + β * (x : ℂ)) * psi (c * x)) = ∫ x, f x from rfl,
    key, hξ]
  have habs : (|y₁| : ℝ) * (c * |y₁|) = c * y₁ ^ 2 := by rw [← sq_abs y₁]; ring
  have hξ2 : (c * |y₁|) ^ 2 = c ^ 2 * y₁ ^ 2 := by rw [mul_pow, sq_abs]
  rw [hξ2]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  have habs' : ((|y₁| : ℝ) : ℂ) * ((c : ℂ) * ((|y₁| : ℝ) : ℂ)) = (c : ℂ) * (y₁ : ℂ) ^ 2 := by exact_mod_cast habs
  linear_combination ((Real.exp (-(Real.pi * (c ^ 2 * y₁ ^ 2))) : ℂ) * ((|y₁| : ℝ) : ℂ) * Complex.I * β) * habs'

noncomputable def eM (x y₁ y₂ θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ / y₁, -(x * Real.cos θ) / y₁ + Real.sin θ / y₂;
     -(Real.sin θ) / y₁, x * Real.sin θ / y₁ + Real.cos θ / y₂]

section EKit
variable (x y₁ y₂ θ : ℝ)

theorem det_eM : (eM x y₁ y₂ θ).det = (y₁ * y₂)⁻¹ := by
  have h := Real.sin_sq_add_cos_sq θ
  rw [eM, Matrix.det_fin_two_of]
  linear_combination (y₁ * y₂)⁻¹ * h

theorem eM_mul_gM (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) : eM x y₁ y₂ θ * gM x y₁ y₂ θ = 1 := by
  have h := Real.sin_sq_add_cos_sq θ
  have h1 : y₁ * y₁⁻¹ = 1 := mul_inv_cancel₀ hy₁
  have h2 : y₂ * y₂⁻¹ = 1 := mul_inv_cancel₀ hy₂
  rw [eM, gM]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (Real.cos θ ^ 2) * h1 + (Real.sin θ ^ 2) * h2 + h
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-(Real.cos θ * Real.sin θ)) * h1 + (Real.cos θ * Real.sin θ) * h2
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (-(Real.sin θ * Real.cos θ)) * h1 + (Real.cos θ * Real.sin θ) * h2
  · simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (Real.sin θ ^ 2) * h1 + (Real.cos θ ^ 2) * h2 + h

theorem inv_eM (hy₁ : y₁ ≠ 0) (hy₂ : y₂ ≠ 0) : (eM x y₁ y₂ θ)⁻¹ = gM x y₁ y₂ θ :=
  Matrix.inv_eq_right_inv (eM_mul_gM x y₁ y₂ θ hy₁ hy₂)

theorem sumsq_eM : ∑ i : Fin 2, ∑ j : Fin 2, eM x y₁ y₂ θ i j ^ 2 = (1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2 := by
  have h := Real.sin_sq_add_cos_sq θ
  simp only [Fin.sum_univ_two, eM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  linear_combination ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2) * h

theorem gM_one_zero : gM x y₁ y₂ θ 1 0 = y₂ * Real.sin θ := by simp [gM]
theorem gM_one_one : gM x y₁ y₂ θ 1 1 = y₂ * Real.cos θ := by simp [gM]

theorem lin_eM :
    -(((eM x y₁ y₂ θ 1 0 : ℝ) : ℂ) - Complex.I * ((eM x y₁ y₂ θ 1 1 : ℝ) : ℂ)) * ((y₂ * Real.sin θ : ℝ) : ℂ) +
      (((eM x y₁ y₂ θ 0 0 : ℝ) : ℂ) - Complex.I * ((eM x y₁ y₂ θ 0 1 : ℝ) : ℂ)) * ((y₂ * Real.cos θ : ℝ) : ℂ) =
      ((y₂ / y₁ : ℝ) : ℂ) * (1 + Complex.I * (x : ℂ)) := by
  have hc : Complex.sin (θ : ℂ) ^ 2 + Complex.cos (θ : ℂ) ^ 2 = 1 := Complex.sin_sq_add_cos_sq _
  simp only [eM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  linear_combination (((y₂ : ℝ) : ℂ) / ((y₁ : ℝ) : ℂ) * (1 + Complex.I * ((x : ℝ) : ℂ))) * hc

end EKit

noncomputable def pF : MvPolynomial (Fin 2 × Fin 2) ℂ :=
  (MvPolynomial.X (0, 0) - MvPolynomial.C Complex.I * MvPolynomial.X (1, 0)) -
    MvPolynomial.C Complex.I * (MvPolynomial.X (0, 1) - MvPolynomial.C Complex.I * MvPolynomial.X (1, 1))

theorem eval_pF (f : Fin 2 × Fin 2 → ℂ) :
    MvPolynomial.eval f pF = (f (0, 0) - Complex.I * f (1, 0)) - Complex.I * (f (0, 1) - Complex.I * f (1, 1)) := by
  simp [pF, map_sub, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]

theorem flatMSection_eq_harm (m n : ℕ) (ε' : ℝ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M) :
    S = fun M : Matrix (Fin 2) (Fin 3) ℝ =>
      MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((M v.1 (Fin.castSucc v.2) : ℝ) : ℂ)) (pF ^ m) *
        (((M 0 2 : ℝ) : ℂ) + ((ε' : ℝ) : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n * gaussian3 M := by
  rw [hS]
  funext M
  rw [map_pow, eval_pF]
  simp only [Fin.castSucc_zero, Fin.castSucc_one]

theorem flatMSection_mem_polyGauss3 (m n : ℕ) (ε' : ℝ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M) :
    S ∈ polyGauss3 := by
  refine ⟨((MvPolynomial.X (0, 0) - MvPolynomial.C Complex.I * MvPolynomial.X (1, 0)) -
      MvPolynomial.C Complex.I * (MvPolynomial.X (0, 1) - MvPolynomial.C Complex.I * MvPolynomial.X (1, 1))) ^ m *
    (MvPolynomial.X (0, 2) + MvPolynomial.C ((ε' : ℝ) : ℂ) * MvPolynomial.C Complex.I * MvPolynomial.X (1, 2)) ^ n, ?_⟩
  funext M
  simp only [hS, map_mul, map_sub, map_add, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C]

theorem harmF_eM (x y₁ y₂ θ : ℝ) :
    ((((eM x y₁ y₂ θ 0 0 : ℝ) : ℂ) - Complex.I * ((eM x y₁ y₂ θ 1 0 : ℝ) : ℂ)) -
        Complex.I * (((eM x y₁ y₂ θ 0 1 : ℝ) : ℂ) - Complex.I * ((eM x y₁ y₂ θ 1 1 : ℝ) : ℂ))) =
      (((Real.cos θ : ℝ) : ℂ) + Complex.I * ((Real.sin θ : ℝ) : ℂ)) *
        ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + Complex.I * (((x / y₁ : ℝ) : ℂ))) := by
  simp only [eM, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  push_cast
  linear_combination (Complex.cos (θ : ℂ) / ((y₂ : ℝ) : ℂ)) * Complex.I_mul_I

section Pointwise

variable (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
  (hpsiInf : ∀ x : InfiniteAdeleRing ℚ, psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
  {P : RealArchParam} (D : ArchDatumR P) (k₀ m n : ℕ) (ε' : ℝ)
  (hcol : (ε' = -1 ∧ (n : ℤ) = (k₀ : ℤ) - m) ∨ (ε' = 1 ∧ (n : ℤ) = (m : ℤ) - k₀))
  (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ (k₀ : ℤ) r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
  (u₃ : ℂ) (a₃ : ZMod 2) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
  (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
  (c : ℝ) (hc : c ≠ 0)

noncomputable def Gfun (e : Fin 2 → Fin 2 → ℝ) : ℂ :=
  godementInner3 psiInf S (Matrix.of e) 1 *
    quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
    D.W (diagOne c * (Matrix.of e)⁻¹)

noncomputable def hX (x y₁ y₂ : ℝ) : ℂ :=
  (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) *
    ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + (Complex.I * (((1 / y₁ : ℝ)) : ℂ)) * (x : ℂ)) ^ m * psi (c * x)

noncomputable def KY (y₁ y₂ : ℝ) : ℂ :=
  ((ε' : ℂ) * (a : ℂ)) ^ n *
    (quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * (((y₂ ^ (n + 1) / |y₁| : ℝ)) : ℂ) *
      (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2))) : ℂ) *
      (centralChar P y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (diagOne (c * y₁ / y₂)))

include hpsiInf hcol hDW hS hc in
theorem pointwise {x y₁ y₂ θ : ℝ} (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) :
    Gfun psiInf D u₃ a₃ S c (fun i j => eM x y₁ y₂ θ i j) * ((y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹ : ℝ) : ℂ) =
      hX m c x y₁ y₂ * KY a D n ε' u₃ a₃ c y₁ y₂ := by
  have hε : ε' = 1 ∨ ε' = -1 := by rcases hcol with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hofe : (Matrix.of fun i j => eM x y₁ y₂ θ i j) = eM x y₁ y₂ θ := rfl
  have hdet : (Matrix.of fun i j => eM x y₁ y₂ θ i j).det ≠ 0 := by
    rw [hofe, det_eM]; exact inv_ne_zero (mul_ne_zero hy₁ hy₂.ne')
  have hGI := LanglandsTunnell.CubicInduction.godementInner3_eq_mul_exp_of_blockPoly_mul_colHarmonic_gaussian3 a psiInf hpsiInf
    (pF ^ m) n ε' hε S (flatMSection_eq_harm m n ε' S hS) (fun i j => eM x y₁ y₂ θ i j) hdet
  rw [Gfun, hGI]
  simp only [hofe]
  rw [map_pow, eval_pF, harmF_eM, mul_pow, inv_eM x y₁ y₂ θ hy₁ hy₂.ne', gM_one_zero, gM_one_one, sumsq_eM, det_eM,
    W_diagOne_mul_gM_weight D k₀ hDW hc x hy₁ hy₂ θ, hX, KY]
  have hy₂' : |y₂| = y₂ := abs_of_pos hy₂
  have habs : |(y₁ * y₂)⁻¹| = (|y₁| * y₂)⁻¹ := by rw [abs_inv, abs_mul, hy₂']
  have hexp : ∀ u v : ℝ, (Real.exp u : ℂ) * (Real.exp v : ℂ) = (Real.exp (u + v) : ℂ) := fun u v => by
    rw [Real.exp_add]; push_cast; ring
  have hy1a : (|y₁| : ℝ) ≠ 0 := abs_ne_zero.2 hy₁
  have e1 : (Real.exp (-(Real.pi * ((1 + x ^ 2) / y₁ ^ 2 + 1 / y₂ ^ 2))) : ℂ) *
      (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * ((y₂ * Real.sin θ) ^ 2 + (y₂ * Real.cos θ) ^ 2))) : ℂ) =
      (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) *
        (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2))) : ℂ) := by
    rw [hexp, hexp]
    congr 2
    have : (y₂ * Real.sin θ) ^ 2 + (y₂ * Real.cos θ) ^ 2 = y₂ ^ 2 := by linear_combination (y₂ ^ 2) * Real.sin_sq_add_cos_sq θ
    rw [this]
    field_simp
    ring
  have hR : (|(y₁ * y₂)⁻¹|)⁻¹ * (|(y₁ * y₂)⁻¹| ^ 2)⁻¹ * (y₂ ^ 2 * (|y₁ * y₂| ^ 4)⁻¹) = y₂ / |y₁| := by
    rw [habs, abs_mul, hy₂']
    field_simp
  have hRc : (((|(y₁ * y₂)⁻¹| : ℝ) : ℂ))⁻¹ * ((((|(y₁ * y₂)⁻¹| : ℝ) : ℂ)) ^ 2)⁻¹ *
      (((y₂ : ℝ) : ℂ) ^ 2 * ((((|y₁ * y₂| : ℝ) : ℂ)) ^ 4)⁻¹) = ((y₂ : ℝ) : ℂ) / ((|y₁| : ℝ) : ℂ) := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hR
    push_cast at this
    exact this
  push_cast at e1 ⊢
  have hcs : Complex.sin (θ : ℂ) ^ 2 + Complex.cos (θ : ℂ) ^ 2 = 1 := Complex.sin_sq_add_cos_sq _
  set Φp : ℂ := Complex.cos (θ : ℂ) + Complex.I * Complex.sin (θ : ℂ) with hΦp
  set Φm : ℂ := Complex.cos (θ : ℂ) - Complex.I * Complex.sin (θ : ℂ) with hΦm
  have hpm : Φp * Φm = 1 := by
    rw [hΦp, hΦm]; linear_combination hcs + (-(Complex.sin (θ : ℂ)) ^ 2) * Complex.I_sq
  set Ψ : ℂ := ((y₂ : ℝ) : ℂ) * Complex.sin (θ : ℂ) + (ε' : ℂ) * Complex.I * (((y₂ : ℝ) : ℂ) * Complex.cos (θ : ℂ)) with hΨ

  set Cc : ℂ := ((1 / (y₁ : ℂ) - 1 / (y₂ : ℂ) + Complex.I * ((x : ℂ) / (y₁ : ℂ))) ^ m * psi (c * x)) *
    quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * (centralChar P y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (diagOne (c * y₁ / y₂)) with hCc
  set E₁ : ℂ := Complex.exp (-((Real.pi : ℂ) * ((1 + (x : ℂ) ^ 2) / (y₁ : ℂ) ^ 2 + 1 / (y₂ : ℂ) ^ 2))) with hE₁
  set E₂ : ℂ := Complex.exp (-((Real.pi : ℂ) * (a : ℂ) ^ 2 *
    ((((y₂ : ℝ) : ℂ) * Complex.sin (θ : ℂ)) ^ 2 + (((y₂ : ℝ) : ℂ) * Complex.cos (θ : ℂ)) ^ 2))) with hE₂
  set E₃ : ℂ := Complex.exp (-((Real.pi : ℂ) * ((x : ℂ) ^ 2 / (y₁ : ℂ) ^ 2))) with hE₃
  set E₄ : ℂ := Complex.exp (-((Real.pi : ℂ) * (((y₁ : ℂ) ^ 2)⁻¹ + ((y₂ : ℂ) ^ 2)⁻¹ + (a : ℂ) ^ 2 * (y₂ : ℂ) ^ 2))) with hE₄
  set d : ℂ := ((|(y₁ * y₂)⁻¹| : ℝ) : ℂ) with hd
  set R₀ : ℂ := d⁻¹ * (d ^ 2)⁻¹ * (((y₂ : ℝ) : ℂ) ^ 2 * ((((|y₁ * y₂| : ℝ) : ℂ)) ^ 4)⁻¹) with hR₀
  have hRc' : R₀ = ((y₂ : ℝ) : ℂ) / ((|y₁| : ℝ) : ℂ) := by rw [hR₀, hd]; linear_combination hRc

  have hcore : Φp ^ m * ((-Complex.I * (a : ℂ)) ^ n * Ψ ^ n) * Φm ^ k₀ = ((ε' : ℂ) * (a : ℂ)) ^ n * ((y₂ : ℝ) : ℂ) ^ n := by
    rw [← mul_pow]
    rcases hcol with ⟨hε1, hn⟩ | ⟨hε1, hn⟩
    ·
      have hk : k₀ = m + n := by omega
      have hprod : (-Complex.I * (a : ℂ)) * Ψ = (((ε' : ℂ) * (a : ℂ)) * ((y₂ : ℝ) : ℂ)) * Φp := by
        rw [hΨ, hΦp, hε1]; push_cast
        linear_combination ((a : ℂ) * ((y₂ : ℝ) : ℂ) * Complex.cos (θ : ℂ)) * Complex.I_sq
      rw [hprod, hk]
      calc Φp ^ m * ((((ε' : ℂ) * (a : ℂ)) * ((y₂ : ℝ) : ℂ)) * Φp) ^ n * Φm ^ (m + n)
          = ((ε' : ℂ) * (a : ℂ)) ^ n * ((y₂ : ℝ) : ℂ) ^ n * (Φp * Φm) ^ (m + n) := by ring
        _ = ((ε' : ℂ) * (a : ℂ)) ^ n * ((y₂ : ℝ) : ℂ) ^ n := by rw [hpm, one_pow, mul_one]
    ·
      have hk : m = n + k₀ := by omega
      have hprod : (-Complex.I * (a : ℂ)) * Ψ = (((ε' : ℂ) * (a : ℂ)) * ((y₂ : ℝ) : ℂ)) * Φm := by
        rw [hΨ, hΦm, hε1]; push_cast
        linear_combination (-((a : ℂ) * ((y₂ : ℝ) : ℂ) * Complex.cos (θ : ℂ))) * Complex.I_sq
      rw [hprod, hk]
      calc Φp ^ (n + k₀) * ((((ε' : ℂ) * (a : ℂ)) * ((y₂ : ℝ) : ℂ)) * Φm) ^ n * Φm ^ k₀
          = ((ε' : ℂ) * (a : ℂ)) ^ n * ((y₂ : ℝ) : ℂ) ^ n * (Φp * Φm) ^ (n + k₀) := by ring
        _ = ((ε' : ℂ) * (a : ℂ)) ^ n * ((y₂ : ℝ) : ℂ) ^ n := by rw [hpm, one_pow, mul_one]
  linear_combination (Cc * E₁ * E₂ * R₀) * hcore +
    (Cc * ((ε' : ℂ) * (a : ℂ)) ^ n * ((y₂ : ℝ) : ℂ) ^ n * R₀) * e1 +
    (Cc * E₃ * E₄ * ((ε' : ℂ) * (a : ℂ)) ^ n * ((y₂ : ℝ) : ℂ) ^ n) * hRc'

end Pointwise

section Assemble

variable (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
  (hpsiInf : ∀ x : InfiniteAdeleRing ℚ, psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
  {P : RealArchParam} (D : ArchDatumR P) (k₀ m n : ℕ) (ε' : ℝ)
  (hcol : (ε' = -1 ∧ (n : ℤ) = (k₀ : ℤ) - m) ∨ (ε' = 1 ∧ (n : ℤ) = (m : ℤ) - k₀))
  (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ (k₀ : ℤ) r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
  (u₃ : ℂ) (a₃ : ZMod 2) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
  (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
  (c : ℝ) (hc : c ≠ 0)

include hpsiInf hcol hDW hS hc in

theorem assemble (hG : Integrable (Gfun psiInf D u₃ a₃ S c)) :
    ∫ e : Fin 2 → Fin 2 → ℝ, Gfun psiInf D u₃ a₃ S c e =
      2 * (Real.pi : ℂ) * ∫ y₁ : ℝ, ∫ y₂ in Ioi (0 : ℝ), (∫ x : ℝ, hX m c x y₁ y₂) * KY a D n ε' u₃ a₃ c y₁ y₂ := by
  have hK := LanglandsTunnell.RankinSelberg.integral_matrixTwo_eq_setIntegral_iwasawaInv_unconditional (Gfun psiInf D u₃ a₃ S c)
  obtain ⟨hiff, hcv⟩ := hK
  have hF := hiff.1 hG
  rw [hcv]
  set R : Set (ℝ × ℝ × ℝ × ℝ) := univ ×ˢ (univ ×ˢ (Ioi (0 : ℝ) ×ˢ Ioc (0 : ℝ) (2 * Real.pi))) with hR
  have hRm : MeasurableSet R := MeasurableSet.univ.prod (MeasurableSet.univ.prod (measurableSet_Ioi.prod measurableSet_Ioc))
  set F' : ℝ × ℝ × ℝ × ℝ → ℂ := fun p => hX m c p.1 p.2.1 p.2.2.1 * KY a D n ε' u₃ a₃ c p.2.1 p.2.2.1 with hF'
  have hnull : (volume : Measure (ℝ × ℝ × ℝ × ℝ)) {p | p.2.1 = 0} = 0 := by
    have hset : {p : ℝ × ℝ × ℝ × ℝ | p.2.1 = 0} = (univ : Set ℝ) ×ˢ (({0} : Set ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
      ext p; simp
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton]
    simp
  have hae : ∀ᵐ p : ℝ × ℝ × ℝ × ℝ, p.2.1 ≠ 0 := measure_eq_zero_iff_ae_notMem.1 hnull
  have hptw : ∀ᵐ p : ℝ × ℝ × ℝ × ℝ ∂(volume.restrict R),
      (Gfun psiInf D u₃ a₃ S c (fun i j =>
          !![Real.cos p.2.2.2 / p.2.1, -(p.1 * Real.cos p.2.2.2) / p.2.1 + Real.sin p.2.2.2 / p.2.2.1;
             -(Real.sin p.2.2.2) / p.2.1, p.1 * Real.sin p.2.2.2 / p.2.1 + Real.cos p.2.2.2 / p.2.2.1] i j) *
        ((p.2.2.1 ^ 2 * (|p.2.1 * p.2.2.1| ^ 4)⁻¹ : ℝ) : ℂ)) = F' p := by
    rw [ae_restrict_iff' hRm]
    filter_upwards [hae] with p hp hpR
    obtain ⟨x, y₁, y₂, θ⟩ := p
    simp only [hR, mem_prod, mem_univ, mem_Ioi, mem_Ioc, true_and] at hpR
    exact pointwise a psiInf hpsiInf D k₀ m n ε' hcol hDW u₃ a₃ S hS c hc hp hpR.1
  rw [integral_congr_ae hptw]
  have hF'int : Integrable F' (volume.restrict R) := hF.congr hptw
  have hμ : (volume.restrict R : Measure (ℝ × ℝ × ℝ × ℝ)) =
      (volume : Measure ℝ).prod ((volume : Measure ℝ).prod
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) := by
    rw [hR, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ, Measure.volume_eq_prod,
      ← Measure.prod_restrict, Measure.restrict_univ, Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [hμ] at hF'int ⊢
  rw [integral_prod_symm _ hF'int]
  have hinner : ∀ q : ℝ × ℝ × ℝ, ∫ x : ℝ, F' (x, q) = (∫ x : ℝ, hX m c x q.1 q.2.1) * KY a D n ε' u₃ a₃ c q.1 q.2.1 := by
    intro q; simp only [hF']; exact integral_mul_const _ _
  simp_rw [hinner]
  have hint2 : Integrable (fun q : ℝ × ℝ × ℝ => (∫ x : ℝ, hX m c x q.1 q.2.1) * KY a D n ε' u₃ a₃ c q.1 q.2.1)
      ((volume : Measure ℝ).prod ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) := by
    have := hF'int.integral_prod_right
    refine this.congr (ae_of_all _ fun q => hinner q)
  rw [integral_prod _ hint2]
  have hstep : ∀ᵐ y₁ : ℝ ∂volume,
      (∫ q : ℝ × ℝ, (∫ x : ℝ, hX m c x (y₁, q).1 (y₁, q).2.1) * KY a D n ε' u₃ a₃ c (y₁, q).1 (y₁, q).2.1
          ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) =
        2 * (Real.pi : ℂ) * ∫ y₂ in Ioi (0 : ℝ), (∫ x : ℝ, hX m c x y₁ y₂) * KY a D n ε' u₃ a₃ c y₁ y₂ := by
    filter_upwards [hint2.prod_right_ae] with y₁ hy
    rw [integral_prod _ hy]
    have hθ : ∀ y₂ : ℝ, (∫ θ : ℝ in Ioc (0 : ℝ) (2 * Real.pi), (∫ x : ℝ, hX m c x y₁ y₂) * KY a D n ε' u₃ a₃ c y₁ y₂) =
        2 * (Real.pi : ℂ) * ((∫ x : ℝ, hX m c x y₁ y₂) * KY a D n ε' u₃ a₃ c y₁ y₂) := by
      intro y₂
      rw [setIntegral_const, Real.volume_real_Ioc_of_le (by positivity), Complex.real_smul]
      push_cast; ring
    simp_rw [hθ]
    rw [integral_const_mul]
  rw [integral_congr_ae hstep, integral_const_mul]

end Assemble

namespace SingArr

theorem volume_setOf_line_eq_zero (r₀ r₁ : ℝ) (h : r₀ ≠ 0) :
    (volume : Measure (ℝ × ℝ)) {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} = 0 := by
  have hmeas : MeasurableSet {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} :=
    measurableSet_eq_fun (measurable_const.mul measurable_snd) (measurable_const.mul measurable_fst)
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hmeas]
  refine Filter.Eventually.of_forall fun u => ?_
  have hsub : Prod.mk u ⁻¹' {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} ⊆ {r₁ * u / r₀} := by
    intro v hv
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hv
    simp only [Set.mem_singleton_iff]
    field_simp
    linarith [hv]
  exact measure_mono_null hsub (Real.volume_singleton)

theorem volume_setOf_vector_on_line_eq_zero (r₀ r₁ : ℝ) (h : r₀ ≠ 0) :
    (volume : Measure (Fin 2 → ℝ)) {q : Fin 2 → ℝ | r₀ * q 1 = r₁ * q 0} = 0 := by
  have hpre : {q : Fin 2 → ℝ | r₀ * q 1 = r₁ * q 0} =
      MeasurableEquiv.piFinTwo (fun _ => ℝ) ⁻¹' {p : ℝ × ℝ | r₀ * p.2 = r₁ * p.1} := by
    ext q; rfl
  rw [hpre, ← (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).measurableEmbedding.map_apply,
    (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).map_eq]
  exact volume_setOf_line_eq_zero r₀ r₁ h

theorem volume_setOf_det_eq_zero :
    (volume : Measure (Fin 2 → Fin 2 → ℝ)) {x : Fin 2 → Fin 2 → ℝ | (Matrix.of x).det = 0} = 0 := by
  have hdet : ∀ x : Fin 2 → Fin 2 → ℝ, (Matrix.of x).det = x 0 0 * x 1 1 - x 0 1 * x 1 0 := fun x => by
    rw [Matrix.det_fin_two]; rfl
  set S : Set ((Fin 2 → ℝ) × (Fin 2 → ℝ)) := {p | p.1 0 * p.2 1 - p.1 1 * p.2 0 = 0} with hS
  have hpre : {x : Fin 2 → Fin 2 → ℝ | (Matrix.of x).det = 0} =
      MeasurableEquiv.piFinTwo (fun _ => Fin 2 → ℝ) ⁻¹' S := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hdet, hS]
    rfl
  rw [hpre, ← (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => Fin 2 → ℝ)).measurableEmbedding.map_apply,
    (volume_preserving_piFinTwo (fun _ : Fin 2 => Fin 2 → ℝ)).map_eq]
  have hmeas : MeasurableSet S := by
    refine measurableSet_eq_fun ?_ measurable_const
    exact ((measurable_pi_apply 0).comp measurable_fst).mul ((measurable_pi_apply 1).comp measurable_snd) |>.sub
      (((measurable_pi_apply 1).comp measurable_fst).mul ((measurable_pi_apply 0).comp measurable_snd))
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hmeas]
  have hae : ∀ᵐ r : Fin 2 → ℝ ∂(volume : Measure (Fin 2 → ℝ)), r 0 ≠ 0 :=
    Measure.ae_eval_ne (fun _ : Fin 2 => (volume : Measure ℝ)) 0 (0 : ℝ)
  filter_upwards [hae] with r hr
  have hfib : Prod.mk r ⁻¹' S ⊆ {q : Fin 2 → ℝ | r 0 * q 1 = r 1 * q 0} := by
    intro q hq
    simp only [Set.mem_preimage, hS, Set.mem_setOf_eq] at hq
    simp only [Set.mem_setOf_eq]
    linarith [hq]
  exact measure_mono_null hfib (volume_setOf_vector_on_line_eq_zero (r 0) (r 1) hr)

end SingArr

section Integrability

open Topology

variable (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
  (hpsiInf : ∀ x : InfiniteAdeleRing ℚ, psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
  {P : RealArchParam} (D : ArchDatumR P) (m n : ℕ) (ε' : ℝ) (hε : ε' = 1 ∨ ε' = -1)
  (u₃ : ℂ) (a₃ : ZMod 2) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
  (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
  (c : ℝ) (hc : c ≠ 0)

theorem continuousOn_quasiChar (u : ℂ) (b : ZMod 2) : ContinuousOn (fun r : ℝ => quasiChar u b r) {r | r ≠ 0} := by
  intro r hr
  refine ContinuousAt.continuousWithinAt ?_
  unfold quasiChar
  refine ContinuousAt.mul ?_ ?_
  · exact (Complex.continuousAt_ofReal_cpow_const |r| u (Or.inr (abs_ne_zero.2 hr))).comp continuous_abs.continuousAt
  · split_ifs
    · exact continuousAt_const
    · exact ((continuous_of_discreteTopology (f := fun s : SignType => ((s : ℝ) : ℂ))).continuousAt).comp
        (continuousAt_sign_of_ne_zero hr)

def U : Set (Fin 2 → Fin 2 → ℝ) := {e | (Matrix.of e).det ≠ 0}

theorem isOpen_U : IsOpen U :=
  isOpen_ne_fun (continuous_id.matrix_det) continuous_const

theorem continuousOn_inv : ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of e)⁻¹) U := by
  intro e he
  have h : ContinuousAt Ring.inverse (Matrix.of e).det := by
    rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ he
  exact (continuousAt_matrix_inv (Matrix.of e) h).continuousWithinAt

include hpsiInf hS hc hε in
theorem continuousOn_Gfun : ContinuousOn (Gfun psiInf D u₃ a₃ S c) U := by

  have heq : ∀ e ∈ U, Gfun psiInf D u₃ a₃ S c e =
      (MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((e v.1 v.2 : ℝ) : ℂ)) (pF ^ m) *
          (Real.exp (-(Real.pi * ∑ i : Fin 2, ∑ j : Fin 2, e i j ^ 2)) : ℂ) *
          (((|(Matrix.of e).det|)⁻¹ : ℝ) : ℂ) *
          (-Complex.I * (a : ℂ)) ^ n *
          ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) + ((ε' : ℝ) : ℂ) * Complex.I * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)) ^ n *
          (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ)) *
        quasiChar (u₃ + 2) a₃ (Matrix.of e).det * (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ) *
        D.W (diagOne c * (Matrix.of e)⁻¹) := by
    intro e he
    rw [Gfun, LanglandsTunnell.CubicInduction.godementInner3_eq_mul_exp_of_blockPoly_mul_colHarmonic_gaussian3 a psiInf hpsiInf
      (pF ^ m) n ε' hε S (flatMSection_eq_harm m n ε' S hS) e he]
  refine ContinuousOn.congr ?_ (fun e he => heq e he)
  have hinv := continuousOn_inv
  have hent : ∀ i j : Fin 2, ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of e)⁻¹ i j) U := fun i j =>
    (continuous_apply_apply i j).continuousOn.comp hinv (Set.mapsTo_univ _ _)
  have hcoord : Continuous fun e : Fin 2 → Fin 2 → ℝ => (fun v : Fin 2 × Fin 2 => ((e v.1 v.2 : ℝ) : ℂ)) :=
    continuous_pi fun v => Complex.continuous_ofReal.comp ((continuous_apply v.2).comp (continuous_apply v.1))
  have hev : ∀ q : MvPolynomial (Fin 2 × Fin 2) ℂ, Continuous fun e : Fin 2 → Fin 2 → ℝ =>
      MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((e v.1 v.2 : ℝ) : ℂ)) q := fun q =>
    (MvPolynomial.continuous_eval q).comp hcoord
  have hdet : Continuous fun e : Fin 2 → Fin 2 → ℝ => (Matrix.of e).det := continuous_id.matrix_det
  have hdetU : ∀ e ∈ U, (Matrix.of e).det ≠ 0 := fun e he => he
  have hW : ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ => D.W (diagOne c * (Matrix.of e)⁻¹)) U := by
    have h1 : ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ => (diagOne c * (Matrix.of e)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ)) U :=
      continuousOn_const.mul hinv
    have hmaps : Set.MapsTo (fun e : Fin 2 → Fin 2 → ℝ => (diagOne c * (Matrix.of e)⁻¹ : Matrix (Fin 2) (Fin 2) ℝ)) U glSet := by
      intro e he
      show (Matrix.of (diagOne c * (Matrix.of e)⁻¹)).det ≠ 0
      have : Matrix.of (diagOne c * (Matrix.of e)⁻¹) = diagOne c * (Matrix.of e)⁻¹ := rfl
      rw [this, Matrix.det_mul, Matrix.det_nonsing_inv]
      have hd : (diagOne c).det = c := by simp [diagOne, Matrix.det_fin_two_of]
      rw [hd, Ring.inverse_eq_inv]
      exact mul_ne_zero hc (inv_ne_zero he)
    have h2 := D.smooth.continuousOn.comp h1 hmaps
    exact h2
  have hq : ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ => quasiChar (u₃ + 2) a₃ (Matrix.of e).det) U :=
    (continuousOn_quasiChar (u₃ + 2) a₃).comp hdet.continuousOn hdetU
  have habs2 : ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ => (((|(Matrix.of e).det| ^ 2)⁻¹ : ℝ) : ℂ)) U :=
    Complex.continuous_ofReal.continuousOn.comp
      (((continuous_abs.comp hdet).pow 2).continuousOn.inv₀ fun e he => pow_ne_zero 2 (abs_ne_zero.2 he)) (Set.mapsTo_univ _ _)
  have habs1 : ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ => (((|(Matrix.of e).det|)⁻¹ : ℝ) : ℂ)) U :=
    Complex.continuous_ofReal.continuousOn.comp
      ((continuous_abs.comp hdet).continuousOn.inv₀ fun e he => abs_ne_zero.2 he) (Set.mapsTo_univ _ _)
  have hE1 : Continuous fun e : Fin 2 → Fin 2 → ℝ => (Real.exp (-(Real.pi * ∑ i : Fin 2, ∑ j : Fin 2, e i j ^ 2)) : ℂ) := by
    refine Complex.continuous_ofReal.comp (Real.continuous_exp.comp ?_)
    refine (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_).const_mul _ |>.neg
    exact (continuous_apply_apply i j).pow 2
  have hE2 : ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ =>
      (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ)) U := by
    refine Complex.continuous_ofReal.continuousOn.comp (Real.continuous_exp.continuousOn.comp ?_ (Set.mapsTo_univ _ _))
      (Set.mapsTo_univ _ _)
    exact ((((hent 1 0).pow 2).add ((hent 1 1).pow 2)).const_smul (Real.pi * (a : ℝ) ^ 2)).neg.congr
      (fun e _ => by simp [smul_eq_mul]; ring)
  have hρ : ContinuousOn (fun e : Fin 2 → Fin 2 → ℝ =>
      ((((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) + ((ε' : ℝ) : ℂ) * Complex.I * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)) ^ n) U :=
    ((Complex.continuous_ofReal.continuousOn.comp (hent 1 0) (Set.mapsTo_univ _ _)).add
      (continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.comp (hent 1 1) (Set.mapsTo_univ _ _)))).pow n
  exact (((((((((hev (pF ^ m)).continuousOn).mul hE1.continuousOn).mul habs1).mul continuousOn_const).mul hρ).mul hE2).mul hq).mul
    habs2).mul hW

theorem Gfun_eq_jacquetIntegrand3 : Gfun psiInf D u₃ a₃ S c = jacquetIntegrand3 D u₃ a₃ c psiInf S 1 := by
  funext e
  rw [Gfun, jacquetIntegrand3, AutomorphicForm.StandardKernel.realMat_one]

theorem neg_re_le_sum_of_mem {M : Multiset ℂ} {μ : ℂ} (h : μ ∈ M) : -μ.re ≤ (M.map (fun z => ‖z‖)).sum := by
  have h1 : -μ.re ≤ ‖μ‖ := by have := Complex.abs_re_le_norm μ; have := neg_abs_le μ.re; linarith
  have h2 : ‖μ‖ ≤ (M.map (fun z => ‖z‖)).sum :=
    Multiset.single_le_sum (fun x hx => by obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 hx; exact norm_nonneg z) _
      (Multiset.mem_map_of_mem _ h)
  linarith

include hpsiInf hS hc hε in
theorem integrable_Gfun (ha : a ≠ 0) : Integrable (Gfun psiInf D u₃ a₃ S c) := by

  set B : ZMod 2 → ℝ := fun b => ((P.twist 0 b).gammaR.map (fun z => ‖z‖)).sum + ((P.twist 0 b).gammaC.map (fun z => ‖z‖)).sum with hB
  set c₀ : ℝ := B 0 + B 1 + 1 with hc₀
  have hBn : ∀ b, 0 ≤ B b := fun b => by
    simp only [hB]
    refine add_nonneg (Multiset.sum_nonneg fun x hx => ?_) (Multiset.sum_nonneg fun x hx => ?_) <;>
    · obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 hx; exact norm_nonneg z
  have hBle : ∀ b, B b ≤ B 0 + B 1 := fun b => by
    rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b with rfl | rfl
    · linarith [hBn 1]
    · linarith [hBn 0]
  have hc₀' : ∀ b : ZMod 2, (∀ μ ∈ (P.twist 0 b).gammaR, -μ.re < c₀) ∧ (∀ ν ∈ (P.twist 0 b).gammaC, -ν.re < c₀) := by
    intro b
    have hgC : 0 ≤ ((P.twist 0 b).gammaC.map (fun z => ‖z‖)).sum :=
      Multiset.sum_nonneg fun x hx => by obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 hx; exact norm_nonneg z
    have hgR : 0 ≤ ((P.twist 0 b).gammaR.map (fun z => ‖z‖)).sum :=
      Multiset.sum_nonneg fun x hx => by obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 hx; exact norm_nonneg z
    refine ⟨fun μ hμ => ?_, fun ν hν => ?_⟩
    · have := neg_re_le_sum_of_mem hμ; have := hBle b; simp only [hB] at *; linarith
    · have := neg_re_le_sum_of_mem hν; have := hBle b; simp only [hB] at *; linarith
  obtain ⟨hmaj, -, -, -⟩ := LanglandsTunnell.CubicInduction.exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod
    (P := P) u₃ a₃ a psiInf hpsiInf ha D S (flatMSection_mem_polyGauss3 m n ε' S hS) c₀ hc₀'
  obtain ⟨V, hV, F, hF, hbound⟩ := hmaj 1 (max c₀ (-u₃.re) + 1) (by linarith)
  have h1 : (1 : GL (Fin 3) (InfiniteAdeleRing ℚ)) ∈ V := mem_of_mem_nhds hV

  have hUc : (volume : Measure (Fin 2 → Fin 2 → ℝ)) Uᶜ = 0 := by
    have : Uᶜ = {x : Fin 2 → Fin 2 → ℝ | (Matrix.of x).det = 0} := by ext x; simp [U]
    rw [this]; exact SingArr.volume_setOf_det_eq_zero
  have haeU : ∀ᵐ e : Fin 2 → Fin 2 → ℝ, e ∈ U := by
    rw [ae_iff]; first | exact hUc | simpa [Set.compl_def] using hUc
  have hmeas : AEStronglyMeasurable (Gfun psiInf D u₃ a₃ S c) volume := by
    have h := (continuousOn_Gfun a psiInf hpsiInf D m n ε' hε u₃ a₃ S hS c hc).aestronglyMeasurable (μ := volume) isOpen_U.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem haeU] at h
  refine Integrable.mono' (hF.const_mul (|c| ^ (1 - (max c₀ (-u₃.re) + 1)))) hmeas (ae_of_all _ fun e => ?_)
  rw [Gfun_eq_jacquetIntegrand3]
  exact hbound 1 h1 c hc e

end Integrability

section XKY

variable (a : ℚ) (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
  (hpsiInf : ∀ x : InfiniteAdeleRing ℚ, psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
  {P : RealArchParam} (D : ArchDatumR P) (k₀ m n : ℕ) (ε' : ℝ)
  (hcol : (ε' = -1 ∧ (n : ℤ) = (k₀ : ℤ) - m) ∨ (ε' = 1 ∧ (n : ℤ) = (m : ℤ) - k₀))
  (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ (k₀ : ℤ) r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
  (u₃ : ℂ) (a₃ : ZMod 2) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
  (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
  (c : ℝ) (hc : c ≠ 0)

include hpsiInf hcol hDW hS hc in

theorem integrable_XKY (hG : Integrable (Gfun psiInf D u₃ a₃ S c)) :
    Integrable (fun q : ℝ × ℝ => (∫ x : ℝ, hX m c x q.1 q.2) * KY a D n ε' u₃ a₃ c q.1 q.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hK := LanglandsTunnell.RankinSelberg.integral_matrixTwo_eq_setIntegral_iwasawaInv_unconditional (Gfun psiInf D u₃ a₃ S c)
  obtain ⟨hiff, -⟩ := hK
  have hF := hiff.1 hG
  set R : Set (ℝ × ℝ × ℝ × ℝ) := univ ×ˢ (univ ×ˢ (Ioi (0 : ℝ) ×ˢ Ioc (0 : ℝ) (2 * Real.pi))) with hR
  have hRm : MeasurableSet R := MeasurableSet.univ.prod (MeasurableSet.univ.prod (measurableSet_Ioi.prod measurableSet_Ioc))
  set F' : ℝ × ℝ × ℝ × ℝ → ℂ := fun p => hX m c p.1 p.2.1 p.2.2.1 * KY a D n ε' u₃ a₃ c p.2.1 p.2.2.1 with hF'
  have hnull : (volume : Measure (ℝ × ℝ × ℝ × ℝ)) {p | p.2.1 = 0} = 0 := by
    have hset : {p : ℝ × ℝ × ℝ × ℝ | p.2.1 = 0} = (univ : Set ℝ) ×ˢ (({0} : Set ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
      ext p; simp
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton]
    simp
  have hae : ∀ᵐ p : ℝ × ℝ × ℝ × ℝ, p.2.1 ≠ 0 := measure_eq_zero_iff_ae_notMem.1 hnull
  have hptw : ∀ᵐ p : ℝ × ℝ × ℝ × ℝ ∂(volume.restrict R),
      (Gfun psiInf D u₃ a₃ S c (fun i j =>
          !![Real.cos p.2.2.2 / p.2.1, -(p.1 * Real.cos p.2.2.2) / p.2.1 + Real.sin p.2.2.2 / p.2.2.1;
             -(Real.sin p.2.2.2) / p.2.1, p.1 * Real.sin p.2.2.2 / p.2.1 + Real.cos p.2.2.2 / p.2.2.1] i j) *
        ((p.2.2.1 ^ 2 * (|p.2.1 * p.2.2.1| ^ 4)⁻¹ : ℝ) : ℂ)) = F' p := by
    rw [ae_restrict_iff' hRm]
    filter_upwards [hae] with p hp hpR
    obtain ⟨x, y₁, y₂, θ⟩ := p
    simp only [hR, mem_prod, mem_univ, mem_Ioi, mem_Ioc, true_and] at hpR
    exact pointwise a psiInf hpsiInf D k₀ m n ε' hcol hDW u₃ a₃ S hS c hc hp hpR.1
  have hF'int : Integrable F' (volume.restrict R) := hF.congr hptw
  have hμ : (volume.restrict R : Measure (ℝ × ℝ × ℝ × ℝ)) =
      (volume : Measure ℝ).prod ((volume : Measure ℝ).prod
        ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) := by
    rw [hR, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ, Measure.volume_eq_prod,
      ← Measure.prod_restrict, Measure.restrict_univ, Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [hμ] at hF'int
  have hinner : ∀ q : ℝ × ℝ × ℝ, ∫ x : ℝ, F' (x, q) = (∫ x : ℝ, hX m c x q.1 q.2.1) * KY a D n ε' u₃ a₃ c q.1 q.2.1 := by
    intro q; simp only [hF']; exact integral_mul_const _ _
  have hint2 : Integrable (fun q : ℝ × ℝ × ℝ => (∫ x : ℝ, hX m c x q.1 q.2.1) * KY a D n ε' u₃ a₃ c q.1 q.2.1)
      ((volume : Measure ℝ).prod ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))) :=
    hF'int.integral_prod_right.congr (ae_of_all _ fun q => hinner q)
  have hassoc := (MeasureTheory.measurePreserving_prodAssoc (volume : Measure ℝ) (volume.restrict (Ioi (0 : ℝ)))
    (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
  have hint3 : Integrable (fun q : (ℝ × ℝ) × ℝ => (∫ x : ℝ, hX m c x q.1.1 q.1.2) * KY a D n ε' u₃ a₃ c q.1.1 q.1.2)
      (((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))).prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :=
    (hassoc.integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding).2 hint2
  have hθ := hint3.integral_prod_left
  have h2π : (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)) : Measure ℝ).real Set.univ = 2 * Real.pi := by
    rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]; ring
  have hθ' : Integrable (fun q : ℝ × ℝ => ((2 * Real.pi : ℝ) : ℂ) • ((∫ x : ℝ, hX m c x q.1 q.2) * KY a D n ε' u₃ a₃ c q.1 q.2))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine hθ.congr (ae_of_all _ fun q => ?_)
    simp only
    rw [integral_const, h2π, Complex.real_smul, smul_eq_mul]
  have h2πne : (((2 * Real.pi : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (0:ℝ) < 2 * Real.pi).ne'
  have := hθ'.smul ((((2 * Real.pi : ℝ)) : ℂ))⁻¹
  refine this.congr (ae_of_all _ fun q => ?_)
  simp only [Pi.smul_apply, smul_smul, inv_mul_cancel₀ h2πne, one_smul]

end XKY

end Ws23PhiFlatM

namespace Ws23FoldGen

open LanglandsTunnell.Converse.ArchR Set

theorem quasiChar_neg_arg (u : ℂ) (b : ZMod 2) (r : ℝ) :
    quasiChar u b (-r) = (-1 : ℂ) ^ b.val * quasiChar u b r := by
  unfold quasiChar
  rw [abs_neg]
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) b with h | h <;> subst h
  · simp
  · rw [if_neg (by decide), if_neg (by decide), Left.sign_neg, show (1 : ZMod 2).val = 1 from rfl, pow_one]
    push_cast
    ring

theorem neg_one_pow_val_mul_self (b : ZMod 2) : (-1 : ℂ) ^ b.val * (-1 : ℂ) ^ b.val = 1 := by
  rw [← pow_add, ← two_mul, pow_mul]; norm_num

theorem archWeightCharℝ_zero (r : rowIsometrySubgroup₀ ℝ) : ((archWeightCharℝ 0 r : ℂˣ) : ℂ) = 1 := by
  show ((((archWeightOneℝ r) ^ (0 : ℤ)) : ℂˣ) : ℂ) = 1
  rw [zpow_zero, Units.val_one]

end Ws23FoldGen

open Ws23FoldGen LanglandsTunnell.Converse.ArchR Set in
theorem solution
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (k₀ : ℕ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ (k₀ : ℤ) r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (u₃ : ℂ) (a₃ : ZMod 2)
    (m n : ℕ) (ε' : ℝ) (hcol : (ε' = -1 ∧ (n : ℤ) = (k₀ : ℤ) - m) ∨ (ε' = 1 ∧ (n : ℤ) = (m : ℤ) - k₀))
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (κ : ℝ)
    (hκ : MeasureTheory.Measure.map
        (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
      ENNReal.ofReal κ • (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
        fun y => ENNReal.ofReal |y|⁻¹)
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (e : ℤ)
    (hσ : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v 0 e)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      0 < κ ∧
      archZeta30 ν_mul (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) (σ.comp E) s 1 =
        (κ : ℂ) * (2 * (Real.pi : ℂ) * ((ε' : ℂ) * (a : ℂ)) ^ n) *
          ∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (s - 2) *
            ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
              ArchR.quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * (((y₂ ^ (n + 2) : ℝ)) : ℂ) * ArchR.centralChar P₂ y₂ *
                (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
                (D.W (ArchR.diagOne ((a : ℝ) * y * y₁ / y₂)) * (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((1 / y₁ - 1 / y₂ - (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m) +
                  (-1 : ℂ) ^ a₃.val * D.W (ArchR.diagOne (-((a : ℝ) * y * y₁ / y₂))) * (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((-(1 / y₁) - 1 / y₂ + (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m) +
                  (-1 : ℂ) ^ (e : ZMod 2).val * D.W (ArchR.diagOne (-((a : ℝ) * y * y₁ / y₂))) * (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((1 / y₁ - 1 / y₂ + (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m) +
                  (-1 : ℂ) ^ (e : ZMod 2).val * (-1 : ℂ) ^ a₃.val * D.W (ArchR.diagOne ((a : ℝ) * y * y₁ / y₂)) * (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((-(1 / y₁) - 1 / y₂ - (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m)) := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hSmem : S ∈ polyGauss3 := Ws23PhiFlatM.flatMSection_mem_polyGauss3 m n ε' S hS
  have hε : ε' = 1 ∨ ε' = -1 := by rcases hcol with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
  have hε0 : (ε' : ℂ) ≠ 0 := by rcases hε with h | h <;> simp [h]
  refine ⟨Ws23Z0.q₀ P₂ u₃, fun s hs => ?_⟩
  obtain ⟨hκpos, hZ⟩ := Ws23Z0.archZeta30_jacquetVector3_eq a ha psiInf hpsiInf D u₃ a₃ S hSmem ν_mul κ hκ σ e hσ E hE s hs
  refine ⟨hκpos, ?_⟩
  rw [hZ, mul_assoc]
  refine congrArg (fun z : ℂ => (κ : ℂ) * z) ?_
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) => ?_

  set He : ℝ → ℂ := fun t => ∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((t : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m with hHe
  have hHe_congr : ∀ t t' : ℝ, t = t' → He t = He t' := by rintro t t' rfl; rfl

  set Q : ℝ → ℝ → ℝ → ℂ := fun τ y₁ y₂ =>
      quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * (((y₂ ^ (n + 1) / |y₁| : ℝ)) : ℂ) *
        (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2))) : ℂ) *
        (centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
        D.W (diagOne ((a : ℝ) * τ * y₁ / y₂)) *
        (∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) *
          ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + (Complex.I * (((1 / y₁ : ℝ)) : ℂ)) * (x : ℂ)) ^ m *
          psi ((a : ℝ) * τ * x)) with hQ

  have hΦ : ∀ τ : ℝ, τ ≠ 0 → Ws23Z0.Phi a psiInf D u₃ a₃ S τ =
      2 * (Real.pi : ℂ) * ((ε' : ℂ) * (a : ℂ)) ^ n * ∫ y₁ : ℝ, ∫ y₂ in Ioi (0 : ℝ), Q τ y₁ y₂ := by
    intro τ hτ
    simp only [Ws23Z0.Phi, hQ]
    exact LanglandsTunnell.CubicInduction.jacquetVector3_one_eq_integral_xMoment_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
      a ha psiInf hpsiInf D k₀ hDW m n ε' hcol u₃ a₃ S hS τ hτ

  have hX : ∀ τ y₁ y₂ : ℝ, y₁ ≠ 0 →
      (∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) *
          ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + (Complex.I * (((1 / y₁ : ℝ)) : ℂ)) * (x : ℂ)) ^ m * psi ((a : ℝ) * τ * x)) =
        ((|y₁| : ℝ) : ℂ) * (Real.exp (-(Real.pi * (((a : ℝ) * τ) ^ 2 * y₁ ^ 2))) : ℂ) * He (1 / y₁ - 1 / y₂ - (a : ℝ) * τ * y₁) := by
    intro τ y₁ y₂ hy₁
    have h := LanglandsTunnell.integral_exp_neg_pi_sq_div_sq_mul_affine_pow_mul_cexp_eq_mul_hermiteMoment (1 / y₁ - 1 / y₂) ((a : ℝ) * τ) hy₁ m
    simp only [hHe]
    rw [← h]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [psi]
    congr 1
    push_cast
    ring_nf

  have hIQ : ∀ τ : ℝ, τ ≠ 0 → Integrable (fun q : ℝ × ℝ => Q τ q.1 q.2) ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    intro τ hτ
    have hc : (a : ℝ) * τ ≠ 0 := mul_ne_zero ha' hτ
    have hG := Ws23PhiFlatM.integrable_Gfun a psiInf hpsiInf D m n ε' hε u₃ a₃ S hS ((a : ℝ) * τ) hc ha
    have h := Ws23PhiFlatM.integrable_XKY a psiInf hpsiInf D k₀ m n ε' hcol hDW u₃ a₃ S hS ((a : ℝ) * τ) hc hG
    have hκ1 : (((ε' : ℂ) * (a : ℂ)) ^ n) ≠ 0 := pow_ne_zero _ (mul_ne_zero hε0 (by exact_mod_cast ha))
    have h' := h.const_mul ((((ε' : ℂ) * (a : ℂ)) ^ n)⁻¹)
    refine h'.congr (ae_of_all _ fun q => ?_)
    have e : (∫ x : ℝ, Ws23PhiFlatM.hX m ((a : ℝ) * τ) x q.1 q.2) * Ws23PhiFlatM.KY a D n ε' u₃ a₃ ((a : ℝ) * τ) q.1 q.2 =
        (((ε' : ℂ) * (a : ℂ)) ^ n) * Q τ q.1 q.2 := by
      simp only [Ws23PhiFlatM.hX, Ws23PhiFlatM.KY, hQ]; ring
    simp only
    rw [e, ← mul_assoc, inv_mul_cancel₀ hκ1, one_mul]

  set G : ℝ → ℝ → ℂ := fun τ y₁ => ∫ y₂ in Ioi (0 : ℝ), Q τ y₁ y₂ with hG
  have hGint : ∀ τ : ℝ, τ ≠ 0 → Integrable (G τ) := fun τ hτ => by
    simpa only [hG] using (hIQ τ hτ).integral_prod_left
  have hsplit : ∀ τ : ℝ, τ ≠ 0 → ∫ y₁ : ℝ, G τ y₁ = ∫ y₁ in Ioi (0 : ℝ), (G τ y₁ + G τ (-y₁)) := by
    intro τ hτ
    have hI := hGint τ hτ
    rw [← intervalIntegral.integral_Iic_add_Ioi hI.integrableOn hI.integrableOn, ← neg_zero,
      ← integral_comp_neg_Ioi 0 (G τ), neg_zero, ← integral_add hI.comp_neg.integrableOn hI.integrableOn]
    refine setIntegral_congr_fun measurableSet_Ioi fun y₁ _ => ?_
    ring
  have hsec : ∀ τ : ℝ, τ ≠ 0 → ∀ᵐ y₁ : ℝ, Integrable (fun y₂ => Q τ y₁ y₂) (volume.restrict (Ioi (0 : ℝ))) :=
    fun τ hτ => (hIQ τ hτ).prod_right_ae
  have hsec' : ∀ τ : ℝ, τ ≠ 0 → ∀ᵐ y₁ : ℝ, Integrable (fun y₂ => Q τ (-y₁) y₂) (volume.restrict (Ioi (0 : ℝ))) :=
    fun τ hτ => (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae (hsec τ hτ)
  have hyn : -y ≠ 0 := neg_ne_zero.2 hy.ne'

  set Fst : ℝ → ℝ → ℂ := fun y₁ y₂ =>
      quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * (((y₂ ^ (n + 2) : ℝ)) : ℂ) * centralChar P₂ y₂ *
        (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) with hFst
  set fp : ℝ → ℝ → ℂ := fun y₁ y₂ => D.W (diagOne ((a : ℝ) * y * y₁ / y₂)) with hfp
  set fm : ℝ → ℝ → ℂ := fun y₁ y₂ => D.W (diagOne (-((a : ℝ) * y * y₁ / y₂))) with hfm
  have hexp2 : ∀ y₁ y₂ τ : ℝ, τ ^ 2 = y ^ 2 →
      (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2))) : ℂ) *
        (Real.exp (-(Real.pi * (((a : ℝ) * τ) ^ 2 * y₁ ^ 2))) : ℂ) =
      (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) := by
    intro y₁ y₂ τ hτ
    rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; rw [mul_pow, hτ]; ring
  have P1 : ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ → Q y y₁ y₂ = Fst y₁ y₂ * fp y₁ y₂ * He (1 / y₁ - 1 / y₂ - (a : ℝ) * y * y₁) := by
    intro y₁ y₂ hy₁ hy₂
    simp only [hQ, hFst, hfp]
    rw [hX y y₁ y₂ hy₁.ne', abs_of_pos hy₁, abs_of_pos hy₂, ← hexp2 y₁ y₂ y rfl]
    have : (((y₂ ^ (n + 1) / y₁ : ℝ)) : ℂ) * ((y₂ : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) = (((y₂ ^ (n + 2) : ℝ)) : ℂ) := by
      have hy1c : ((y₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy₁.ne'
      push_cast; field_simp; ring
    linear_combination (quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * centralChar P₂ y₂ *
      (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2))) : ℂ) *
      (Real.exp (-(Real.pi * (((a : ℝ) * y) ^ 2 * y₁ ^ 2))) : ℂ) * D.W (diagOne ((a : ℝ) * y * y₁ / y₂)) *
      He (1 / y₁ - 1 / y₂ - (a : ℝ) * y * y₁)) * this

  have hsc : ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      (((y₂ ^ (n + 1) / y₁ : ℝ)) : ℂ) * ((y₂ : ℝ) : ℂ) * ((y₁ : ℝ) : ℂ) = (((y₂ ^ (n + 2) : ℝ)) : ℂ) := by
    intro y₁ y₂ hy₁ hy₂
    have hy1c : ((y₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy₁.ne'
    push_cast; field_simp; ring
  have P2 : ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      Q y (-y₁) y₂ = (-1 : ℂ) ^ a₃.val * Fst y₁ y₂ * fm y₁ y₂ * He (-(1 / y₁) - 1 / y₂ + (a : ℝ) * y * y₁) := by
    intro y₁ y₂ hy₁ hy₂
    simp only [hQ, hFst, hfm]
    rw [hX y (-y₁) y₂ (neg_ne_zero.2 hy₁.ne'), abs_neg, abs_of_pos hy₁, abs_of_pos hy₂,
      show (-y₁ * y₂)⁻¹ = -((y₁ * y₂)⁻¹) by rw [neg_mul, inv_neg], quasiChar_neg_arg,
      show (a : ℝ) * y * -y₁ / y₂ = -((a : ℝ) * y * y₁ / y₂) by ring,
      hHe_congr (1 / -y₁ - 1 / y₂ - (a : ℝ) * y * -y₁) (-(1 / y₁) - 1 / y₂ + (a : ℝ) * y * y₁) (by rw [div_neg]; ring),
      show ((-y₁) ^ 2)⁻¹ = (y₁ ^ 2)⁻¹ by rw [neg_sq], show ((a : ℝ) * y) ^ 2 * (-y₁) ^ 2 = ((a : ℝ) * y) ^ 2 * y₁ ^ 2 by rw [neg_sq],
      ← hexp2 y₁ y₂ y rfl]
    linear_combination ((-1 : ℂ) ^ a₃.val * quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * centralChar P₂ y₂ *
      (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2))) : ℂ) *
      (Real.exp (-(Real.pi * (((a : ℝ) * y) ^ 2 * y₁ ^ 2))) : ℂ) * D.W (diagOne (-((a : ℝ) * y * y₁ / y₂))) *
      He (-(1 / y₁) - 1 / y₂ + (a : ℝ) * y * y₁)) * hsc y₁ y₂ hy₁ hy₂
  have P3 : ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      Q (-y) y₁ y₂ = Fst y₁ y₂ * fm y₁ y₂ * He (1 / y₁ - 1 / y₂ + (a : ℝ) * y * y₁) := by
    intro y₁ y₂ hy₁ hy₂
    simp only [hQ, hFst, hfm]
    rw [hX (-y) y₁ y₂ hy₁.ne', abs_of_pos hy₁, abs_of_pos hy₂,
      show (a : ℝ) * -y * y₁ / y₂ = -((a : ℝ) * y * y₁ / y₂) by ring,
      hHe_congr (1 / y₁ - 1 / y₂ - (a : ℝ) * -y * y₁) (1 / y₁ - 1 / y₂ + (a : ℝ) * y * y₁) (by ring),
      ← hexp2 y₁ y₂ (-y) (neg_sq y)]
    linear_combination (quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * centralChar P₂ y₂ *
      (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2))) : ℂ) *
      (Real.exp (-(Real.pi * (((a : ℝ) * -y) ^ 2 * y₁ ^ 2))) : ℂ) * D.W (diagOne (-((a : ℝ) * y * y₁ / y₂))) *
      He (1 / y₁ - 1 / y₂ + (a : ℝ) * y * y₁)) * hsc y₁ y₂ hy₁ hy₂
  have P4 : ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ →
      Q (-y) (-y₁) y₂ = (-1 : ℂ) ^ a₃.val * Fst y₁ y₂ * fp y₁ y₂ * He (-(1 / y₁) - 1 / y₂ - (a : ℝ) * y * y₁) := by
    intro y₁ y₂ hy₁ hy₂
    simp only [hQ, hFst, hfp]
    rw [hX (-y) (-y₁) y₂ (neg_ne_zero.2 hy₁.ne'), abs_neg, abs_of_pos hy₁, abs_of_pos hy₂,
      show (-y₁ * y₂)⁻¹ = -((y₁ * y₂)⁻¹) by rw [neg_mul, inv_neg], quasiChar_neg_arg,
      show (a : ℝ) * -y * -y₁ / y₂ = (a : ℝ) * y * y₁ / y₂ by ring,
      hHe_congr (1 / -y₁ - 1 / y₂ - (a : ℝ) * -y * -y₁) (-(1 / y₁) - 1 / y₂ - (a : ℝ) * y * y₁) (by rw [div_neg]; ring),
      show ((-y₁) ^ 2)⁻¹ = (y₁ ^ 2)⁻¹ by rw [neg_sq], show ((a : ℝ) * -y) ^ 2 * (-y₁) ^ 2 = ((a : ℝ) * -y) ^ 2 * y₁ ^ 2 by rw [neg_sq],
      ← hexp2 y₁ y₂ (-y) (neg_sq y)]
    linear_combination ((-1 : ℂ) ^ a₃.val * quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * centralChar P₂ y₂ *
      (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2))) : ℂ) *
      (Real.exp (-(Real.pi * (((a : ℝ) * -y) ^ 2 * y₁ ^ 2))) : ℂ) * D.W (diagOne ((a : ℝ) * y * y₁ / y₂)) *
      He (-(1 / y₁) - 1 / y₂ - (a : ℝ) * y * y₁)) * hsc y₁ y₂ hy₁ hy₂

  have hI1 : IntegrableOn (fun y₁ => G y y₁ + G y (-y₁)) (Ioi 0) := ((hGint y hy.ne').add (hGint y hy.ne').comp_neg).integrableOn
  have hI2 : IntegrableOn (fun y₁ => G (-y) y₁ + G (-y) (-y₁)) (Ioi 0) := ((hGint (-y) hyn).add (hGint (-y) hyn).comp_neg).integrableOn
  have hae : ∀ᵐ y₁ : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      (G y y₁ + G y (-y₁)) + (-1 : ℂ) ^ (e : ZMod 2).val * (G (-y) y₁ + G (-y) (-y₁)) =
        ∫ y₂ in Ioi (0 : ℝ), Fst y₁ y₂ *
          (fp y₁ y₂ * He (1 / y₁ - 1 / y₂ - (a : ℝ) * y * y₁) +
            (-1 : ℂ) ^ a₃.val * fm y₁ y₂ * He (-(1 / y₁) - 1 / y₂ + (a : ℝ) * y * y₁) +
            (-1 : ℂ) ^ (e : ZMod 2).val * fm y₁ y₂ * He (1 / y₁ - 1 / y₂ + (a : ℝ) * y * y₁) +
            (-1 : ℂ) ^ (e : ZMod 2).val * (-1 : ℂ) ^ a₃.val * fp y₁ y₂ * He (-(1 / y₁) - 1 / y₂ - (a : ℝ) * y * y₁)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae (hsec y hy.ne'), ae_restrict_of_ae (hsec' y hy.ne'),
      ae_restrict_of_ae (hsec (-y) hyn), ae_restrict_of_ae (hsec' (-y) hyn)] with y₁ hy₁ i1 i2 i3 i4
    have hy₁ : 0 < y₁ := hy₁
    simp only [hG]
    have i12 : Integrable (fun y₂ => Q y y₁ y₂ + Q y (-y₁) y₂) (volume.restrict (Ioi (0 : ℝ))) := i1.add i2
    have i34 : Integrable (fun y₂ => (-1 : ℂ) ^ (e : ZMod 2).val * (Q (-y) y₁ y₂ + Q (-y) (-y₁) y₂)) (volume.restrict (Ioi (0 : ℝ))) :=
      (i3.add i4).const_mul _
    rw [← integral_add i1 i2, ← integral_add i3 i4, ← integral_const_mul, ← integral_add i12 i34]
    refine setIntegral_congr_fun measurableSet_Ioi fun y₂ (hy₂ : 0 < y₂) => ?_
    rw [P1 y₁ y₂ hy₁ hy₂, P2 y₁ y₂ hy₁ hy₂, P3 y₁ y₂ hy₁ hy₂, P4 y₁ y₂ hy₁ hy₂]
    ring
  have eΦ1 := hΦ y hy.ne'
  have eΦ2 := hΦ (-y) hyn
  rw [hsplit y hy.ne'] at eΦ1
  rw [hsplit (-y) hyn] at eΦ2
  rw [eΦ1, eΦ2]
  have hcomb : (∫ y₁ in Ioi (0 : ℝ), (G y y₁ + G y (-y₁))) + (-1 : ℂ) ^ (e : ZMod 2).val * ∫ y₁ in Ioi (0 : ℝ), (G (-y) y₁ + G (-y) (-y₁)) =
      ∫ y₁ in Ioi (0 : ℝ), ((G y y₁ + G y (-y₁)) + (-1 : ℂ) ^ (e : ZMod 2).val * (G (-y) y₁ + G (-y) (-y₁))) := by
    rw [integral_add hI1 (hI2.const_mul _), integral_const_mul]
  have step : ∀ T1 T2 Y cc sg : ℂ, (cc * T1 + sg * (cc * T2)) * Y = cc * Y * (T1 + sg * T2) := by intros; ring
  rw [step, hcomb, integral_congr_ae hae]
  simp only [hFst, hHe, hfp, hfm]
  push_cast
  ring

#print axioms solution

end S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_integral_twoSheet_hermiteBracket_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_integral_twoSheet_hermiteBracket_of_conjBlockHarmonic_pow_colHarmonic_gaussian3 (solution)
