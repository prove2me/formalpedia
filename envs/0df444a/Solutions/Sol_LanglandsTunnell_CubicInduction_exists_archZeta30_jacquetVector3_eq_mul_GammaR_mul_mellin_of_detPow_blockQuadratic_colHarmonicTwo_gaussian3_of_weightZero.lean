-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_weightZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/b99df490-2b39-591f-80cd-8b338f7587d9

import Mathlib
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_iotaGL_diagUnitGL2_mul
import Theorems.Thm_LanglandsTunnell_CubicInduction_archZeta30_one_eq_mul_integral_quasiChar_of_isArchCompAt
import Theorems.Thm_LanglandsTunnell_CubicInduction_exists_integrable_majorant_jacquetIntegrand3_and_aestronglyMeasurable_prod
import Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_weightZero
import Theorems.Thm_LanglandsTunnell_exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_weightZero
p2m_attr_erase "simp" "LanglandsTunnell.CubicLambda.ResolventDatum.s3.injEq LanglandsTunnell.CubicLambda.ResolventDatum.s3.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.sizeOf_spec LanglandsTunnell.CubicLambda.ResolventDatum.cyclic.injEq"

set_option autoImplicit false

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

noncomputable section

namespace Z0Q

open LanglandsTunnell.Converse.ArchR Set Real

section Profile

variable {P₂ : RealArchParam} (D : ArchDatumR P₂)

def Fp (τ : ℝ) : ℂ := D.W (diagOne τ)

theorem continuous_diagOneCoords : Continuous fun τ : ℝ => Matrix.of.symm (ArchR.diagOne τ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [ArchR.diagOne, continuous_const, continuous_id']

theorem continuousOn_Fp : ContinuousOn (Fp D) {τ : ℝ | τ ≠ 0} := by
  have hW := D.smooth.continuousOn
  have hmap : MapsTo (fun τ : ℝ => Matrix.of.symm (ArchR.diagOne τ)) {τ : ℝ | τ ≠ 0} ArchR.glSet := by
    intro τ hτ
    show (Matrix.of (Matrix.of.symm (ArchR.diagOne τ))).det ≠ 0
    simpa [ArchR.diagOne, Matrix.det_fin_two] using hτ
  have h := hW.comp (continuous_diagOneCoords).continuousOn hmap
  refine h.congr (fun τ _ => ?_)
  simp [Fp, ArchR.asPi]

theorem measurable_Fp : Measurable (Fp D) :=
  measurable_of_continuousOn_compl_singleton 0 (by rw [Set.compl_singleton_eq]; exact continuousOn_Fp D)

theorem exists_bound_Fp : ∃ CF σF : ℝ, 0 ≤ CF ∧ 0 ≤ σF ∧ ∀ τ : ℝ, τ ≠ 0 → ‖Fp D τ‖ ≤ CF * (1 + |τ| ^ (-σF)) := by
  obtain ⟨C₁, hC₁⟩ := D.decay_top 0 0
  obtain ⟨C₂, σ₂, hC₂⟩ := D.decay_zero 0
  have hK1 : ArchR.IsK (1 : Matrix (Fin 2) (Fin 2) ℝ) := Submonoid.one_mem _
  have key : ∀ y : ℝ, ‖iteratedFDerivWithin ℝ 0 (ArchR.asPi D.W) ArchR.glSet (ArchR.diagOneMulCoords y 1)‖ = ‖Fp D y‖ := by
    intro y; rw [norm_iteratedFDerivWithin_zero]; simp [ArchR.asPi, ArchR.diagOneMulCoords, Fp]
  have h1 : ∀ y : ℝ, 1 ≤ |y| → ‖Fp D y‖ ≤ C₁ := by
    intro y hy; have := hC₁ y 1 hK1 hy; rw [key] at this; simpa using this
  have h2 : ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 → ‖Fp D y‖ ≤ C₂ * |y| ^ (-σ₂) := by
    intro y hy hy1; have := hC₂ y 1 hK1 hy hy1; rwa [key] at this
  have hC₁0 : 0 ≤ C₁ := le_trans (norm_nonneg _) (h1 1 (by simp))
  have hC₂0 : 0 ≤ C₂ := by
    have := h2 1 one_ne_zero (by simp)
    simp only [abs_one, Real.one_rpow, mul_one] at this
    exact le_trans (norm_nonneg _) this
  refine ⟨max C₁ C₂, max σ₂ 0, hC₁0.trans (le_max_left _ _), le_max_right _ _, fun τ hτ => ?_⟩
  have hM : 0 ≤ max C₁ C₂ := hC₁0.trans (le_max_left _ _)
  have hτp : 0 < |τ| := abs_pos.2 hτ
  have hr : 0 ≤ |τ| ^ (-max σ₂ 0) := Real.rpow_nonneg hτp.le _
  by_cases h : 1 ≤ |τ|
  · calc ‖Fp D τ‖ ≤ C₁ := h1 τ h
      _ ≤ max C₁ C₂ := le_max_left _ _
      _ ≤ max C₁ C₂ * (1 + |τ| ^ (-max σ₂ 0)) := le_mul_of_one_le_right hM (by linarith)
  · push Not at h
    calc ‖Fp D τ‖ ≤ C₂ * |τ| ^ (-σ₂) := h2 τ hτ h.le
      _ ≤ max C₁ C₂ * |τ| ^ (-max σ₂ 0) := by
          refine mul_le_mul (le_max_right _ _) ?_ (Real.rpow_nonneg hτp.le _) hM
          exact Real.rpow_le_rpow_of_exponent_ge hτp h.le (neg_le_neg (le_max_left _ _))
      _ ≤ max C₁ C₂ * (1 + |τ| ^ (-max σ₂ 0)) := by nlinarith

end Profile

theorem quasiChar_of_pos (u : ℂ) (e : ZMod 2) {x : ℝ} (hx : 0 < x) : quasiChar u e x = (x : ℂ) ^ u := by
  unfold quasiChar
  rw [abs_of_pos hx]
  split_ifs
  · rw [mul_one]
  · rw [sign_pos hx]; simp

theorem quasiChar_neg_eq (u : ℂ) (e : ZMod 2) {x : ℝ} (hx : x ≠ 0) :
    quasiChar u e (-x) = (if e = 0 then (1 : ℂ) else -1) * quasiChar u e x := by
  unfold quasiChar
  rw [abs_neg]
  split_ifs with h
  · rw [one_mul]
  · rw [Left.sign_neg]
    rcases lt_or_gt_of_ne hx with h' | h'
    · rw [sign_neg h']; simp
    · rw [sign_pos h']; simp

theorem ite_eq_neg_one_pow (e : ZMod 2) : (if e = 0 then (1 : ℂ) else -1) = (-1 : ℂ) ^ e.val := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) e with h | h <;> subst h
  · simp
  · rw [if_neg (by decide), show (1 : ZMod 2).val = 1 from rfl, pow_one]

theorem measurable_quasiChar (u : ℂ) (e : ZMod 2) : Measurable (quasiChar u e) := by
  have hsign : Measurable fun y : ℝ => (((SignType.sign y : SignType) : ℝ) : ℂ) := by
    have : (fun y : ℝ => (((SignType.sign y : SignType) : ℝ) : ℂ)) =
        fun y => if 0 < y then (1 : ℂ) else if y < 0 then -1 else 0 := by
      funext y; rw [sign_apply]; split_ifs <;> simp
    rw [this]
    exact Measurable.ite measurableSet_Ioi measurable_const
      (Measurable.ite measurableSet_Iio measurable_const measurable_const)
  have habs : Measurable fun y : ℝ => ((|y| : ℝ) : ℂ) := Complex.measurable_ofReal.comp measurable_abs
  unfold quasiChar
  refine (habs.pow_const u).mul ?_
  split_ifs
  · exact measurable_const
  · exact hsign

theorem rpow_le_rpow_add_rpow_neg {w r M : ℝ} (hw : 0 < w) (hM : |r| ≤ M) : w ^ r ≤ w ^ M + w ^ (-M) := by
  have hr1 : r ≤ M := (le_abs_self r).trans hM
  have hr2 : -M ≤ r := by have := neg_abs_le r; linarith
  rcases le_or_gt 1 w with h1 | h1
  · have : w ^ r ≤ w ^ M := Real.rpow_le_rpow_of_exponent_le h1 hr1
    linarith [Real.rpow_nonneg hw.le (-M)]
  · have : w ^ r ≤ w ^ (-M) := Real.rpow_le_rpow_of_exponent_ge hw h1.le hr2
    linarith [Real.rpow_nonneg hw.le M]

section Kernels

variable (a : ℚ) (P₂ : RealArchParam)

def Kq (q : ℂ) (w : ℝ) : ℂ :=
  centralChar P₂ w * ((|w| : ℝ) : ℂ) * ((w : ℝ) : ℂ) ^ q * (rexp (-(π * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ)

theorem measurable_Kq (q : ℂ) : Measurable (Kq a P₂ q) := by
  unfold Kq centralChar
  exact (((measurable_quasiChar _ _).mul (Complex.measurable_ofReal.comp measurable_abs)).mul
    (Complex.measurable_ofReal.pow_const q)).mul (Complex.measurable_ofReal.comp (Real.measurable_exp.comp (by fun_prop)))

theorem norm_Kq_le (q : ℂ) (w : ℝ) (hw : 0 < w) :
    ‖Kq a P₂ q w‖ ≤ 1 * (w ^ |P₂.centralExponent.re + 1 + q.re| + w ^ (-|P₂.centralExponent.re + 1 + q.re|)) *
      rexp (-(π * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) := by
  rw [Kq, centralChar, quasiChar_of_pos _ _ hw, norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hw,
    Complex.norm_cpow_eq_rpow_re_of_pos hw, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_abs, abs_of_pos hw, abs_of_nonneg (Real.exp_nonneg _), one_mul]
  have e : w ^ P₂.centralExponent.re * w * w ^ q.re = w ^ (P₂.centralExponent.re + 1 + q.re) := by
    rw [Real.rpow_add hw, Real.rpow_add hw, Real.rpow_one]
  rw [e]
  exact mul_le_mul_of_nonneg_right (rpow_le_rpow_add_rpow_neg hw le_rfl) (Real.exp_nonneg _)

variable {P₂' : RealArchParam} (D : ArchDatumR P₂')

def gD (t : ℝ) : ℂ := Fp D ((a : ℝ) * t)

theorem measurable_gD : Measurable (gD a D) := (measurable_Fp D).comp (measurable_const_mul _)

theorem exists_bound_gD (ha : a ≠ 0) : ∃ C σF : ℝ, 0 ≤ σF ∧ ∀ t : ℝ, 0 < t → ‖gD a D t‖ ≤ C * (1 + t ^ (-σF)) := by
  obtain ⟨CF, σF, hCF, hσF, hb⟩ := exists_bound_Fp D
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hapos : 0 < |(a : ℝ)| := abs_pos.2 ha'
  refine ⟨CF * max 1 (|(a : ℝ)| ^ (-σF)), σF, hσF, fun t ht => ?_⟩
  have h := hb ((a : ℝ) * t) (mul_ne_zero ha' ht.ne')
  rw [abs_mul, abs_of_pos ht, Real.mul_rpow hapos.le ht.le] at h
  have hm1 : (1 : ℝ) ≤ max 1 (|(a : ℝ)| ^ (-σF)) := le_max_left _ _
  have hm2 : |(a : ℝ)| ^ (-σF) ≤ max 1 (|(a : ℝ)| ^ (-σF)) := le_max_right _ _
  have ht0 : 0 ≤ t ^ (-σF) := Real.rpow_nonneg ht.le _
  calc ‖gD a D t‖ = ‖Fp D ((a : ℝ) * t)‖ := rfl
    _ ≤ CF * (1 + |(a : ℝ)| ^ (-σF) * t ^ (-σF)) := h
    _ ≤ CF * (max 1 (|(a : ℝ)| ^ (-σF)) * 1 + max 1 (|(a : ℝ)| ^ (-σF)) * t ^ (-σF)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (by linarith) (mul_le_mul_of_nonneg_right hm2 ht0)) hCF
    _ = CF * max 1 (|(a : ℝ)| ^ (-σF)) * (1 + t ^ (-σF)) := by ring

end Kernels

theorem cpow_ofReal_mul' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (c : ℂ) :
    (((x * y : ℝ)) : ℂ) ^ c = (x : ℂ) ^ c * (y : ℂ) ^ c := by
  push_cast; exact Complex.mul_cpow_ofReal_nonneg hx hy c

theorem cpow_ofReal_inv' {x : ℝ} (hx : 0 < x) (c : ℂ) : (((x⁻¹ : ℝ)) : ℂ) ^ c = (((x : ℝ)) : ℂ) ^ (-c) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ ?_, Complex.cpow_neg]
  rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm

section KernelT

variable (a : ℚ) (P₂ : RealArchParam)

def e₁ (y y₁ : ℝ) : ℂ := (rexp (-(π * ((y₁ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ)

def E₂ (w : ℝ) : ℂ := (rexp (-(π * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ)

def Ω (w : ℝ) : ℂ := centralChar P₂ w * ((|w| : ℝ) : ℂ)

def Tg (g : ℝ → ℂ) (p q : ℂ) (y : ℝ) (w : ℝ × ℝ) : ℂ :=
  ((w.1 : ℝ) : ℂ) ^ p * Kq a P₂ q w.2 * e₁ a y w.1 * g (y * w.1 / w.2)

variable {a P₂}

theorem e₁_neg (y y₁ : ℝ) : e₁ a (-y) y₁ = e₁ a y y₁ := by simp [e₁, neg_sq]
theorem e₁_neg' (y y₁ : ℝ) : e₁ a y (-y₁) = e₁ a y y₁ := by simp [e₁, neg_sq]

theorem exp_split (y y₁ y₂ : ℝ) :
    (rexp (-(π * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) =
      e₁ a y y₁ * E₂ a y₂ := by
  rw [e₁, E₂, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

theorem Tg_eq (g : ℝ → ℂ) (p q : ℂ) (Y : ℝ) (y₁ y₂ : ℝ) :
    Tg a P₂ g p q Y (y₁, y₂) = (y₁ : ℂ) ^ p * (Ω P₂ y₂ * (y₂ : ℂ) ^ q * E₂ a y₂) * e₁ a Y y₁ * g (Y * y₁ / y₂) := by
  simp only [Tg, Kq, Ω, E₂, mul_assoc]

theorem cpow_p_id {x : ℂ} (hx : x ≠ 0) (u₃ : ℂ) (δ : ℕ) :
    x ^ (-u₃ - 2 - (δ : ℂ)) = x ^ (-(u₃ + 2)) * (x ^ δ)⁻¹ := by
  rw [show -u₃ - 2 - (δ : ℂ) = -(u₃ + 2) + (-(δ : ℂ)) by ring, Complex.cpow_add _ _ hx, Complex.cpow_neg x (δ : ℂ),
    Complex.cpow_natCast]

theorem cpow_q_id {x : ℂ} (hx : x ≠ 0) (u₃ : ℂ) (n δ : ℕ) :
    x ^ ((n : ℂ) - u₃ - 1 - (δ : ℂ)) = x ^ (-(u₃ + 2)) * x ^ (n + 1) * (x ^ δ)⁻¹ := by
  have h : (n : ℂ) - u₃ - 1 - (δ : ℂ) = -(u₃ + 2) + ((n + 1 : ℕ) : ℂ) + (-(δ : ℂ)) := by push_cast; ring
  rw [h, Complex.cpow_add _ _ hx, Complex.cpow_add _ _ hx, Complex.cpow_neg x (δ : ℂ), Complex.cpow_natCast x (n + 1),
    Complex.cpow_natCast x δ]

end KernelT

section FoldQ

variable (a : ℚ) {P₂ : RealArchParam} (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (δ : ℕ)

def GQ (y y₁ y₂ : ℝ) : ℂ :=
  quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ *
    (((y₂ ^ 3 * ((y₁ * y₂)⁻¹) ^ δ * ((y₁ ^ 2)⁻¹ - (y₂ ^ 2)⁻¹ + 2 * (a : ℝ) * y * y₁ / y₂ - (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2 + (2 * Real.pi)⁻¹)) : ℝ) : ℂ) *
    (rexp (-(π * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
    (centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
    D.W (diagOne ((a : ℝ) * y * y₁ / y₂))

variable {a D u₃ a₃ δ}

theorem inv_mul_pow_eq (y₁ y₂ : ℝ) (δ : ℕ) : ((y₁ * y₂)⁻¹) ^ δ = (y₁ ^ δ)⁻¹ * (y₂ ^ δ)⁻¹ := by
  rw [mul_inv, mul_pow, inv_pow, inv_pow]

theorem neg_inv_mul_pow_eq (y₁ y₂ : ℝ) (δ : ℕ) : (-(y₁ * y₂)⁻¹) ^ δ = (-1 : ℝ) ^ δ * ((y₁ ^ δ)⁻¹ * (y₂ ^ δ)⁻¹) := by
  rw [neg_pow, inv_mul_pow_eq]

theorem eA {x : ℂ} (hx : x ≠ 0) (u₃ : ℂ) (δ : ℕ) :
    x ^ (-u₃ - 4 - (δ : ℂ)) = x ^ (-(u₃ + 2)) * (x ^ 2)⁻¹ * (x ^ δ)⁻¹ := by
  rw [show -u₃ - 4 - (δ : ℂ) = -(u₃ + 2) + (-(2 : ℂ)) + (-(δ : ℂ)) by ring, Complex.cpow_add _ _ hx,
    Complex.cpow_add _ _ hx, Complex.cpow_neg x (δ : ℂ), Complex.cpow_neg x (2 : ℂ), Complex.cpow_natCast, Complex.cpow_two]

theorem eB {x : ℂ} (hx : x ≠ 0) (u₃ : ℂ) (δ : ℕ) :
    x ^ (1 - u₃ - (δ : ℂ)) = x ^ (-(u₃ + 2)) * x ^ 3 * (x ^ δ)⁻¹ := by
  rw [show 1 - u₃ - (δ : ℂ) = -(u₃ + 2) + ((3 : ℕ) : ℂ) + (-(δ : ℂ)) by push_cast; ring, Complex.cpow_add _ _ hx,
    Complex.cpow_add _ _ hx, Complex.cpow_neg x (δ : ℂ), Complex.cpow_natCast x 3, Complex.cpow_natCast x δ]

theorem eD {x : ℂ} (hx : x ≠ 0) (u₃ : ℂ) (δ : ℕ) :
    x ^ (-1 - u₃ - (δ : ℂ)) = x ^ (-(u₃ + 2)) * x ^ 3 * (x ^ 2)⁻¹ * (x ^ δ)⁻¹ := by
  have h3 : x ^ 3 * (x ^ 2)⁻¹ = x := by field_simp
  rw [show -1 - u₃ - (δ : ℂ) = -(u₃ + 2) + (1 : ℂ) + (-(δ : ℂ)) by ring, Complex.cpow_add _ _ hx,
    Complex.cpow_add _ _ hx, Complex.cpow_neg x (δ : ℂ), Complex.cpow_natCast, Complex.cpow_one,
    show x ^ (-(u₃ + 2)) * x ^ 3 * (x ^ 2)⁻¹ * (x ^ δ)⁻¹ = x ^ (-(u₃ + 2)) * (x ^ 3 * (x ^ 2)⁻¹) * (x ^ δ)⁻¹ by ring, h3]

theorem eE {x : ℂ} (hx : x ≠ 0) (u₃ : ℂ) (δ : ℕ) :
    x ^ (-u₃ - 1 - (δ : ℂ)) = x ^ (-(u₃ + 2)) * x * (x ^ δ)⁻¹ := by
  rw [show -u₃ - 1 - (δ : ℂ) = -(u₃ + 2) + (1 : ℂ) + (-(δ : ℂ)) by ring, Complex.cpow_add _ _ hx,
    Complex.cpow_add _ _ hx, Complex.cpow_neg x (δ : ℂ), Complex.cpow_natCast, Complex.cpow_one]

theorem eF {x : ℂ} (hx : x ≠ 0) (u₃ : ℂ) (δ : ℕ) :
    x ^ (-u₃ - (δ : ℂ)) = x ^ (-(u₃ + 2)) * x ^ 3 * x⁻¹ * (x ^ δ)⁻¹ := by
  have h3 : x ^ 3 * x⁻¹ = x ^ 2 := by field_simp
  rw [show -u₃ - (δ : ℂ) = -(u₃ + 2) + (2 : ℂ) + (-(δ : ℂ)) by ring, Complex.cpow_add _ _ hx,
    Complex.cpow_add _ _ hx, Complex.cpow_neg x (δ : ℂ), Complex.cpow_natCast, Complex.cpow_two,
    show x ^ (-(u₃ + 2)) * x ^ 3 * x⁻¹ * (x ^ δ)⁻¹ = x ^ (-(u₃ + 2)) * (x ^ 3 * x⁻¹) * (x ^ δ)⁻¹ by ring, h3]

theorem eG {x : ℂ} (hx : x ≠ 0) (u₃ : ℂ) (δ : ℕ) :
    x ^ (-(δ : ℂ) - u₃) = x ^ (-(u₃ + 2)) * x ^ 2 * (x ^ δ)⁻¹ := by
  rw [show -(δ : ℂ) - u₃ = -(u₃ + 2) + (2 : ℂ) + (-(δ : ℂ)) by ring, Complex.cpow_add _ _ hx,
    Complex.cpow_add _ _ hx, Complex.cpow_neg x (δ : ℂ), Complex.cpow_natCast, Complex.cpow_two]

theorem GQ_four (c : ZMod 2)
    (hpar : ∀ τ : ℝ, τ ≠ 0 → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (ha : a ≠ 0) {y y₁ y₂ : ℝ} (hy : y ≠ 0) (hy₁ : 0 < y₁) (hy₂ : 0 < y₂) :
    (GQ a D u₃ a₃ δ y y₁ y₂ =
      (Tg a P₂ (gD a D) (-u₃ - 4 - (δ : ℂ)) (1 - u₃ - (δ : ℂ)) y (y₁, y₂) - Tg a P₂ (gD a D) (-u₃ - 2 - (δ : ℂ)) (-1 - u₃ - (δ : ℂ)) y (y₁, y₂)
        - (((a : ℝ) * y : ℝ) : ℂ) ^ 2 * Tg a P₂ (gD a D) (-(δ : ℂ) - u₃) (1 - u₃ - (δ : ℂ)) y (y₁, y₂)
        + (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * Tg a P₂ (gD a D) (-u₃ - 2 - (δ : ℂ)) (1 - u₃ - (δ : ℂ)) y (y₁, y₂))
      + (2 * (((a : ℝ) * y : ℝ) : ℂ) * Tg a P₂ (gD a D) (-u₃ - 1 - (δ : ℂ)) (-u₃ - (δ : ℂ)) y (y₁, y₂))) ∧
    (GQ a D u₃ a₃ δ y (-y₁) y₂ = (if a₃ = 0 then (1 : ℂ) else -1) * (-1 : ℂ) ^ δ * (-1 : ℂ) ^ c.val *
      ((Tg a P₂ (gD a D) (-u₃ - 4 - (δ : ℂ)) (1 - u₃ - (δ : ℂ)) y (y₁, y₂) - Tg a P₂ (gD a D) (-u₃ - 2 - (δ : ℂ)) (-1 - u₃ - (δ : ℂ)) y (y₁, y₂)
        - (((a : ℝ) * y : ℝ) : ℂ) ^ 2 * Tg a P₂ (gD a D) (-(δ : ℂ) - u₃) (1 - u₃ - (δ : ℂ)) y (y₁, y₂)
        + (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * Tg a P₂ (gD a D) (-u₃ - 2 - (δ : ℂ)) (1 - u₃ - (δ : ℂ)) y (y₁, y₂))
      - (2 * (((a : ℝ) * y : ℝ) : ℂ) * Tg a P₂ (gD a D) (-u₃ - 1 - (δ : ℂ)) (-u₃ - (δ : ℂ)) y (y₁, y₂)))) ∧
    (GQ a D u₃ a₃ δ (-y) y₁ y₂ = (-1 : ℂ) ^ c.val *
      ((Tg a P₂ (gD a D) (-u₃ - 4 - (δ : ℂ)) (1 - u₃ - (δ : ℂ)) y (y₁, y₂) - Tg a P₂ (gD a D) (-u₃ - 2 - (δ : ℂ)) (-1 - u₃ - (δ : ℂ)) y (y₁, y₂)
        - (((a : ℝ) * y : ℝ) : ℂ) ^ 2 * Tg a P₂ (gD a D) (-(δ : ℂ) - u₃) (1 - u₃ - (δ : ℂ)) y (y₁, y₂)
        + (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * Tg a P₂ (gD a D) (-u₃ - 2 - (δ : ℂ)) (1 - u₃ - (δ : ℂ)) y (y₁, y₂))
      - (2 * (((a : ℝ) * y : ℝ) : ℂ) * Tg a P₂ (gD a D) (-u₃ - 1 - (δ : ℂ)) (-u₃ - (δ : ℂ)) y (y₁, y₂)))) ∧
    (GQ a D u₃ a₃ δ (-y) (-y₁) y₂ = (if a₃ = 0 then (1 : ℂ) else -1) * (-1 : ℂ) ^ δ *
      ((Tg a P₂ (gD a D) (-u₃ - 4 - (δ : ℂ)) (1 - u₃ - (δ : ℂ)) y (y₁, y₂) - Tg a P₂ (gD a D) (-u₃ - 2 - (δ : ℂ)) (-1 - u₃ - (δ : ℂ)) y (y₁, y₂)
        - (((a : ℝ) * y : ℝ) : ℂ) ^ 2 * Tg a P₂ (gD a D) (-(δ : ℂ) - u₃) (1 - u₃ - (δ : ℂ)) y (y₁, y₂)
        + (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * Tg a P₂ (gD a D) (-u₃ - 2 - (δ : ℂ)) (1 - u₃ - (δ : ℂ)) y (y₁, y₂))
      + (2 * (((a : ℝ) * y : ℝ) : ℂ) * Tg a P₂ (gD a D) (-u₃ - 1 - (δ : ℂ)) (-u₃ - (δ : ℂ)) y (y₁, y₂)))) := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hτ : (a : ℝ) * (y * y₁ / y₂) ≠ 0 := mul_ne_zero ha' (div_ne_zero (mul_ne_zero hy hy₁.ne') hy₂.ne')
  have hF1 : Fp D (-((a : ℝ) * (y * y₁ / y₂))) = (-1 : ℂ) ^ c.val * Fp D ((a : ℝ) * (y * y₁ / y₂)) := hpar _ hτ
  have hy₁0 : (y₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₁.ne'
  have hy₂0 : (y₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy₂.ne'
  have hpm : 0 < y₁ * y₂ := mul_pos hy₁ hy₂

  have e0 : ∀ Y : ℝ, GQ a D u₃ a₃ δ Y y₁ y₂ =
      ((y₁ : ℂ) ^ (-(u₃ + 2)) * (y₂ : ℂ) ^ (-(u₃ + 2))) *
      (((y₂ ^ 3 * ((y₁ ^ δ)⁻¹ * (y₂ ^ δ)⁻¹) * ((y₁ ^ 2)⁻¹ - (y₂ ^ 2)⁻¹ + 2 * (a : ℝ) * Y * y₁ / y₂ - (a : ℝ) ^ 2 * Y ^ 2 * y₁ ^ 2 + (2 * Real.pi)⁻¹)) : ℝ) : ℂ) *
      (e₁ a Y y₁ * E₂ a y₂) * Ω P₂ y₂ * Fp D ((a : ℝ) * (Y * y₁ / y₂)) := by
    intro Y
    rw [GQ, quasiChar_of_pos _ _ (inv_pos.2 hpm), cpow_ofReal_inv' hpm, cpow_ofReal_mul' hy₁.le hy₂.le,
      inv_mul_pow_eq, exp_split, Ω, Fp, show (a : ℝ) * Y * y₁ / y₂ = (a : ℝ) * (Y * y₁ / y₂) by ring]
  have e1 : ∀ Y : ℝ, GQ a D u₃ a₃ δ Y (-y₁) y₂ =
      (if a₃ = 0 then (1 : ℂ) else -1) * ((y₁ : ℂ) ^ (-(u₃ + 2)) * (y₂ : ℂ) ^ (-(u₃ + 2))) *
      ((((-1 : ℝ) ^ δ * (y₂ ^ 3 * ((y₁ ^ δ)⁻¹ * (y₂ ^ δ)⁻¹)) * ((y₁ ^ 2)⁻¹ - (y₂ ^ 2)⁻¹ + 2 * (a : ℝ) * Y * (-y₁) / y₂ - (a : ℝ) ^ 2 * Y ^ 2 * y₁ ^ 2 + (2 * Real.pi)⁻¹)) : ℝ) : ℂ) *
      (e₁ a Y y₁ * E₂ a y₂) * Ω P₂ y₂ * Fp D (-((a : ℝ) * (Y * y₁ / y₂))) := by
    intro Y
    rw [GQ, show (-y₁ * y₂)⁻¹ = -((y₁ * y₂)⁻¹) by rw [neg_mul, inv_neg],
      quasiChar_neg_eq _ _ (inv_ne_zero hpm.ne'), quasiChar_of_pos _ _ (inv_pos.2 hpm), cpow_ofReal_inv' hpm,
      cpow_ofReal_mul' hy₁.le hy₂.le, neg_inv_mul_pow_eq, neg_sq, exp_split, Ω, Fp,
      show (a : ℝ) * Y * -y₁ / y₂ = -((a : ℝ) * (Y * y₁ / y₂)) by ring]
    push_cast; ring
  have hneg : (a : ℝ) * (-y * y₁ / y₂) = -((a : ℝ) * (y * y₁ / y₂)) := by ring
  rw [e0 y, e1 y, e0 (-y), e1 (-y), hneg, neg_neg, hF1]
  simp only [Tg_eq, e₁_neg, gD, eA hy₁0, eB hy₂0, cpow_p_id hy₁0, eD hy₂0, eE hy₁0, eF hy₂0, eG hy₁0]
  push_cast
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ring

end FoldQ

section Integr

variable (a : ℚ) (P₂ : RealArchParam)

local notation "μ0" => Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))

theorem ae_pos_prod' : ∀ᵐ q : ℝ × ℝ ∂((μ0).prod (μ0)), 0 < q.1 ∧ 0 < q.2 := by
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with q hq
  exact ⟨hq.1, hq.2⟩

theorem integrable_Tg_ae (ha : a ≠ 0) (g : ℝ → ℂ) (hgm : Measurable g) (C σF : ℝ) (hσF : 0 ≤ σF)
    (hg : ∀ t : ℝ, 0 < t → ‖g t‖ ≤ C * (1 + t ^ (-σF))) (p q : ℂ) :
    ∀ᵐ y : ℝ ∂(μ0), Integrable (fun w : ℝ × ℝ => Tg a P₂ g p q y w) ((μ0).prod (μ0)) := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hb : 0 < (a : ℝ) ^ 2 := by positivity
  obtain ⟨σ₀, hcore⟩ :=
    LanglandsTunnell.exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin
      ((a : ℝ) ^ 2) hb p g hgm C σF hσF hg (Kq a P₂ q) (measurable_Kq a P₂ q) 1
      |P₂.centralExponent.re + 1 + q.re| (norm_Kq_le a P₂ q) _ rfl
  set s : ℂ := ((max σ₀ 0 + 1 : ℝ) : ℂ) with hs
  have hsre : σ₀ < s.re := by rw [hs, Complex.ofReal_re]; linarith [le_max_left σ₀ 0]
  have hI := (hcore s hsre).1
  filter_upwards [hI.prod_right_ae, ae_restrict_mem measurableSet_Ioi] with y hy hy0
  have hy0' : (0:ℝ) < y := hy0
  have hc : ((y : ℝ) : ℂ) ^ (s - 2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl (Complex.ofReal_ne_zero.2 hy0'.ne')
  have h2 := hy.const_mul ((((y : ℝ) : ℂ) ^ (s - 2))⁻¹)
  refine h2.congr (ae_of_all _ fun w => ?_)
  show (((y : ℝ) : ℂ) ^ (s - 2))⁻¹ * (((y : ℝ) : ℂ) ^ (s - 2) * (((w.1 : ℝ) : ℂ) ^ p * Kq a P₂ q w.2 *
    (rexp (-(π * ((w.1 ^ 2)⁻¹ + (a : ℝ) ^ 2 * y ^ 2 * w.1 ^ 2))) : ℂ) * g (y * w.1 / w.2))) = Tg a P₂ g p q y w
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rfl

end Integr

section FoldMainQ

variable (a : ℚ) {P₂ : RealArchParam} (D : ArchDatumR P₂) (u₃ : ℂ) (a₃ : ZMod 2) (δ : ℕ)

local notation "μ0" => Measure.restrict (volume : Measure ℝ) (Ioi (0:ℝ))

theorem ite_mul_neg_one_pow_eq (a₃ : ZMod 2) (δ : ℕ) :
    (if a₃ = 0 then (1 : ℂ) else -1) * (-1 : ℂ) ^ δ = (-1 : ℂ) ^ (a₃.val + δ) := by
  rw [ite_eq_neg_one_pow, pow_add]

theorem sign_odd (a₃ c : ZMod 2) (δ : ℕ) (hodd : ((δ : ℕ) : ZMod 2) = a₃ + c + 1) :
    (-1 : ℂ) ^ (a₃.val + δ) * (-1 : ℂ) ^ c.val = -1 := by
  have h2 : ∀ x : ZMod 2, x + x = 0 := by intro x; fin_cases x <;> decide
  have h : ((a₃.val + δ + c.val : ℕ) : ZMod 2) = 1 := by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hodd]
    calc a₃ + (a₃ + c + 1) + c = (a₃ + a₃) + (c + c) + 1 := by ring
      _ = 1 := by rw [h2, h2, zero_add, zero_add]
  have hm : (a₃.val + δ + c.val) % 2 = 1 := by
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast] at this
  rw [← pow_add, neg_one_pow_eq_pow_mod_two, hm, pow_one]

theorem foldQ (c : ZMod 2) (ha : a ≠ 0)
    (hpar : ∀ τ : ℝ, τ ≠ 0 → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (hodd : ((δ : ℕ) : ZMod 2) = a₃ + c + 1) (Φ : ℝ → ℂ)
    (hΦ : ∀ Y : ℝ, Y ≠ 0 → Φ Y = 2 * (Real.pi : ℂ) * (a : ℂ) ^ 2 *
      ∫ y₁ : ℝ, ∫ y₂ in Ioi (0:ℝ), GQ a D u₃ a₃ δ Y y₁ y₂)
    {y : ℝ} (hy : 0 < y)
    (h1 : Integrable (fun w : ℝ × ℝ => Tg a P₂ (gD a D) (-u₃ - 4 - (δ : ℂ)) (1 - u₃ - (δ : ℂ)) y w) ((μ0).prod (μ0)))
    (h2 : Integrable (fun w : ℝ × ℝ => Tg a P₂ (gD a D) (-u₃ - 2 - (δ : ℂ)) (-1 - u₃ - (δ : ℂ)) y w) ((μ0).prod (μ0)))
    (h3 : Integrable (fun w : ℝ × ℝ => Tg a P₂ (gD a D) (-u₃ - 1 - (δ : ℂ)) (-u₃ - (δ : ℂ)) y w) ((μ0).prod (μ0)))
    (h4 : Integrable (fun w : ℝ × ℝ => Tg a P₂ (gD a D) (-(δ : ℂ) - u₃) (1 - u₃ - (δ : ℂ)) y w) ((μ0).prod (μ0)))
    (h5 : Integrable (fun w : ℝ × ℝ => Tg a P₂ (gD a D) (-u₃ - 2 - (δ : ℂ)) (1 - u₃ - (δ : ℂ)) y w) ((μ0).prod (μ0))) :
    Φ y + (-1 : ℂ) ^ (a₃.val + δ) * Φ (-y) =
      16 * (Real.pi : ℂ) * (a : ℂ) ^ 3 * (y : ℂ) * ∫ y₁ in Ioi (0:ℝ), ∫ y₂ in Ioi (0:ℝ),
        Tg a P₂ (gD a D) (-u₃ - 1 - (δ : ℂ)) (-u₃ - (δ : ℂ)) y (y₁, y₂) := by
  set ε' : ℂ := (-1 : ℂ) ^ (a₃.val + δ) with hε'
  set εc : ℂ := (-1 : ℂ) ^ c.val with hεc
  have hε : (if a₃ = 0 then (1 : ℂ) else -1) * (-1 : ℂ) ^ δ = ε' := by rw [ite_mul_neg_one_pow_eq]
  have hεε : ε' * ε' = 1 := by rw [hε', ← pow_add, ← two_mul, pow_mul]; norm_num
  have hodd' : ε' * εc = -1 := sign_odd a₃ c δ hodd
  set κ₃ : ℂ := (((a : ℝ) * y : ℝ) : ℂ) with hκ₃
  set T1 : ℝ × ℝ → ℂ := fun w => Tg a P₂ (gD a D) (-u₃ - 4 - (δ : ℂ)) (1 - u₃ - (δ : ℂ)) y w with hT1
  set T2 : ℝ × ℝ → ℂ := fun w => Tg a P₂ (gD a D) (-u₃ - 2 - (δ : ℂ)) (-1 - u₃ - (δ : ℂ)) y w with hT2
  set T3 : ℝ × ℝ → ℂ := fun w => Tg a P₂ (gD a D) (-u₃ - 1 - (δ : ℂ)) (-u₃ - (δ : ℂ)) y w with hT3
  set T4 : ℝ × ℝ → ℂ := fun w => Tg a P₂ (gD a D) (-(δ : ℂ) - u₃) (1 - u₃ - (δ : ℂ)) y w with hT4
  set T5 : ℝ × ℝ → ℂ := fun w => Tg a P₂ (gD a D) (-u₃ - 2 - (δ : ℂ)) (1 - u₃ - (δ : ℂ)) y w with hT5
  set Ef : ℝ × ℝ → ℂ := fun w => T1 w - T2 w - κ₃ ^ 2 * T4 w + (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * T5 w with hEf
  set Of : ℝ × ℝ → ℂ := fun w => 2 * κ₃ * T3 w with hOf
  have iE : Integrable Ef ((μ0).prod (μ0)) := ((h1.sub h2).sub (h4.const_mul _)).add (h5.const_mul _)
  have iO : Integrable Of ((μ0).prod (μ0)) := h3.const_mul _
  have four : ∀ w : ℝ × ℝ, 0 < w.1 ∧ 0 < w.2 →
      GQ a D u₃ a₃ δ y w.1 w.2 = Ef w + Of w ∧
      GQ a D u₃ a₃ δ y (-w.1) w.2 = ε' * εc * (Ef w - Of w) ∧
      GQ a D u₃ a₃ δ (-y) w.1 w.2 = εc * (Ef w - Of w) ∧
      GQ a D u₃ a₃ δ (-y) (-w.1) w.2 = ε' * (Ef w + Of w) := by
    intro w hw
    have h := GQ_four (a := a) (D := D) (u₃ := u₃) (a₃ := a₃) (δ := δ) c hpar ha hy.ne' hw.1 hw.2
    rw [hε] at h
    exact h
  have hA₁ : Integrable (fun w : ℝ × ℝ => GQ a D u₃ a₃ δ y w.1 w.2) ((μ0).prod (μ0)) := by
    refine (iE.add iO).congr ?_
    filter_upwards [ae_pos_prod'] with w hw
    rw [(four w hw).1]; rfl
  have hA₂ : Integrable (fun w : ℝ × ℝ => GQ a D u₃ a₃ δ y (-w.1) w.2) ((μ0).prod (μ0)) := by
    refine ((iE.sub iO).const_mul (ε' * εc)).congr ?_
    filter_upwards [ae_pos_prod'] with w hw
    rw [(four w hw).2.1]; rfl
  have hA₃ : Integrable (fun w : ℝ × ℝ => GQ a D u₃ a₃ δ (-y) w.1 w.2) ((μ0).prod (μ0)) := by
    refine ((iE.sub iO).const_mul εc).congr ?_
    filter_upwards [ae_pos_prod'] with w hw
    rw [(four w hw).2.2.1]; rfl
  have hA₄ : Integrable (fun w : ℝ × ℝ => GQ a D u₃ a₃ δ (-y) (-w.1) w.2) ((μ0).prod (μ0)) := by
    refine ((iE.add iO).const_mul ε').congr ?_
    filter_upwards [ae_pos_prod'] with w hw
    rw [(four w hw).2.2.2]; rfl

  set Hp : ℝ → ℂ := fun y₁ => ∫ y₂ in Ioi (0:ℝ), GQ a D u₃ a₃ δ y y₁ y₂ with hHp
  set Hm : ℝ → ℂ := fun y₁ => ∫ y₂ in Ioi (0:ℝ), GQ a D u₃ a₃ δ (-y) y₁ y₂ with hHm
  have iHp : IntegrableOn Hp (Ioi 0) := hA₁.integral_prod_left
  have iHpn : IntegrableOn (fun y₁ => Hp (-y₁)) (Ioi 0) := hA₂.integral_prod_left
  have iHm : IntegrableOn Hm (Ioi 0) := hA₃.integral_prod_left
  have iHmn : IntegrableOn (fun y₁ => Hm (-y₁)) (Ioi 0) := hA₄.integral_prod_left
  have toIic : ∀ F : ℝ → ℂ, IntegrableOn (fun y₁ => F (-y₁)) (Ioi 0) → IntegrableOn F (Iic 0) := by
    intro F hF
    have h' : IntegrableOn F (Iio 0) := by
      rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
        (Homeomorph.neg ℝ).measurableEmbedding]
      simpa only [Function.comp_def, neg_preimage, neg_Iio, neg_zero] using hF
    exact h'.congr_set_ae Iio_ae_eq_Iic.symm
  have splitP : ∫ y₁ : ℝ, Hp y₁ = (∫ y₁ in Ioi (0:ℝ), Hp (-y₁)) + ∫ y₁ in Ioi (0:ℝ), Hp y₁ := by
    rw [← intervalIntegral.integral_Iic_add_Ioi (toIic Hp iHpn) iHp, ← neg_zero, ← integral_comp_neg_Ioi 0 Hp, neg_zero]
  have splitM : ∫ y₁ : ℝ, Hm y₁ = (∫ y₁ in Ioi (0:ℝ), Hm (-y₁)) + ∫ y₁ in Ioi (0:ℝ), Hm y₁ := by
    rw [← intervalIntegral.integral_Iic_add_Ioi (toIic Hm iHmn) iHm, ← neg_zero, ← integral_comp_neg_Ioi 0 Hm, neg_zero]
  rw [hΦ y hy.ne', hΦ (-y) (neg_ne_zero.2 hy.ne')]
  change 2 * (Real.pi : ℂ) * (a : ℂ) ^ 2 * (∫ y₁ : ℝ, Hp y₁) +
    ε' * (2 * (Real.pi : ℂ) * (a : ℂ) ^ 2 * ∫ y₁ : ℝ, Hm y₁) = _
  rw [splitP, splitM]
  have hsum : ∫ y₁ in Ioi (0:ℝ), (Hp (-y₁) + Hp y₁ + ε' * (Hm (-y₁) + Hm y₁)) =
      ((∫ y₁ in Ioi (0:ℝ), Hp (-y₁)) + ∫ y₁ in Ioi (0:ℝ), Hp y₁) +
        ε' * ((∫ y₁ in Ioi (0:ℝ), Hm (-y₁)) + ∫ y₁ in Ioi (0:ℝ), Hm y₁) := by
    have hI12 : IntegrableOn (fun y₁ => Hp (-y₁) + Hp y₁) (Ioi 0) := iHpn.add iHp
    have hI34 : IntegrableOn (fun y₁ => ε' * (Hm (-y₁) + Hm y₁)) (Ioi 0) := (iHmn.add iHm).const_mul ε'
    rw [integral_add hI12 hI34, integral_add iHpn iHp, integral_const_mul, integral_add iHmn iHm]
  have hinner : ∀ᵐ y₁ : ℝ ∂(μ0), Hp (-y₁) + Hp y₁ + ε' * (Hm (-y₁) + Hm y₁) =
      ∫ y₂ in Ioi (0:ℝ), (4 : ℂ) * Of (y₁, y₂) := by
    filter_upwards [hA₁.prod_right_ae, hA₂.prod_right_ae, hA₃.prod_right_ae, hA₄.prod_right_ae,
      ae_restrict_mem measurableSet_Ioi] with y₁ i1 i2 i3 i4 hy₁
    have hy₁' : (0:ℝ) < y₁ := hy₁
    have eq1 : ∫ y₂ in Ioi (0:ℝ), (GQ a D u₃ a₃ δ y (-y₁) y₂ + GQ a D u₃ a₃ δ y y₁ y₂ +
        ε' * (GQ a D u₃ a₃ δ (-y) (-y₁) y₂ + GQ a D u₃ a₃ δ (-y) y₁ y₂)) =
        Hp (-y₁) + Hp y₁ + ε' * (Hm (-y₁) + Hm y₁) := by
      have hI12 : Integrable (fun y₂ => GQ a D u₃ a₃ δ y (-y₁) y₂ + GQ a D u₃ a₃ δ y y₁ y₂) (μ0) := i2.add i1
      have hI34 : Integrable (fun y₂ => ε' * (GQ a D u₃ a₃ δ (-y) (-y₁) y₂ + GQ a D u₃ a₃ δ (-y) y₁ y₂)) (μ0) :=
        (i4.add i3).const_mul ε'
      rw [integral_add hI12 hI34, integral_add i2 i1, integral_const_mul, integral_add i4 i3]
    rw [← eq1]
    refine setIntegral_congr_fun measurableSet_Ioi fun y₂ (hy₂ : 0 < y₂) => ?_
    obtain ⟨q1, q2, q3, q4⟩ := four (y₁, y₂) ⟨hy₁', hy₂⟩
    simp only at q1 q2 q3 q4
    rw [q1, q2, q3, q4]
    linear_combination (2 * (Ef (y₁, y₂) - Of (y₁, y₂))) * hodd' + (Ef (y₁, y₂) + Of (y₁, y₂)) * hεε
  calc 2 * (Real.pi : ℂ) * (a : ℂ) ^ 2 * ((∫ y₁ in Ioi (0:ℝ), Hp (-y₁)) + ∫ y₁ in Ioi (0:ℝ), Hp y₁) +
        ε' * (2 * (Real.pi : ℂ) * (a : ℂ) ^ 2 * ((∫ y₁ in Ioi (0:ℝ), Hm (-y₁)) + ∫ y₁ in Ioi (0:ℝ), Hm y₁))
      = 2 * (Real.pi : ℂ) * (a : ℂ) ^ 2 * (((∫ y₁ in Ioi (0:ℝ), Hp (-y₁)) + ∫ y₁ in Ioi (0:ℝ), Hp y₁) +
          ε' * ((∫ y₁ in Ioi (0:ℝ), Hm (-y₁)) + ∫ y₁ in Ioi (0:ℝ), Hm y₁)) := by ring
    _ = 2 * (Real.pi : ℂ) * (a : ℂ) ^ 2 * ∫ y₁ in Ioi (0:ℝ), ∫ y₂ in Ioi (0:ℝ), (4 : ℂ) * Of (y₁, y₂) := by
        rw [← hsum, integral_congr_ae hinner]
    _ = 16 * (Real.pi : ℂ) * (a : ℂ) ^ 3 * (y : ℂ) * ∫ y₁ in Ioi (0:ℝ), ∫ y₂ in Ioi (0:ℝ), T3 (y₁, y₂) := by
        have : ∀ y₁ : ℝ, ∫ y₂ in Ioi (0:ℝ), (4 : ℂ) * Of (y₁, y₂) = (4 * (2 * κ₃)) * ∫ y₂ in Ioi (0:ℝ), T3 (y₁, y₂) := by
          intro y₁
          rw [← integral_const_mul]
          refine integral_congr_ae (ae_of_all _ fun y₂ => ?_)
          simp only [hOf]; ring
        simp_rw [this]
        rw [integral_const_mul, hκ₃]
        push_cast
        ring

end FoldMainQ

theorem quadSection_mem_polyGauss3 (δ : ℕ) (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ)) ^ δ *
        ((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) ^ 2 + (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ)) ^ 2) *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ 2) * gaussian3 M) :
    S ∈ polyGauss3 := by
  refine ⟨(MvPolynomial.X (0, 0) * MvPolynomial.X (1, 1) - MvPolynomial.X (0, 1) * MvPolynomial.X (1, 0)) ^ δ *
    ((MvPolynomial.X (0, 0) + MvPolynomial.C Complex.I * MvPolynomial.X (1, 0)) ^ 2 +
      (MvPolynomial.X (0, 1) + MvPolynomial.C Complex.I * MvPolynomial.X (1, 1)) ^ 2) *
    (MvPolynomial.X (0, 2) - MvPolynomial.C Complex.I * MvPolynomial.X (1, 2)) ^ 2, ?_⟩
  funext M
  simp only [hS, map_mul, map_sub, map_add, map_pow, MvPolynomial.eval_X, MvPolynomial.eval_C, Complex.ofReal_mul,
    Complex.ofReal_sub]

end Z0Q

end

theorem solution
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (u₃ : ℂ) (a₃ : ZMod 2) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ)) ^ δ *
        ((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) ^ 2 + (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ)) ^ 2) *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ 2) * gaussian3 M)
    (u₁ u₂ : ℂ) (c : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c u₂ c)
    (hpar : ∀ τ : ℝ, τ ≠ 0 → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (hodd : ((δ : ℕ) : ZMod 2) = a₃ + c + 1)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (κ : ℝ)
    (hκ : MeasureTheory.Measure.map
        (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
      ENNReal.ofReal κ • (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
        fun y => ENNReal.ofReal |y|⁻¹)
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (e : ℤ)
    (hσ : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v 0 e)
    (he : ((e : ZMod 2)) = a₃ + ((δ : ℕ) : ZMod 2))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          D.W (ArchR.diagOne ((a : ℝ) * (σ' / w))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ (-u₃ - (δ : ℂ)) *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ)) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      MellinConvergent H s ∧
        archZeta30 ν_mul (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) (σ.comp E) s 1 =
          (κ : ℂ) * (8 * (Real.pi : ℂ) * (a : ℂ) ^ 3) * Complex.Gammaℝ (s + u₃ + (δ : ℂ)) * mellin H s := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hb : 0 < (a : ℝ) ^ 2 := by positivity
  have hSpg : S ∈ polyGauss3 := Z0Q.quadSection_mem_polyGauss3 δ S hS
  obtain ⟨C₁, σ₁, hσ₁, hg₁⟩ := Z0Q.exists_bound_gD a D ha
  have hH' : H = fun σ' => (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * σ' ^ 2)) : ℂ) *
      ∫ w in Set.Ioi (0 : ℝ), Z0Q.gD a D (σ' / w) * Z0Q.Kq a P₂ (-u₃ - (δ : ℂ)) w := by
    rw [hH]
    funext σ'
    congr 1
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only [Z0Q.gD, Z0Q.Fp, Z0Q.Kq]
    ring
  obtain ⟨σB, hcore⟩ :=
    LanglandsTunnell.exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin
      ((a : ℝ) ^ 2) hb (-u₃ - 1 - (δ : ℂ)) (Z0Q.gD a D) (Z0Q.measurable_gD a D) C₁ σ₁ hσ₁ hg₁
      (Z0Q.Kq a P₂ (-u₃ - (δ : ℂ))) (Z0Q.measurable_Kq a P₂ _) 1 |P₂.centralExponent.re + 1 + (-u₃ - (δ : ℂ)).re|
      (Z0Q.norm_Kq_le a P₂ _) H hH'
  have i1 := Z0Q.integrable_Tg_ae a P₂ ha (Z0Q.gD a D) (Z0Q.measurable_gD a D) C₁ σ₁ hσ₁ hg₁ (-u₃ - 4 - (δ : ℂ)) (1 - u₃ - (δ : ℂ))
  have i2 := Z0Q.integrable_Tg_ae a P₂ ha (Z0Q.gD a D) (Z0Q.measurable_gD a D) C₁ σ₁ hσ₁ hg₁ (-u₃ - 2 - (δ : ℂ)) (-1 - u₃ - (δ : ℂ))
  have i3 := Z0Q.integrable_Tg_ae a P₂ ha (Z0Q.gD a D) (Z0Q.measurable_gD a D) C₁ σ₁ hσ₁ hg₁ (-u₃ - 1 - (δ : ℂ)) (-u₃ - (δ : ℂ))
  have i4 := Z0Q.integrable_Tg_ae a P₂ ha (Z0Q.gD a D) (Z0Q.measurable_gD a D) C₁ σ₁ hσ₁ hg₁ (-(δ : ℂ) - u₃) (1 - u₃ - (δ : ℂ))
  have i5 := Z0Q.integrable_Tg_ae a P₂ ha (Z0Q.gD a D) (Z0Q.measurable_gD a D) C₁ σ₁ hσ₁ hg₁ (-u₃ - 2 - (δ : ℂ)) (1 - u₃ - (δ : ℂ))
  have hΦ : ∀ Y : ℝ, Y ≠ 0 → Ws23Z0.Phi a psiInf D u₃ a₃ S Y =
      2 * (Real.pi : ℂ) * (a : ℂ) ^ 2 * ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ), Z0Q.GQ a D u₃ a₃ δ Y y₁ y₂ :=
    fun Y hY => LanglandsTunnell.CubicInduction.jacquetVector3_one_eq_integral_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_weightZero
      a ha psiInf hpsiInf D hDW0 u₃ a₃ δ S hS Y hY
  refine ⟨max (Ws23Z0.q₀ P₂ u₃) σB, fun s hs => ?_⟩
  have hs1 : Ws23Z0.q₀ P₂ u₃ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs2 : σB < (s + 1).re := by
    have h' := lt_of_le_of_lt (le_max_right (Ws23Z0.q₀ P₂ u₃) σB) hs
    rw [Complex.add_re, Complex.one_re]; linarith
  obtain ⟨-, hZ⟩ := Ws23Z0.archZeta30_jacquetVector3_eq a ha psiInf hpsiInf D u₃ a₃ S hSpg ν_mul κ hκ σ e hσ E hE s hs1
  obtain ⟨-, hMC, hId⟩ := hcore (s + 1) hs2
  rw [show s + 1 - 1 = s by ring] at hMC hId
  refine ⟨hMC, ?_⟩
  rw [hZ]
  have hεe : (-1 : ℂ) ^ (e : ZMod 2).val = (-1 : ℂ) ^ (a₃.val + δ) := by
    rw [he, neg_one_pow_eq_pow_mod_two (n := a₃.val + δ)]
    congr 1
    rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod]
  have hfold : ∀ᵐ y : ℝ ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      (Ws23Z0.Phi a psiInf D u₃ a₃ S y + (-1 : ℂ) ^ (e : ZMod 2).val * Ws23Z0.Phi a psiInf D u₃ a₃ S (-y)) *
          ((y : ℝ) : ℂ) ^ (s - 2) =
        (16 * (Real.pi : ℂ) * (a : ℂ) ^ 3) * (((y : ℝ) : ℂ) ^ (s + 1 - 2) *
          ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
            ((y₁ : ℝ) : ℂ) ^ (-u₃ - 1 - (δ : ℂ)) * Z0Q.Kq a P₂ (-u₃ - (δ : ℂ)) y₂ *
              (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) * Z0Q.gD a D (y * y₁ / y₂)) := by
    filter_upwards [i1, i2, i3, i4, i5, ae_restrict_mem measurableSet_Ioi] with y h1 h2 h3 h4 h5 hy
    have hy' : (0 : ℝ) < y := hy
    have hy0 : ((y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy'.ne'
    have hy1 : ((y : ℝ) : ℂ) ^ (s + 1 - 2) = ((y : ℝ) : ℂ) ^ (s - 2) * ((y : ℝ) : ℂ) := by
      rw [show s + 1 - 2 = (s - 2) + 1 by ring, Complex.cpow_add _ _ hy0, Complex.cpow_one]
    rw [hεe, Z0Q.foldQ a D u₃ a₃ δ c ha hpar hodd (Ws23Z0.Phi a psiInf D u₃ a₃ S) hΦ hy' h1 h2 h3 h4 h5, hy1]
    simp only [Z0Q.Tg, Z0Q.e₁]
    ring
  rw [integral_congr_ae hfold, integral_const_mul, hId, show s + 1 - (-u₃ - 1 - (δ : ℂ)) - 2 = s + u₃ + (δ : ℂ) by ring]
  ring

#print axioms solution

end S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_weightZero
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_weightZero (solution)
