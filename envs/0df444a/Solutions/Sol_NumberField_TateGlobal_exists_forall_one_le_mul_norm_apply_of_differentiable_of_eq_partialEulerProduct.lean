-- Prove2me | solution 1 for NumberField.TateGlobal.exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/fdc6acc0-73f1-5151-afe4-d8b0474f8031

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Theorems.Thm_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Theorems.Thm_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
import Theorems.Thm_NumberField_TateGlobal_exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc
import Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc
import Theorems.Thm_NumberField_TateGlobal_exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct
import Theorems.Thm_NumberField_TateGlobal_exists_finset_forall_isUnramifiedCharAt_of_continuous
import Definitions.Def_NumberField_NormPowChar
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq"
p2m_attr_erase "simp" "LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.TateLocal.conductorExponentAt_one LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec"

set_option Elab.async false
set_option autoImplicit false

namespace LineLowerBound
section
open Complex Filter Topology

private theorem exists_pos_forall_le_pow_mul (C C' : ℝ) (M M' : ℕ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (X : ℝ → ℝ) (y : ℝ), (∀ σ, 0 ≤ X σ) →
      (∀ σ : ℝ, 1 < σ → σ ≤ 2 → (σ - 1) ^ 3 ≤ C * (1 + |y|) ^ M * X σ ^ 4) →
      (∀ σ σ' : ℝ, 1 ≤ σ → σ ≤ 2 → 1 ≤ σ' → σ' ≤ 2 →
        |X σ - X σ'| ≤ C' * (1 + |y|) ^ M' * |σ - σ'|) →
      ∀ σ₀ : ℝ, 1 ≤ σ₀ → σ₀ ≤ 2 → c₀ ≤ (1 + |y|) ^ (3 * M' + M) * X σ₀ := by

  set C₁ : ℝ := max C 1 with hC₁
  set C₁' : ℝ := max C' 1 with hC₁'
  have hC₁1 : 1 ≤ C₁ := le_max_right _ _
  have hC₁'1 : 1 ≤ C₁' := le_max_right _ _
  set K : ℝ := 16 * C₁ * C₁' ^ 4 + 1 with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ 16 * C₁ * C₁' ^ 4 := by positivity
    linarith
  have hK0 : 0 < K := by linarith
  set c₁ : ℝ := 1 / (C₁ * K ^ 3) with hc₁
  have hc₁0 : 0 < c₁ := by positivity
  have hc₁1 : c₁ ≤ 1 := by
    rw [hc₁, div_le_one (by positivity)]
    have : 1 ≤ K ^ 3 := one_le_pow₀ hK1
    nlinarith
  refine ⟨c₁ / 2, by positivity, ?_⟩
  intro X y hX0 h1 h2 σ₀ hσ₀ hσ₀'
  set D : ℝ := 1 + |y| with hD
  have hD1 : 1 ≤ D := by have := abs_nonneg y; linarith
  have hD0 : 0 < D := by linarith

  have h1' : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → (σ - 1) ^ 3 ≤ C₁ * D ^ M * X σ ^ 4 := by
    intro σ hσ hσ2
    refine (h1 σ hσ hσ2).trans ?_
    have : 0 ≤ D ^ M * X σ ^ 4 := by positivity
    calc C * (1 + |y|) ^ M * X σ ^ 4 = C * (D ^ M * X σ ^ 4) := by rw [hD]; ring
      _ ≤ C₁ * (D ^ M * X σ ^ 4) := mul_le_mul_of_nonneg_right (le_max_left _ _) this
      _ = C₁ * D ^ M * X σ ^ 4 := by ring
  have h2' : ∀ σ σ' : ℝ, 1 ≤ σ → σ ≤ 2 → 1 ≤ σ' → σ' ≤ 2 →
      |X σ - X σ'| ≤ C₁' * D ^ M' * |σ - σ'| := by
    intro σ σ' a b c d
    refine (h2 σ σ' a b c d).trans ?_
    have : 0 ≤ D ^ M' * |σ - σ'| := by positivity
    calc C' * (1 + |y|) ^ M' * |σ - σ'| = C' * (D ^ M' * |σ - σ'|) := by rw [hD]; ring
      _ ≤ C₁' * (D ^ M' * |σ - σ'|) := mul_le_mul_of_nonneg_right (le_max_left _ _) this
      _ = C₁' * D ^ M' * |σ - σ'| := by ring

  set P : ℝ := D ^ (4 * M' + M) with hP
  have hP1 : 1 ≤ P := one_le_pow₀ hD1
  have hP0 : 0 < P := by linarith
  set δ : ℝ := 1 / (K * P) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]
    nlinarith
  have hδKP : δ * (K * P) = 1 := by
    rw [hδ]; field_simp

  have hexp : D ^ (12 * M' + 4 * M) = P ^ 3 * D ^ M := by
    rw [hP, ← pow_mul, ← pow_add]; congr 1; ring
  have hexp4 : (D ^ (3 * M' + M)) ^ 4 = D ^ (12 * M' + 4 * M) := by
    rw [← pow_mul]; congr 1; ring

  have claimA : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → δ ≤ σ - 1 → c₁ ≤ D ^ (3 * M' + M) * X σ := by
    intro σ hσ hσ2 hδσ
    have hA := h1' σ hσ hσ2

    have hδ3 : δ ^ 3 ≤ C₁ * D ^ M * X σ ^ 4 := (pow_le_pow_left₀ hδ0.le hδσ 3).trans hA

    have hone : 1 ≤ C₁ * K ^ 3 * (D ^ (12 * M' + 4 * M) * X σ ^ 4) := by
      have hKP3 : 0 ≤ (K * P) ^ 3 := by positivity
      have := mul_le_mul_of_nonneg_right hδ3 hKP3
      have hl : δ ^ 3 * (K * P) ^ 3 = 1 := by rw [← mul_pow, hδKP, one_pow]
      rw [hl] at this
      calc (1 : ℝ) ≤ C₁ * D ^ M * X σ ^ 4 * (K * P) ^ 3 := this
        _ = C₁ * K ^ 3 * (P ^ 3 * D ^ M * X σ ^ 4) := by ring
        _ = C₁ * K ^ 3 * (D ^ (12 * M' + 4 * M) * X σ ^ 4) := by rw [hexp]
    have hc₁le : c₁ ≤ D ^ (12 * M' + 4 * M) * X σ ^ 4 := by
      rw [hc₁, div_le_iff₀ (by positivity)]
      calc (1 : ℝ) ≤ C₁ * K ^ 3 * (D ^ (12 * M' + 4 * M) * X σ ^ 4) := hone
        _ = D ^ (12 * M' + 4 * M) * X σ ^ 4 * (C₁ * K ^ 3) := by ring

    have hc₁4 : c₁ ^ 4 ≤ (D ^ (3 * M' + M) * X σ) ^ 4 := by
      have : c₁ ^ 4 ≤ c₁ := pow_le_of_le_one hc₁0.le hc₁1 (by norm_num)
      refine this.trans ?_
      rw [mul_pow, hexp4]
      exact hc₁le
    exact le_of_pow_le_pow_left₀ (by norm_num) (mul_nonneg (by positivity) (hX0 σ)) hc₁4

  have hc₁D0 : 0 ≤ D ^ (3 * M' + M) * X σ₀ := mul_nonneg (by positivity) (hX0 σ₀)
  by_cases hcase : 1 + δ < σ₀
  ·
    have h := claimA σ₀ (by linarith) hσ₀' (by linarith)
    have hc : c₁ / 2 ≤ c₁ := by linarith
    rw [hD] at h
    linarith
  ·
    push Not at hcase
    set σ₁ : ℝ := 1 + δ with hσ₁
    have hσ₁1 : 1 < σ₁ := by linarith
    have hσ₁2 : σ₁ ≤ 2 := by linarith
    have hA1 := claimA σ₁ hσ₁1 hσ₁2 (by linarith)
    have hB1 := h1' σ₁ hσ₁1 hσ₁2

    set e : ℝ := C₁' * D ^ M' * δ with he
    have he0 : 0 ≤ e := by positivity
    have hlip : X σ₁ - e ≤ X σ₀ := by
      have h := h2' σ₀ σ₁ hσ₀ hσ₀' hσ₁1.le hσ₁2
      have habs : |σ₀ - σ₁| ≤ δ := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
      have : |X σ₀ - X σ₁| ≤ e := by
        refine h.trans ?_
        rw [he]
        exact mul_le_mul_of_nonneg_left habs (by positivity)
      have := (abs_sub_comm (X σ₀) (X σ₁)).symm ▸ this
      linarith [(abs_le.mp this).2, (abs_le.mp this).1, abs_sub_comm (X σ₀) (X σ₁)]

    have he4 : e ^ 4 ≤ (X σ₁ / 2) ^ 4 := by

      have hδ3 : δ ^ 3 ≤ C₁ * D ^ M * X σ₁ ^ 4 := by
        have : (σ₁ - 1) ^ 3 = δ ^ 3 := by rw [hσ₁]; ring
        rw [← this]; exact hB1
      have hkey : 16 * e ^ 4 * (C₁ * D ^ M) ≤ δ ^ 3 := by

        have hsmall : 16 * C₁ * C₁' ^ 4 * P * δ ≤ 1 := by
          have : 16 * C₁ * C₁' ^ 4 ≤ K := by rw [hK]; linarith
          calc 16 * C₁ * C₁' ^ 4 * P * δ ≤ K * P * δ := by
                have hPδ : 0 ≤ P * δ := by positivity
                nlinarith
            _ = 1 := by rw [← hδKP]; ring
        have hDpow : D ^ (4 * M') * D ^ M = P := by rw [hP, ← pow_add]
        calc 16 * e ^ 4 * (C₁ * D ^ M)
            = (16 * C₁ * C₁' ^ 4 * (D ^ (4 * M') * D ^ M) * δ) * δ ^ 3 := by
              rw [he]; ring
          _ = (16 * C₁ * C₁' ^ 4 * P * δ) * δ ^ 3 := by rw [hDpow]
          _ ≤ 1 * δ ^ 3 := mul_le_mul_of_nonneg_right hsmall (by positivity)
          _ = δ ^ 3 := one_mul _
      have hCD : 0 < C₁ * D ^ M := by positivity
      have : 16 * e ^ 4 ≤ X σ₁ ^ 4 := by
        have h16 : 16 * e ^ 4 * (C₁ * D ^ M) ≤ X σ₁ ^ 4 * (C₁ * D ^ M) := by
          calc 16 * e ^ 4 * (C₁ * D ^ M) ≤ δ ^ 3 := hkey
            _ ≤ C₁ * D ^ M * X σ₁ ^ 4 := hδ3
            _ = X σ₁ ^ 4 * (C₁ * D ^ M) := by ring
        exact le_of_mul_le_mul_right h16 hCD
      calc e ^ 4 = (16 * e ^ 4) / 16 := by ring
        _ ≤ X σ₁ ^ 4 / 16 := by gcongr
        _ = (X σ₁ / 2) ^ 4 := by ring
    have heX : e ≤ X σ₁ / 2 :=
      le_of_pow_le_pow_left₀ (by norm_num) (by linarith [hX0 σ₁]) he4

    have hX₀ : X σ₁ / 2 ≤ X σ₀ := by linarith
    have hDn : 0 ≤ D ^ (3 * M' + M) := by positivity
    have : D ^ (3 * M' + M) * (X σ₁ / 2) ≤ D ^ (3 * M' + M) * X σ₀ :=
      mul_le_mul_of_nonneg_left hX₀ hDn
    rw [hD] at this hA1
    linarith

private theorem norm_deriv_le_of_forall_norm_le (f : ℂ → ℂ) (hf : Differentiable ℂ f) (A : ℝ) (N : ℕ)
    (hA : 0 ≤ A) (a b : ℝ) (h : ∀ w : ℂ, a ≤ w.re → w.re ≤ b → ‖f w‖ ≤ A * (1 + |w.im|) ^ N)
    (w : ℂ) (hw : a + 1 / 2 ≤ w.re) (hw' : w.re ≤ b - 1 / 2) :
    ‖deriv f w‖ ≤ 2 * (A * 2 ^ N * (1 + |w.im|) ^ N) := by
  have hR : (0 : ℝ) < 1 / 2 := by norm_num
  have hC : ∀ z ∈ Metric.sphere w (1 / 2), ‖f z‖ ≤ A * 2 ^ N * (1 + |w.im|) ^ N := by
    intro z hz
    rw [Metric.mem_sphere, Complex.dist_eq] at hz
    have hre : |(z - w).re| ≤ 1 / 2 := hz ▸ Complex.abs_re_le_norm (z - w)
    have him : |(z - w).im| ≤ 1 / 2 := hz ▸ Complex.abs_im_le_norm (z - w)
    rw [Complex.sub_re] at hre
    rw [Complex.sub_im] at him
    have hre' := abs_le.mp hre
    have him' := abs_le.mp him
    have hz1 : a ≤ z.re := by linarith
    have hz2 : z.re ≤ b := by linarith
    refine (h z hz1 hz2).trans ?_
    have hzim : 1 + |z.im| ≤ 2 * (1 + |w.im|) := by
      have : |z.im| ≤ |w.im| + 1 / 2 := by
        calc |z.im| = |(z.im - w.im) + w.im| := by ring_nf
          _ ≤ |z.im - w.im| + |w.im| := abs_add_le _ _
          _ ≤ 1 / 2 + |w.im| := by linarith [abs_le.mpr him']
          _ = |w.im| + 1 / 2 := by ring
      linarith [abs_nonneg w.im]
    have hpow : (1 + |z.im|) ^ N ≤ (2 * (1 + |w.im|)) ^ N :=
      pow_le_pow_left₀ (by positivity) hzim N
    calc A * (1 + |z.im|) ^ N ≤ A * (2 * (1 + |w.im|)) ^ N := mul_le_mul_of_nonneg_left hpow hA
      _ = A * 2 ^ N * (1 + |w.im|) ^ N := by rw [mul_pow]; ring
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hf.diffContOnCl hC
  calc ‖deriv f w‖ ≤ A * 2 ^ N * (1 + |w.im|) ^ N / (1 / 2) := this
    _ = 2 * (A * 2 ^ N * (1 + |w.im|) ^ N) := by ring

private theorem norm_sub_le_of_forall_norm_deriv_le (f : ℂ → ℂ) (hf : Differentiable ℂ f) (B a b y : ℝ)
    (hB : ∀ w : ℂ, a ≤ w.re → w.re ≤ b → w.im = y → ‖deriv f w‖ ≤ B)
    (σ σ' : ℝ) (hσ : a ≤ σ) (hσb : σ ≤ b) (hσ' : a ≤ σ') (hσ'b : σ' ≤ b) :
    ‖f (↑σ + ↑y * I) - f (↑σ' + ↑y * I)‖ ≤ B * |σ - σ'| := by
  set s : Set ℂ := {w : ℂ | a ≤ w.re} ∩ ({w : ℂ | w.re ≤ b} ∩ ({w : ℂ | w.im ≤ y} ∩ {w : ℂ | y ≤ w.im}))
    with hs
  have hconv : Convex ℝ s :=
    (convex_halfSpace_re_ge a).inter ((convex_halfSpace_re_le b).inter
      ((convex_halfSpace_im_le y).inter (convex_halfSpace_im_ge y)))
  have hmem : ∀ t : ℝ, a ≤ t → t ≤ b → (↑t + ↑y * I : ℂ) ∈ s := by
    intro t h1 h2
    simp only [hs, Set.mem_inter_iff, Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im,
      Complex.mul_im]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hdiff : ∀ x ∈ s, DifferentiableAt ℂ f x := fun x _ => hf x
  have hbound : ∀ x ∈ s, ‖deriv f x‖ ≤ B := by
    intro x hx
    simp only [hs, Set.mem_inter_iff, Set.mem_setOf_eq] at hx
    exact hB x hx.1 hx.2.1 (le_antisymm hx.2.2.1 hx.2.2.2)
  have key := hconv.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) hdiff hbound
    (hmem σ' hσ' hσ'b) (hmem σ hσ hσb)
  have hnorm : ‖(↑σ + ↑y * I : ℂ) - (↑σ' + ↑y * I)‖ = |σ - σ'| := by
    have : (↑σ + ↑y * I : ℂ) - (↑σ' + ↑y * I) = ((σ - σ' : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at key
  exact key

private theorem exists_pos_forall_le_norm (g : ℂ → ℂ) (hg : Continuous g) (a b c d : ℝ) (hab : a ≤ b)
    (hcd : c ≤ d)
    (h0 : ∀ w : ℂ, a ≤ w.re → w.re ≤ b → c ≤ w.im → w.im ≤ d → g w ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ w : ℂ, a ≤ w.re → w.re ≤ b → c ≤ w.im → w.im ≤ d → m ≤ ‖g w‖ := by
  set Kc : Set ℂ := {w : ℂ | a ≤ w.re ∧ w.re ≤ b ∧ c ≤ w.im ∧ w.im ≤ d} with hKc
  have hclosed : IsClosed Kc := by
    have e1 : IsClosed {w : ℂ | a ≤ w.re} := isClosed_le continuous_const Complex.continuous_re
    have e2 : IsClosed {w : ℂ | w.re ≤ b} := isClosed_le Complex.continuous_re continuous_const
    have e3 : IsClosed {w : ℂ | c ≤ w.im} := isClosed_le continuous_const Complex.continuous_im
    have e4 : IsClosed {w : ℂ | w.im ≤ d} := isClosed_le Complex.continuous_im continuous_const
    have : Kc = {w : ℂ | a ≤ w.re} ∩ {w : ℂ | w.re ≤ b} ∩ {w : ℂ | c ≤ w.im} ∩ {w : ℂ | w.im ≤ d} := by
      ext w; simp only [hKc, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
    rw [this]
    exact ((e1.inter e2).inter e3).inter e4
  have hbdd : Bornology.IsBounded Kc := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := |a| + |b| + |c| + |d|)).subset ?_
    intro w hw
    simp only [hKc, Set.mem_setOf_eq] at hw
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    have h1 : |w.re| ≤ |a| + |b| := by
      rcases le_or_gt 0 w.re with h | h
      · rw [abs_of_nonneg h]; linarith [le_abs_self b, abs_nonneg a]
      · rw [abs_of_neg h]; linarith [neg_abs_le a, abs_nonneg b]
    have h2 : |w.im| ≤ |c| + |d| := by
      rcases le_or_gt 0 w.im with h | h
      · rw [abs_of_nonneg h]; linarith [le_abs_self d, abs_nonneg c]
      · rw [abs_of_neg h]; linarith [neg_abs_le c, abs_nonneg d]
    linarith
  have hcpt : IsCompact Kc := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hne : Kc.Nonempty := ⟨↑a + ↑c * I, by
    simp only [hKc, Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩⟩
  have hcont : ContinuousOn (fun w => ‖g w‖) Kc := (continuous_norm.comp hg).continuousOn
  obtain ⟨w₀, hw₀, hmin⟩ := hcpt.exists_isMinOn hne hcont
  have hw₀' : a ≤ w₀.re ∧ w₀.re ≤ b ∧ c ≤ w₀.im ∧ w₀.im ≤ d := by
    simpa only [hKc, Set.mem_setOf_eq] using hw₀
  refine ⟨‖g w₀‖, norm_pos_iff.mpr (h0 w₀ hw₀'.1 hw₀'.2.1 hw₀'.2.2.1 hw₀'.2.2.2), ?_⟩
  intro w h1 h2 h3 h4
  have hw : w ∈ Kc := by simp only [hKc, Set.mem_setOf_eq]; exact ⟨h1, h2, h3, h4⟩
  exact hmin hw

private theorem exp_neg_le_norm_tprod_inv_one_sub {ι : Type*} (x : ι → ℂ) (hx : ∀ i, ‖x i‖ ≤ 1 / 2)
    (hs : Summable fun i => ‖x i‖) :
    Real.exp (-(3 / 2 * ∑' i, ‖x i‖)) ≤ ‖∏' i, (1 - x i)⁻¹‖ := by

  have hne : ∀ i, (1 - x i) ≠ 0 := by
    intro i h
    have : ‖x i‖ = 1 := by
      have : x i = 1 := by linear_combination -h
      rw [this, norm_one]
    linarith [hx i]
  have hne' : ∀ i, (1 - x i)⁻¹ ≠ 0 := fun i => inv_ne_zero (hne i)
  have harg : ∀ i, (1 - x i).arg ≠ Real.pi := by
    intro i h
    rw [Complex.arg_eq_pi_iff] at h
    have hre : (1 - x i).re = 1 - (x i).re := by simp
    have : (x i).re ≤ ‖x i‖ := Complex.re_le_norm _
    linarith [hx i, h.1]
  have hlog : ∀ i, Complex.log ((1 - x i)⁻¹) = -Complex.log (1 - x i) := fun i =>
    Complex.log_inv _ (harg i)

  have hsx : Summable x := .of_norm hs
  have hsl : Summable fun i => Complex.log (1 - x i) := by
    have := Complex.summable_log_one_add_of_summable hsx.neg
    refine this.congr fun i => ?_
    simp [sub_eq_add_neg]
  have hsl' : Summable fun i => Complex.log ((1 - x i)⁻¹) := by
    refine hsl.neg.congr fun i => ?_
    rw [hlog]

  have hprod : ∏' i, (1 - x i)⁻¹ = Complex.exp (∑' i, Complex.log ((1 - x i)⁻¹)) :=
    (Complex.cexp_tsum_eq_tprod hne' hsl').symm
  rw [hprod, Complex.norm_exp, Complex.re_tsum hsl']
  apply Real.exp_le_exp.mpr

  have hterm : ∀ i, -(3 / 2 * ‖x i‖) ≤ (Complex.log ((1 - x i)⁻¹)).re := by
    intro i
    rw [hlog, Complex.neg_re]
    have h1 : ‖Complex.log (1 - x i)‖ ≤ 3 / 2 * ‖x i‖ := by
      have := Complex.norm_log_one_add_half_le_self (z := -x i) (by rw [norm_neg]; exact hx i)
      simpa [sub_eq_add_neg, norm_neg] using this
    have h2 : (Complex.log (1 - x i)).re ≤ ‖Complex.log (1 - x i)‖ := Complex.re_le_norm _
    linarith
  have hsre : Summable fun i => (Complex.log ((1 - x i)⁻¹)).re :=
    (Complex.reCLM.summable hsl')
  have hsn : Summable fun i => -(3 / 2 * ‖x i‖) := (hs.mul_left (3 / 2)).neg
  calc -(3 / 2 * ∑' i, ‖x i‖) = ∑' i, -(3 / 2 * ‖x i‖) := by
        rw [← tsum_mul_left, tsum_neg]
    _ ≤ ∑' i, (Complex.log ((1 - x i)⁻¹)).re := hsn.tsum_le_tsum hterm hsre
end
end LineLowerBound

namespace LineLowerBound
section
open Complex

private theorem exists_forall_one_le_of_three_four_one (L : ℂ → ℂ) (hL : Differentiable ℂ L)
    (Z : ℝ → ℝ) (hZ0 : ∀ σ, 0 ≤ Z σ) (C₁ : ℝ)
    (hZ : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → (σ - 1) * Z σ ≤ C₁)
    (P : ℝ → ℝ → ℝ) (hP0 : ∀ σ t, 0 ≤ P σ t) (good : ℝ → Prop) (C₂ : ℝ) (M : ℕ)
    (hP : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ t : ℝ, good t → P σ t ≤ C₂ * (1 + |t|) ^ M)
    (a b : ℝ) (hab : a ≤ b) (hbad : ∀ t : ℝ, ¬ good t → a ≤ t ∧ t ≤ b)
    (h341 : ∀ σ : ℝ, 1 < σ → ∀ t : ℝ, 1 ≤ Z σ ^ 3 * ‖L ((σ : ℂ) + (t : ℂ) * I)‖ ^ 4 * P σ t)
    (hgrowth : ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 3 → ‖L w‖ ≤ A * (1 + |w.im|) ^ N)
    (hzero : ∀ w : ℂ, 1 ≤ w.re → w.re ≤ 2 → L w ≠ 0)
    (hIII : ∃ m₃ : ℝ, 0 < m₃ ∧ ∀ w : ℂ, 2 < w.re → m₃ ≤ ‖L w‖) :
    ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, 1 ≤ w.re → 1 ≤ A * (1 + |w.im|) ^ N * ‖L w‖ := by
  classical
  obtain ⟨A₁, N₁, hA₁⟩ := hgrowth
  obtain ⟨m₃, hm₃0, hRegIII⟩ := hIII

  have hA₁0 : 0 ≤ A₁ := by
    have h := hA₁ 1 (by simp) (by norm_num [Complex.one_re])
    have h1 : (1 + |(1 : ℂ).im|) ^ N₁ = 1 := by simp
    rw [h1, mul_one] at h
    exact (norm_nonneg _).trans h
  set D₁ : ℝ := max C₁ 1 with hD₁
  set D₂ : ℝ := max C₂ 1 with hD₂
  have hD₁1 : 1 ≤ D₁ := le_max_right _ _
  have hD₂1 : 1 ≤ D₂ := le_max_right _ _
  have hZ' : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → (σ - 1) * Z σ ≤ D₁ :=
    fun σ h1 h2 => (hZ σ h1 h2).trans (le_max_left _ _)
  have hP' : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ t : ℝ, good t → P σ t ≤ D₂ * (1 + |t|) ^ M := by
    intro σ h1 h2 t ht
    refine (hP σ h1 h2 t ht).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

  set Cc : ℝ := D₁ ^ 3 * D₂ with hCc
  have hC1 : ∀ t : ℝ, good t → ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (σ - 1) ^ 3 ≤ Cc * (1 + |t|) ^ M * ‖L ((σ : ℂ) + (t : ℂ) * I)‖ ^ 4 := by
    intro t ht σ hσ hσ2
    have h := h341 σ hσ t
    have e1 : ((σ - 1) * Z σ) ^ 3 ≤ D₁ ^ 3 :=
      pow_le_pow_left₀ (mul_nonneg (by linarith) (hZ0 σ)) (hZ' σ hσ hσ2) 3
    have e3 := hP' σ hσ hσ2 t ht
    have hσ0 : 0 ≤ (σ - 1) ^ 3 := pow_nonneg (by linarith) 3
    calc (σ - 1) ^ 3 ≤ (σ - 1) ^ 3 * (Z σ ^ 3 * ‖L ((σ : ℂ) + (t : ℂ) * I)‖ ^ 4 * P σ t) :=
          le_mul_of_one_le_right hσ0 h
      _ = ((σ - 1) * Z σ) ^ 3 * ‖L ((σ : ℂ) + (t : ℂ) * I)‖ ^ 4 * P σ t := by ring
      _ ≤ D₁ ^ 3 * ‖L ((σ : ℂ) + (t : ℂ) * I)‖ ^ 4 * (D₂ * (1 + |t|) ^ M) :=
          mul_le_mul (mul_le_mul_of_nonneg_right e1 (by positivity)) e3 (hP0 σ t)
            (mul_nonneg (pow_nonneg (by linarith) 3) (by positivity))
      _ = Cc * (1 + |t|) ^ M * ‖L ((σ : ℂ) + (t : ℂ) * I)‖ ^ 4 := by rw [hCc]; ring

  obtain ⟨c₀, hc₀, hext⟩ := exists_pos_forall_le_pow_mul Cc (2 * (A₁ * 2 ^ N₁)) M N₁
  have hRegI : ∀ w : ℂ, 1 ≤ w.re → w.re ≤ 2 → good w.im →
      c₀ ≤ (1 + |w.im|) ^ (3 * N₁ + M) * ‖L w‖ := by
    intro w h1 h2 hI
    have hcube : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
        (σ - 1) ^ 3 ≤ Cc * (1 + |w.im|) ^ M * (fun σ : ℝ => ‖L ((σ : ℂ) + (w.im : ℂ) * I)‖) σ ^ 4 :=
      fun σ hσ hσ2 => hC1 w.im hI σ hσ hσ2
    have hderiv : ∀ z : ℂ, 1 ≤ z.re → z.re ≤ 2 → z.im = w.im →
        ‖deriv L z‖ ≤ 2 * (A₁ * 2 ^ N₁ * (1 + |w.im|) ^ N₁) := by
      intro z hz1 hz2 hz3
      have := norm_deriv_le_of_forall_norm_le L hL A₁ N₁ hA₁0 0 3 (fun w h0 h3 => hA₁ w h0 h3) z
        (by linarith) (by linarith)
      rw [hz3] at this
      exact this
    have hlip : ∀ σ σ' : ℝ, 1 ≤ σ → σ ≤ 2 → 1 ≤ σ' → σ' ≤ 2 →
        |(fun σ : ℝ => ‖L ((σ : ℂ) + (w.im : ℂ) * I)‖) σ -
            (fun σ : ℝ => ‖L ((σ : ℂ) + (w.im : ℂ) * I)‖) σ'| ≤
          2 * (A₁ * 2 ^ N₁) * (1 + |w.im|) ^ N₁ * |σ - σ'| := by
      intro σ σ' p q r s
      have hmv := norm_sub_le_of_forall_norm_deriv_le L hL (2 * (A₁ * 2 ^ N₁ * (1 + |w.im|) ^ N₁)) 1 2
        w.im hderiv σ σ' p q r s
      calc |‖L ((σ : ℂ) + (w.im : ℂ) * I)‖ - ‖L ((σ' : ℂ) + (w.im : ℂ) * I)‖|
          ≤ ‖L ((σ : ℂ) + (w.im : ℂ) * I) - L ((σ' : ℂ) + (w.im : ℂ) * I)‖ := abs_norm_sub_norm_le _ _
        _ ≤ 2 * (A₁ * 2 ^ N₁ * (1 + |w.im|) ^ N₁) * |σ - σ'| := hmv
        _ = 2 * (A₁ * 2 ^ N₁) * (1 + |w.im|) ^ N₁ * |σ - σ'| := by ring
    have key := hext (fun σ : ℝ => ‖L ((σ : ℂ) + (w.im : ℂ) * I)‖) w.im (fun σ => norm_nonneg _)
      hcube hlip w.re h1 h2
    simpa only [re_add_im] using key

  obtain ⟨m, hm, hmin⟩ := exists_pos_forall_le_norm L hL.continuous 1 2 a b (by norm_num) hab
    (fun w p q _ _ => hzero w p q)

  refine ⟨max (max (1 / c₀) (1 / m)) (1 / m₃), 3 * N₁ + M, fun w hw => ?_⟩
  have hP1 : 1 ≤ (1 + |w.im|) ^ (3 * N₁ + M) := one_le_pow₀ (by linarith [abs_nonneg w.im])
  have hPQ : 0 ≤ (1 + |w.im|) ^ (3 * N₁ + M) * ‖L w‖ := by positivity
  have hAmax1 : 1 / c₀ ≤ max (max (1 / c₀) (1 / m)) (1 / m₃) := le_max_of_le_left (le_max_left _ _)
  have hAmax2 : 1 / m ≤ max (max (1 / c₀) (1 / m)) (1 / m₃) := le_max_of_le_left (le_max_right _ _)
  have hAmax3 : 1 / m₃ ≤ max (max (1 / c₀) (1 / m)) (1 / m₃) := le_max_right _ _
  have from_lower : ∀ μ : ℝ, 0 < μ → μ ≤ ‖L w‖ →
      1 / μ ≤ max (max (1 / c₀) (1 / m)) (1 / m₃) →
      1 ≤ max (max (1 / c₀) (1 / m)) (1 / m₃) * (1 + |w.im|) ^ (3 * N₁ + M) * ‖L w‖ := by
    intro μ hμ hμQ hμA
    have h1 : 1 ≤ 1 / μ * ‖L w‖ := by
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hμ, one_mul]; exact hμQ
    have h2 : 1 / μ * ‖L w‖ ≤ 1 / μ * ((1 + |w.im|) ^ (3 * N₁ + M) * ‖L w‖) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact le_mul_of_one_le_left (norm_nonneg _) hP1
    have h3 : 1 / μ * ((1 + |w.im|) ^ (3 * N₁ + M) * ‖L w‖) ≤
        max (max (1 / c₀) (1 / m)) (1 / m₃) * ((1 + |w.im|) ^ (3 * N₁ + M) * ‖L w‖) :=
      mul_le_mul_of_nonneg_right hμA hPQ
    calc (1 : ℝ) ≤ max (max (1 / c₀) (1 / m)) (1 / m₃) * ((1 + |w.im|) ^ (3 * N₁ + M) * ‖L w‖) :=
          h1.trans (h2.trans h3)
      _ = max (max (1 / c₀) (1 / m)) (1 / m₃) * (1 + |w.im|) ^ (3 * N₁ + M) * ‖L w‖ := by ring
  by_cases h2 : w.re ≤ 2
  · by_cases hI : good w.im
    ·
      have key := hRegI w hw h2 hI
      have h1 : 1 ≤ 1 / c₀ * ((1 + |w.im|) ^ (3 * N₁ + M) * ‖L w‖) := by
        rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc₀, one_mul]; exact key
      have h3 : 1 / c₀ * ((1 + |w.im|) ^ (3 * N₁ + M) * ‖L w‖) ≤
          max (max (1 / c₀) (1 / m)) (1 / m₃) * ((1 + |w.im|) ^ (3 * N₁ + M) * ‖L w‖) :=
        mul_le_mul_of_nonneg_right hAmax1 hPQ
      calc (1 : ℝ) ≤ max (max (1 / c₀) (1 / m)) (1 / m₃) * ((1 + |w.im|) ^ (3 * N₁ + M) * ‖L w‖) :=
            h1.trans h3
        _ = max (max (1 / c₀) (1 / m)) (1 / m₃) * (1 + |w.im|) ^ (3 * N₁ + M) * ‖L w‖ := by ring
    ·
      have hw' := hbad w.im hI
      exact from_lower m hm (hmin w hw h2 hw'.1 hw'.2) hAmax2
  ·
    push Not at h2
    exact from_lower m₃ hm₃0 (hRegIII w h2) hAmax3
end
end LineLowerBound

namespace ThreeFourOne
section
open Complex

private theorem re_neg_log_comb_nonneg {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re + (-log (1 - a * z ^ 2)).re := by
  have hac₀ : ‖(a : ℂ)‖ < 1 := by
    simp only [Complex.norm_of_nonneg ha₀, ha₁]
  have hac₁ : ‖a * z‖ < 1 := by rwa [norm_mul, hz, mul_one]
  have hac₂ : ‖a * z ^ 2‖ < 1 := by rwa [norm_mul, norm_pow, hz, one_pow, mul_one]
  rw [← ((hasSum_re <| hasSum_taylorSeries_neg_log hac₀).mul_left 3).add
    ((hasSum_re <| hasSum_taylorSeries_neg_log hac₁).mul_left 4) |>.add
    (hasSum_re <| hasSum_taylorSeries_neg_log hac₂) |>.tsum_eq]
  refine tsum_nonneg fun n ↦ ?_
  simp only [← ofReal_pow, div_natCast_re, ofReal_re, mul_pow, mul_re, ofReal_im, zero_mul,
    sub_zero]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · simp only [← mul_div_assoc, ← add_div]
    refine div_nonneg ?_ n.cast_nonneg
    rw [← pow_mul, pow_mul', sq, mul_re, ← sq, ← sq, ← sq_norm_sub_sq_re, norm_pow, hz]
    convert! (show 0 ≤ 2 * a ^ n * ((z ^ n).re + 1) ^ 2 by positivity) using 1
    ring

private theorem re_neg_log_comb_nonneg' {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a < 1) {z : ℂ} (hz : ‖z‖ = 1 ∨ z = 0) :
    0 ≤ 3 * (-log (1 - a)).re + 4 * (-log (1 - a * z)).re + (-log (1 - a * z ^ 2)).re := by
  rcases hz with hz | rfl
  · exact re_neg_log_comb_nonneg ha₀ ha₁ hz
  · have hac₀ : ‖(a : ℂ)‖ < 1 := by
      simp only [Complex.norm_of_nonneg ha₀, ha₁]
    have h0 : 0 ≤ (-log (1 - (a : ℂ))).re := by
      rw [← (hasSum_re <| hasSum_taylorSeries_neg_log hac₀).tsum_eq]
      refine tsum_nonneg fun n ↦ ?_
      simp only [← ofReal_pow, div_natCast_re, ofReal_re]
      positivity
    simp only [mul_zero, zero_pow two_ne_zero, sub_zero, log_one, neg_zero, zero_re, add_zero]
    linarith

private theorem facts {ι : Type*} (x : ι → ℂ) (hx : ∀ i, ‖x i‖ < 1) (hs : Summable fun i => ‖x i‖) :
    (∀ i, 1 - x i ≠ 0) ∧ (∀ i, log (1 - x i)⁻¹ = -log (1 - x i)) ∧ Summable fun i => log (1 - x i) := by
  have hre : ∀ i, (x i).re < 1 := fun i => (re_le_norm (x i)).trans_lt (hx i)
  refine ⟨fun i h => ?_, fun i => ?_, ?_⟩
  · have h' : (1 - x i).re = 0 := by rw [h, zero_re]
    rw [sub_re, one_re] at h'
    linarith [hre i]
  · refine log_inv _ fun harg => ?_
    obtain ⟨hneg, -⟩ := arg_eq_pi_iff.mp harg
    rw [sub_re, one_re] at hneg
    linarith [hre i]
  · have h1 : Summable fun i => -x i := (Summable.of_norm hs).neg
    simpa only [sub_eq_add_neg] using Complex.summable_log_one_add_of_summable h1

private theorem summable_re_and_norm_tprod_eq_exp {ι : Type*} (x : ι → ℂ) (hx : ∀ i, ‖x i‖ < 1)
    (hs : Summable fun i => ‖x i‖) :
    (Summable fun i => (-log (1 - x i)).re) ∧
      ‖∏' i, (1 - x i)⁻¹‖ = Real.exp (∑' i, (-log (1 - x i)).re) := by
  obtain ⟨hne, hlog, hsum⟩ := facts x hx hs
  have hsum' : Summable fun i => log (1 - x i)⁻¹ := hsum.neg.congr fun i => (hlog i).symm
  refine ⟨(hasSum_re hsum.neg.hasSum).summable, ?_⟩
  rw [← cexp_tsum_eq_tprod (fun i => inv_ne_zero (hne i)) hsum', norm_exp, ← (hasSum_re hsum'.hasSum).tsum_eq]
  congr 1
  exact tsum_congr fun i => by rw [hlog i]

private theorem one_le_norm_tprod_pow_three_mul_norm_tprod_pow_four_mul_norm_tprod {ι : Type*} (a : ι → ℝ) (z : ι → ℂ)
    (ha₀ : ∀ i, 0 ≤ a i) (ha₁ : ∀ i, a i < 1) (hz : ∀ i, ‖z i‖ = 1 ∨ z i = 0) (hs : Summable a) :
    1 ≤ ‖∏' i, (1 - (a i : ℂ))⁻¹‖ ^ 3 * ‖∏' i, (1 - (a i : ℂ) * z i)⁻¹‖ ^ 4 *
      ‖∏' i, (1 - (a i : ℂ) * z i ^ 2)⁻¹‖ := by
  have hn₁ : ∀ i, ‖(a i : ℂ)‖ = a i := fun i => Complex.norm_of_nonneg (ha₀ i)
  have hzle : ∀ i, ‖z i‖ ≤ 1 := fun i => by
    rcases hz i with h | h
    · exact h.le
    · rw [h, norm_zero]; exact zero_le_one
  have hn₂ : ∀ i, ‖(a i : ℂ) * z i‖ ≤ a i := fun i => by
    rw [norm_mul, hn₁]
    exact mul_le_of_le_one_right (ha₀ i) (hzle i)
  have hn₃ : ∀ i, ‖(a i : ℂ) * z i ^ 2‖ ≤ a i := fun i => by
    rw [norm_mul, hn₁, norm_pow]
    exact mul_le_of_le_one_right (ha₀ i) (pow_le_one₀ (norm_nonneg _) (hzle i))
  obtain ⟨hS₁, hP₁⟩ := summable_re_and_norm_tprod_eq_exp (fun i => (a i : ℂ))
    (fun i => by simpa only [hn₁] using ha₁ i) (by simpa only [hn₁] using hs)
  obtain ⟨hS₂, hP₂⟩ := summable_re_and_norm_tprod_eq_exp (fun i => (a i : ℂ) * z i)
    (fun i => (hn₂ i).trans_lt (ha₁ i)) (Summable.of_nonneg_of_le (fun i => norm_nonneg _) hn₂ hs)
  obtain ⟨hS₃, hP₃⟩ := summable_re_and_norm_tprod_eq_exp (fun i => (a i : ℂ) * z i ^ 2)
    (fun i => (hn₃ i).trans_lt (ha₁ i)) (Summable.of_nonneg_of_le (fun i => norm_nonneg _) hn₃ hs)
  try simp only at hS₁ hS₂ hS₃ hP₁ hP₂ hP₃
  have hcomb := ((hS₁.hasSum.mul_left 3).add (hS₂.hasSum.mul_left 4)).add hS₃.hasSum
  have hkey : 0 ≤ 3 * (∑' i, (-log (1 - (a i : ℂ))).re) + 4 * (∑' i, (-log (1 - (a i : ℂ) * z i)).re) +
      ∑' i, (-log (1 - (a i : ℂ) * z i ^ 2)).re := by
    rw [← hcomb.tsum_eq]
    exact tsum_nonneg fun i => re_neg_log_comb_nonneg' (ha₀ i) (ha₁ i) (hz i)
  rw [hP₁, hP₂, hP₃]
  first
    | (rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
       exact Real.one_le_exp (by push_cast; exact hkey))
    | (simp only [← Real.exp_nat_mul, ← Real.exp_add, Nat.cast_ofNat]
       exact Real.one_le_exp hkey)

private theorem _root_.ThreeFourOne.one_le_norm_tprod_cpow_three_four_one {ι : Type*} (N : ι → ℕ) (hN : ∀ i, 2 ≤ N i) (c : ι → ℂ)
    (hc : ∀ i, ‖c i‖ = 1 ∨ c i = 0) {σ : ℝ} (hσ : 1 < σ) (hs : Summable fun i => (N i : ℝ) ^ (-σ)) (t : ℝ) :
    1 ≤ ‖∏' i, (1 - ((N i : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ^ 3 *
        ‖∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)))⁻¹‖ ^ 4 *
      ‖∏' i, (1 - c i ^ 2 * ((N i : ℕ) : ℂ) ^ (-((σ : ℂ) + 2 * (t : ℂ) * I)))⁻¹‖ := by
  have hNpos : ∀ i, (0 : ℝ) < N i := fun i => by
    have := hN i
    positivity
  have hNne : ∀ i, ((N i : ℕ) : ℂ) ≠ 0 := fun i => by
    exact_mod_cast (hNpos i).ne'

  set a : ι → ℝ := fun i => (N i : ℝ) ^ (-σ) with ha_def
  set z : ι → ℂ := fun i => c i * ((N i : ℕ) : ℂ) ^ (-((t : ℂ) * I)) with hz_def
  have ha₀ : ∀ i, 0 ≤ a i := fun i => Real.rpow_nonneg (hNpos i).le _
  have ha₁ : ∀ i, a i < 1 := fun i => by
    show (N i : ℝ) ^ (-σ) < 1
    rw [Real.rpow_neg (hNpos i).le, inv_lt_one_iff₀]
    right
    refine Real.one_lt_rpow ?_ (zero_lt_one.trans hσ)
    exact_mod_cast (one_lt_two.trans_le (hN i))
  have hunit : ∀ i, ‖((N i : ℕ) : ℂ) ^ (-((t : ℂ) * I))‖ = 1 := fun i => by
    rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (hNpos i)]
    simp only [neg_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, neg_zero,
      Real.rpow_zero]
  have hz : ∀ i, ‖z i‖ = 1 ∨ z i = 0 := fun i => by
    rcases hc i with h | h
    · left
      show ‖c i * ((N i : ℕ) : ℂ) ^ (-((t : ℂ) * I))‖ = 1
      rw [norm_mul, h, hunit, mul_one]
    · right
      show c i * ((N i : ℕ) : ℂ) ^ (-((t : ℂ) * I)) = 0
      rw [h, zero_mul]

  have hcoe : ∀ i, ((a i : ℝ) : ℂ) = ((N i : ℕ) : ℂ) ^ (-(σ : ℂ)) := fun i => by
    show (((N i : ℝ) ^ (-σ) : ℝ) : ℂ) = ((N i : ℕ) : ℂ) ^ (-(σ : ℂ))
    rw [ofReal_cpow (hNpos i).le, ofReal_natCast, ofReal_neg]
  have hfac₂ : ∀ i, c i * ((N i : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) = (a i : ℂ) * z i := fun i => by
    rw [hcoe]
    show c i * ((N i : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) =
      ((N i : ℕ) : ℂ) ^ (-(σ : ℂ)) * (c i * ((N i : ℕ) : ℂ) ^ (-((t : ℂ) * I)))
    rw [neg_add, cpow_add _ _ (hNne i)]
    ring
  have hfac₃ : ∀ i, c i ^ 2 * ((N i : ℕ) : ℂ) ^ (-((σ : ℂ) + 2 * (t : ℂ) * I)) = (a i : ℂ) * z i ^ 2 := fun i => by
    rw [hcoe]
    show c i ^ 2 * ((N i : ℕ) : ℂ) ^ (-((σ : ℂ) + 2 * (t : ℂ) * I)) =
      ((N i : ℕ) : ℂ) ^ (-(σ : ℂ)) * (c i * ((N i : ℕ) : ℂ) ^ (-((t : ℂ) * I))) ^ 2
    rw [neg_add, cpow_add _ _ (hNne i), show -(2 * (t : ℂ) * I) = ((2 : ℕ) : ℂ) * -((t : ℂ) * I) by push_cast; ring,
      cpow_nat_mul]
    ring
  have key := one_le_norm_tprod_pow_three_mul_norm_tprod_pow_four_mul_norm_tprod a z ha₀ ha₁ hz hs
  simp only [hcoe] at key
  simp only [hfac₂, hfac₃]
  first
    | exact key
    | (simpa only [hcoe] using key)
p2m_export "ThreeFourOne" "one_le_norm_tprod_cpow_three_four_one"
end
end ThreeFourOne

namespace NumberField
p2m_export "NumberField" "HeightOneSpectrum.one_lt_absNorm RingOfIntegers dedekindZeta AdeleRing RingOfIntegers.HeightOneSpectrum.one_lt_absNorm AdelicLevel.uniformizerUnit summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero TateGlobal.exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm localChar IsUnramifiedCharAt mem_normOneIdeles_iff localChar_apply ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg normPowChar normPowChar_eq_one_of_ideleNorm_eq_one exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one exists_eq_normPowChar_of_forall_mem_normOneIdeles exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct exists_finset_forall_isUnramifiedCharAt_of_continuous"
namespace ThreeFourOneSites
p2m_open "NumberField.TateGlobal NumberField"
section
p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.NumberField IsDedekindDomain AutomorphicForm Complex"
p2m_open "NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.NumberField.TateGlobal"

variable (K : Type) [Field K] [NumberField K]

private theorem two_le_absNorm_aux4 (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h : 1 < Ideal.absNorm v.asIdeal := by
    first
      | exact NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
      | exact IsDedekindDomain.HeightOneSpectrum.one_lt_absNorm v
      | exact v.one_lt_absNorm
  omega

private theorem summable_subtype (T : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-σ) := by
  have hrow := NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K hσ
  first
    | exact hrow.subtype _
    | exact hrow.comp_injective Subtype.val_injective
    | exact (hrow.subtype {v | v ∉ T}).congr fun _ => rfl

private theorem one_le_norm_tprod_absNorm_three_four_one (T : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 < σ)
    (u : ℝ) :
    1 ≤ ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ^ 3 *
          ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-((σ : ℂ) + (u : ℂ) * I)))⁻¹‖ ^ 4 *
        ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-((σ : ℂ) + 2 * (u : ℂ) * I)))⁻¹‖ := by
  have h := _root_.ThreeFourOne.one_le_norm_tprod_cpow_three_four_one
    (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => Ideal.absNorm v.1.asIdeal) (fun v => two_le_absNorm_aux4 K v.1)
    (fun _ => (1 : ℂ)) (fun _ => Or.inl norm_one) hσ (summable_subtype K T hσ) u
  simpa only [one_mul, one_pow] using h

open scoped Classical in
private theorem one_le_norm_tprod_ite_three_four_one (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχu : IsUnitaryChar (𝓞 K) K χ)
    (T : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    1 ≤ ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ^ 3 *
          ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I))))⁻¹‖ ^ 4 *
        ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) ^ 2 *
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-((σ : ℂ) + 2 * (t : ℂ) * I))))⁻¹‖ := by
  have hc : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
      ‖(if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0)‖ = 1 ∨
        (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) = 0 := fun v => by
    by_cases h : IsUnramifiedCharAt χ v.1
    · left
      rw [if_pos h]
      first
        | exact hχu _
        | exact hχu (uniformizerIdele K v.1)
        | simpa using hχu (uniformizerIdele K v.1)
    · right
      exact if_neg h
  exact _root_.ThreeFourOne.one_le_norm_tprod_cpow_three_four_one
    (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => Ideal.absNorm v.1.asIdeal) (fun v => two_le_absNorm_aux4 K v.1)
    (fun v => if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) hc hσ
    (summable_subtype K T hσ) t

open scoped Classical in
private theorem one_le_norm_apply_three_four_one (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχu : IsUnitaryChar (𝓞 K) K χ)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (L : ℂ → ℂ)
    (hLE : ∀ s : ℂ, 1 < s.re →
        L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
    {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    1 ≤ ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ^ 3 *
          ‖L ((σ : ℂ) + (t : ℂ) * I)‖ ^ 4 *
        ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) ^ 2 *
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-((σ : ℂ) + 2 * (t : ℂ) * I))))⁻¹‖ := by
  have hre : (1 : ℝ) < ((σ : ℂ) + (t : ℂ) * I).re := by
    first
      | (rw [show ((σ : ℂ) + (t : ℂ) * I).re = σ by simp]
         exact hσ)
      | simpa using hσ
  rw [hLE _ hre]
  exact one_le_norm_tprod_ite_three_four_one K χ hχu T hσ t
end
end NumberField.TateGlobal.ThreeFourOneSites

namespace NumberField
p2m_export "NumberField" "HeightOneSpectrum.one_lt_absNorm RingOfIntegers dedekindZeta AdeleRing RingOfIntegers.HeightOneSpectrum.one_lt_absNorm AdelicLevel.uniformizerUnit summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero TateGlobal.exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm localChar IsUnramifiedCharAt mem_normOneIdeles_iff localChar_apply ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg normPowChar normPowChar_eq_one_of_ideleNorm_eq_one exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one exists_eq_normPowChar_of_forall_mem_normOneIdeles exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct exists_finset_forall_isUnramifiedCharAt_of_continuous"
namespace EulerFactors
p2m_open "NumberField.TateGlobal NumberField"
section
p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.NumberField IsDedekindDomain AutomorphicForm"
p2m_open "NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.NumberField.TateGlobal NumberField.AdelicLevel"

section Helpers

variable {ι : Type} {x : ι → ℂ}

private theorem one_sub_ne_zero_of_norm_lt_one (hx1 : ∀ i, ‖x i‖ < 1) (i : ι) : (1 : ℂ) - x i ≠ 0 := by
  intro h
  have h1 : x i = 1 := by linear_combination -h
  have := hx1 i
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

private theorem re_one_sub_pos_of_norm_lt_one (hx1 : ∀ i, ‖x i‖ < 1) (i : ι) : 0 < ((1 : ℂ) - x i).re := by
  have h1 : |(x i).re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm (x i)) (hx1 i)
  have h2 := (abs_lt.mp h1).2
  simp only [Complex.sub_re, Complex.one_re]
  linarith

private theorem arg_one_sub_ne_pi_of_norm_lt_one (hx1 : ∀ i, ‖x i‖ < 1) (i : ι) : ((1 : ℂ) - x i).arg ≠ Real.pi := by
  intro h
  have := (Complex.arg_eq_pi_iff.mp h).1
  linarith [re_one_sub_pos_of_norm_lt_one hx1 i]

private theorem summable_log_one_sub (hx : Summable fun i => ‖x i‖) :
    Summable fun i => Complex.log (1 - x i) := by
  have h := Complex.summable_log_one_add_of_summable (Summable.of_norm hx).neg
  simpa [sub_eq_add_neg] using h

private theorem summable_log_inv_one_sub (hx : Summable fun i => ‖x i‖) (hx1 : ∀ i, ‖x i‖ < 1) :
    Summable fun i => Complex.log ((1 - x i)⁻¹) := by
  refine (summable_log_one_sub hx).neg.congr fun i => ?_
  rw [Complex.log_inv _ (arg_one_sub_ne_pi_of_norm_lt_one hx1 i)]

end Helpers

variable (K : Type) [Field K] [NumberField K]

private theorem isUnitaryChar_one : IsUnitaryChar (𝓞 K) K (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := by
  intro x
  simp

private theorem isIdeleClassChar_one : IsIdeleClassChar (𝓞 K) K (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := by
  intro u
  rfl

private theorem localChar_one (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    localChar (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) v t = 1 := by
  rfl

private theorem valued_uniformizerUnit_eq_ofAdd (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v (uniformizerUnit K v : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ) := by
  first
    | exact valued_uniformizerUnit K v
    | simpa using valued_uniformizerUnit K v

variable {K}

private theorem meromorphicOn_shift_div (τ : ℝ) {Q : ℂ → ℂ} (hQ : Differentiable ℂ Q) :
    MeromorphicOn (fun s : ℂ => Q (s - ((τ : ℝ) : ℂ) * Complex.I) / (s - 1)) Set.univ := by
  have h1 : MeromorphicOn (fun s : ℂ => Q (s - ((τ : ℝ) : ℂ) * Complex.I)) Set.univ := by
    have hd : Differentiable ℂ (fun s : ℂ => Q (s - ((τ : ℝ) : ℂ) * Complex.I)) :=
      hQ.comp (differentiable_id.sub_const _)
    exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hd).meromorphicOn
  have h2 : MeromorphicOn (fun s : ℂ => s - 1) Set.univ :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr (differentiable_id.sub_const 1)).meromorphicOn
  exact h1.div h2

private theorem tprod_inv_one_sub_eq_inv_tprod {ι : Type} {x : ι → ℂ} (hx : Summable fun i => ‖x i‖)
    (hx1 : ∀ i, ‖x i‖ < 1) :
    ∏' i, (1 - x i)⁻¹ = (∏' i, (1 - x i))⁻¹ := by
  have hne : ∀ i, (1 : ℂ) - x i ≠ 0 := by
    intro i h
    have h1 : x i = 1 := by linear_combination -h
    have := hx1 i
    rw [h1, norm_one] at this
    exact lt_irrefl _ this
  have hre : ∀ i, 0 < ((1 : ℂ) - x i).re := by
    intro i
    have h1 : |(x i).re| < 1 := lt_of_le_of_lt (Complex.abs_re_le_norm (x i)) (hx1 i)
    have h2 := (abs_lt.mp h1).2
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have harg : ∀ i, ((1 : ℂ) - x i).arg ≠ Real.pi := by
    intro i h
    have := (Complex.arg_eq_pi_iff.mp h).1
    linarith [hre i]
  have hlog : Summable fun i => Complex.log (1 - x i) := by
    have h := Complex.summable_log_one_add_of_summable (Summable.of_norm hx).neg
    simpa [sub_eq_add_neg] using h
  have hlog' : Summable fun i => Complex.log ((1 - x i)⁻¹) := by
    refine hlog.neg.congr fun i => ?_
    rw [Complex.log_inv _ (harg i)]
  have hA : Complex.exp (∑' i, Complex.log ((1 - x i)⁻¹)) = ∏' i, (1 - x i)⁻¹ :=
    Complex.cexp_tsum_eq_tprod (fun i => inv_ne_zero (hne i)) hlog'
  have hB : Complex.exp (∑' i, Complex.log (1 - x i)) = ∏' i, (1 - x i) :=
    Complex.cexp_tsum_eq_tprod hne hlog
  rw [← hA, ← hB, ← Complex.exp_neg, ← tsum_neg]
  congr 1
  exact tsum_congr fun i => Complex.log_inv _ (harg i)

open scoped Classical in
private theorem shift_div_eq_inv_tprod (τ : ℝ) (T : Finset (HeightOneSpectrum (𝓞 K))) {Q : ℂ → ℂ}
    (hQE : ∀ s : ℂ, 1 < s.re →
      Q s = (s - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) *
        ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt (normPowChar K τ) v.1 then
                (((normPowChar K τ) (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
    (s : ℂ) (hs : 1 < s.re) :
    Q (s - ((τ : ℝ) : ℂ) * Complex.I) / (s - 1) =
      (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - ((localChar (1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) v.1 (uniformizerUnit K v.1) : ℂˣ) : ℂ) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  have hs' : 1 < (s - ((τ : ℝ) : ℂ) * Complex.I).re := by
    simpa using hs
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have : s = 1 := sub_eq_zero.mp h
    rw [this] at hs
    simp at hs
  have hN : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ≠ 0 := fun v => by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.1.ne_bot)
  rw [hQE _ hs']
  have hshift : s - ((τ : ℝ) : ℂ) * Complex.I - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I) = s - 1 := by ring
  rw [hshift, mul_div_cancel_left₀ _ hs1]
  rw [← tprod_inv_one_sub_eq_inv_tprod]
  · refine tprod_congr fun v => ?_
    rw [ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg, localChar_one,
      Units.val_one, one_mul, ← Complex.cpow_add _ _ (hN v)]
    congr 2
    ring
  ·
    have hN := NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K hs
    refine (hN.comp_injective (Subtype.val_injective (p := fun v : HeightOneSpectrum (𝓞 K) => v ∉ T))).congr ?_
    intro v
    have hpos : (0 : ℕ) < Ideal.absNorm v.1.asIdeal :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.1.ne_bot)
    simp only [Function.comp, localChar_one, Units.val_one, one_mul, Complex.norm_natCast_cpow_of_pos hpos,
      Complex.neg_re]
  · intro v
    have hpos : (0 : ℕ) < Ideal.absNorm v.1.asIdeal :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.1.ne_bot)
    have hgt : (1 : ℝ) < ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) := by
      first
        | exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v.1
        | exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v.1
        | exact_mod_cast v.1.one_lt_absNorm
    rw [localChar_one, Units.val_one, one_mul, Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hgt (by linarith)

variable (K)

private theorem continuous_one : Continuous (⇑(1 : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)) := by
  first
    | exact continuous_const
    | (show Continuous fun _ : (AdeleRing (𝓞 K) K)ˣ => (1 : ℂˣ); exact continuous_const)
    | simpa using (continuous_const : Continuous fun _ : (AdeleRing (𝓞 K) K)ˣ => (1 : ℂˣ))

private theorem apply_uniformizerIdele_eq_localChar (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    χ (uniformizerIdele K v) = localChar χ v (uniformizerUnit K v) := by
  first
    | rfl
    | (rw [localChar_apply]; rfl)
    | simp [localChar_apply, uniformizerIdele]

variable {K}

private theorem tprod_compl_eq_tprod_compl_of_subset {T S : Finset (HeightOneSpectrum (𝓞 K))} (hTS : T ⊆ S)
    (f : HeightOneSpectrum (𝓞 K) → ℂ) (hf : ∀ v, v ∉ T → v ∈ S → f v = 1) :
    ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, f v.1 = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, f v.1 := by
  change ∏' v : ({v | v ∉ T} : Set (HeightOneSpectrum (𝓞 K))), f v =
    ∏' v : ({v | v ∉ S} : Set (HeightOneSpectrum (𝓞 K))), f v
  rw [tprod_subtype, tprod_subtype]
  refine tprod_congr fun v => ?_
  by_cases hT : v ∈ T
  · have hS : v ∈ S := hTS hT
    simp [Set.mulIndicator_apply, hT, hS]
  · by_cases hS : v ∈ S
    · simp [Set.mulIndicator_apply, hT, hS, hf v hT hS]
    · simp [Set.mulIndicator_apply, hT, hS]

private theorem isIdeleClassChar_mul_self {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχ : IsIdeleClassChar (𝓞 K) K χ) :
    IsIdeleClassChar (𝓞 K) K (χ * χ) := by
  intro u
  rw [MonoidHom.mul_apply, hχ u, one_mul]

private theorem isUnitaryChar_mul_self {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχ : IsUnitaryChar (𝓞 K) K χ) :
    IsUnitaryChar (𝓞 K) K (χ * χ) := by
  intro y
  rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, hχ y, one_mul]

private theorem continuous_mul_self {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχ : Continuous χ) : Continuous (⇑(χ * χ)) := by
  first
    | exact hχ.mul hχ
    | (show Continuous fun y => χ y * χ y; exact hχ.mul hχ)
    | simpa using hχ.mul hχ

private theorem isUnramifiedCharAt_mul_self {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {v : HeightOneSpectrum (𝓞 K)}
    (hv : IsUnramifiedCharAt χ v) : IsUnramifiedCharAt (χ * χ) v := by
  intro t ht ht'
  have h1 := hv t ht ht'
  rw [localChar_apply] at h1 ⊢
  rw [MonoidHom.mul_apply, h1, one_mul]

open scoped Classical in
private theorem ite_mul_self_eq_sq {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} {v : HeightOneSpectrum (𝓞 K)}
    (hv : IsUnramifiedCharAt χ v) :
    (if IsUnramifiedCharAt (χ * χ) v then (((χ * χ) (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) =
      (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) ^ 2 := by
  rw [if_pos (isUnramifiedCharAt_mul_self hv), if_pos hv, MonoidHom.mul_apply, Units.val_mul, sq]

private theorem natCast_cpow_neg_mul_cpow_neg (v : HeightOneSpectrum (𝓞 K)) (t : ℝ) (s : ℂ) :
    ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ))) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + Complex.I * (t : ℂ))) := by
  have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  rw [← Complex.cpow_add _ _ hN]
  congr 1
  ring

section F2

variable {ι : Type}

private theorem norm_coeff_mul_cpow_le {c : ℂ} (hc : ‖c‖ ≤ 1) (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    ‖c * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re) := by
  have hpos : (0 : ℕ) < Ideal.absNorm v.asIdeal :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot)
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) hc

private theorem norm_coeff_mul_cpow_lt_one
    {c : ℂ} (hc : ‖c‖ ≤ 1) (v : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 1 < s.re) :
    ‖c * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ < 1 := by
  refine (norm_coeff_mul_cpow_le hc v s).trans_lt ?_
  have hgt : (1 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    first
      | exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
      | exact_mod_cast NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
      | exact_mod_cast v.one_lt_absNorm
  exact Real.rpow_lt_one_of_one_lt_of_neg hgt (by linarith)

private theorem summable_norm_coeff_mul_cpow (S : Finset (HeightOneSpectrum (𝓞 K)))
    (c : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
      ‖c v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖ := by
  have hN := (NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K hs).comp_injective
    (Subtype.val_injective (p := fun v : HeightOneSpectrum (𝓞 K) => v ∉ S))
  refine Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_) hN
  exact norm_coeff_mul_cpow_le (hc v) v.1 s

private theorem tprod_inv_one_sub_eq_cexp {x : ι → ℂ} (hx : Summable fun i => ‖x i‖) (hx1 : ∀ i, ‖x i‖ < 1) :
    ∏' i, (1 - x i)⁻¹ = Complex.exp (∑' i, -Complex.log (1 - x i)) := by
  rw [← Complex.cexp_tsum_eq_tprod (fun i => inv_ne_zero (one_sub_ne_zero_of_norm_lt_one hx1 i))
    (summable_log_inv_one_sub hx hx1)]
  congr 1
  exact tsum_congr fun i => Complex.log_inv _ (arg_one_sub_ne_pi_of_norm_lt_one hx1 i)

private theorem tprod_inv_one_sub_ne_zero {x : ι → ℂ} (hx : Summable fun i => ‖x i‖) (hx1 : ∀ i, ‖x i‖ < 1) :
    ∏' i, (1 - x i)⁻¹ ≠ 0 := by
  rw [tprod_inv_one_sub_eq_cexp hx hx1]
  exact Complex.exp_ne_zero _

private theorem norm_tprod_inv_one_sub_eq_rexp {x : ι → ℂ} (hx : Summable fun i => ‖x i‖) (hx1 : ∀ i, ‖x i‖ < 1) :
    ‖∏' i, (1 - x i)⁻¹‖ = Real.exp (∑' i, (-Complex.log (1 - x i)).re) := by
  rw [tprod_inv_one_sub_eq_cexp hx hx1, Complex.norm_exp]
  congr 1
  first
    | exact Complex.re_tsum (summable_log_one_sub hx).neg
    | simpa using Complex.re_tsum (summable_log_one_sub hx).neg

private theorem norm_tprod_inv_one_sub_le_rexp {x : ι → ℂ} (hx : Summable fun i => ‖x i‖) (hx2 : ∀ i, ‖x i‖ ≤ 1 / 2) :
    ‖∏' i, (1 - x i)⁻¹‖ ≤ Real.exp ((3 / 2) * ∑' i, ‖x i‖) := by
  have hx1 : ∀ i, ‖x i‖ < 1 := fun i => lt_of_le_of_lt (hx2 i) (by norm_num)
  rw [norm_tprod_inv_one_sub_eq_rexp hx hx1]
  refine Real.exp_le_exp.mpr ?_
  rw [← tsum_mul_left]
  have hterm : ∀ i, (-Complex.log (1 - x i)).re ≤ 3 / 2 * ‖x i‖ := by
    intro i
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_neg]
    have h := Complex.norm_log_one_add_half_le_self (z := -x i) (by rw [norm_neg]; exact hx2 i)
    rw [norm_neg] at h
    simpa [sub_eq_add_neg] using h
  have hsum : Summable fun i => (-Complex.log (1 - x i)).re := by
    first
      | exact (summable_log_one_sub hx).neg.mapL Complex.reCLM
      | exact Complex.reCLM.summable (summable_log_one_sub hx).neg
      | simpa using Complex.reCLM.summable (summable_log_one_sub hx).neg
  exact Summable.tsum_le_tsum hterm hsum (hx.mul_left (3 / 2))

end F2

variable (K)

private theorem dedekindZeta_eq_prod_mul_tprod (T : Finset (HeightOneSpectrum (𝓞 K))) (u : ℂ) (hu : 1 < u.re) :
    NumberField.dedekindZeta K u =
      (∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-u))⁻¹) *
        ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-u))⁻¹ := by
  have hP := hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta K u hu
  set F : HeightOneSpectrum (𝓞 K) → ℂ := fun v => (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-u))⁻¹ with hF
  have hs : Multipliable (F ∘ ((↑) : ↥(T : Set (HeightOneSpectrum (𝓞 K))) → HeightOneSpectrum (𝓞 K))) :=
    T.finite_toSet.multipliable F
  have hsc : Multipliable (F ∘ ((↑) : ↥((T : Set (HeightOneSpectrum (𝓞 K)))ᶜ) → HeightOneSpectrum (𝓞 K))) := by
    apply Complex.multipliable_of_summable_log
    have hx : Summable fun v : ↥((T : Set (HeightOneSpectrum (𝓞 K)))ᶜ) =>
        ‖(1 : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-u)‖ := by
      have hN := (NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K hu).comp_injective
        (Subtype.val_injective (p := fun v : HeightOneSpectrum (𝓞 K) => v ∈ (T : Set (HeightOneSpectrum (𝓞 K)))ᶜ))
      refine Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_) hN
      exact norm_coeff_mul_cpow_le norm_one.le v.1 u
    have hx1 : ∀ v : ↥((T : Set (HeightOneSpectrum (𝓞 K)))ᶜ),
        ‖(1 : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-u)‖ < 1 :=
      fun v => norm_coeff_mul_cpow_lt_one norm_one.le v.1 hu
    have h := summable_log_inv_one_sub hx hx1
    simpa [hF, Function.comp] using h
  have hsplit := hP.unique (hs.hasProd.mul_compl hsc.hasProd)
  rw [hsplit]
  first
    | (simp only [Function.comp_def]; rw [Finset.tprod_subtype']; rfl)
    | (simp only [Function.comp]; rw [Finset.tprod_subtype']; rfl)
    | (simp only [Function.comp_def, Finset.tprod_subtype']; rfl)
    | simp only [Function.comp_def, Finset.tprod_subtype', hF]
end
end NumberField.TateGlobal.EulerFactors

namespace NumberField
p2m_export "NumberField" "HeightOneSpectrum.one_lt_absNorm RingOfIntegers dedekindZeta AdeleRing RingOfIntegers.HeightOneSpectrum.one_lt_absNorm AdelicLevel.uniformizerUnit summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero TateGlobal.exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm localChar IsUnramifiedCharAt mem_normOneIdeles_iff localChar_apply ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg normPowChar normPowChar_eq_one_of_ideleNorm_eq_one exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one exists_eq_normPowChar_of_forall_mem_normOneIdeles exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct exists_finset_forall_isUnramifiedCharAt_of_continuous"
namespace RamifiedPlaces
p2m_open "NumberField.TateGlobal NumberField"
section
p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.NumberField IsDedekindDomain AutomorphicForm"
p2m_open "NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.NumberField.TateGlobal"

variable (K : Type) [Field K] [NumberField K]

private theorem exists_finset_subset_and_forall_isUnramifiedCharAt (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (T S₀ : Finset (HeightOneSpectrum (𝓞 K))) (hS₀ : ∀ v ∉ S₀, IsUnramifiedCharAt χ v) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), T ⊆ S ∧ (∀ v ∉ S, IsUnramifiedCharAt χ v) ∧
      ∀ v ∈ S, v ∉ T → ¬ IsUnramifiedCharAt χ v := by
  classical
  refine ⟨T ∪ S₀.filter (fun v => ¬ IsUnramifiedCharAt χ v), ?_, ?_, ?_⟩
  · first
      | exact Finset.subset_union_left
      | exact Finset.subset_union_left _ _
  · intro v hv
    by_contra hram
    have hvS₀ : v ∈ S₀ := by
      by_contra h
      exact hram (hS₀ v h)
    exact hv (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvS₀, hram⟩))
  · intro v hvS hvT
    rcases Finset.mem_union.mp hvS with h | h
    · exact absurd h hvT
    · exact (Finset.mem_filter.mp h).2

open scoped Classical in
private theorem tprod_ite_eq_tprod_of_subset (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) {T S : Finset (HeightOneSpectrum (𝓞 K))}
    (hTS : T ⊆ S) (hS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (hST : ∀ v ∈ S, v ∉ T → ¬ IsUnramifiedCharAt χ v)
    (s : ℂ) :
    ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ =
      ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          (1 - ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  refine (EulerFactors.tprod_compl_eq_tprod_compl_of_subset hTS
    (fun v => (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
      (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) fun v hvT hvS => ?_).trans ?_
  · simp only [if_neg (hST v hvS hvT), zero_mul, sub_zero, inv_one]
  · exact tprod_congr fun v => by simp only [if_pos (hS v.1 v.2)]

open scoped Classical in
private theorem tprod_ite_eq_inv_tprod_one_sub_localChar_of_subset (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχu : IsUnitaryChar (𝓞 K) K χ) {T S : Finset (HeightOneSpectrum (𝓞 K))} (hTS : T ⊆ S)
    (hS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (hST : ∀ v ∈ S, v ∉ T → ¬ IsUnramifiedCharAt χ v) {s : ℂ}
    (hs : 1 < s.re) :
    ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ =
      (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          (1 - ((localChar χ v.1 (NumberField.AdelicLevel.uniformizerUnit K v.1) : ℂˣ) : ℂ) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))))⁻¹ := by
  rw [tprod_ite_eq_tprod_of_subset K χ hTS hS hST s]
  have hx : Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
      ‖((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖ :=
    EulerFactors.summable_norm_coeff_mul_cpow S (fun v => ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ))
      (fun v => (hχu (uniformizerIdele K v.1)).le) s hs
  have hx1 : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      ‖((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖ < 1 :=
    fun v => EulerFactors.norm_coeff_mul_cpow_lt_one (hχu (uniformizerIdele K v.1)).le v.1 hs
  rw [EulerFactors.tprod_inv_one_sub_eq_inv_tprod hx hx1]

  first
    | (congr 1; done)
    | (congr 1
       exact tprod_congr fun v => by rw [EulerFactors.apply_uniformizerIdele_eq_localChar])

open scoped Classical in
private theorem tprod_ite_sq_eq_tprod_ite_mul_self_of_subset (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    {T S : Finset (HeightOneSpectrum (𝓞 K))} (hTS : T ⊆ S) (hS : ∀ v ∉ S, IsUnramifiedCharAt χ v)
    (hST : ∀ v ∈ S, v ∉ T → ¬ IsUnramifiedCharAt χ v) (s : ℂ) :
    ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) ^ 2 *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ =
      ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          (1 - (if IsUnramifiedCharAt (χ * χ) v.1 then (((χ * χ) (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  refine (EulerFactors.tprod_compl_eq_tprod_compl_of_subset hTS
    (fun v => (1 - (if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) ^ 2 *
      (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) fun v hvT hvS => ?_).trans ?_
  · simp only [if_neg (hST v hvS hvT), zero_pow two_ne_zero, zero_mul, sub_zero, inv_one]
  · exact tprod_congr fun v => by simp only [EulerFactors.ite_mul_self_eq_sq (hS v.1 v.2)]
end
end NumberField.TateGlobal.RamifiedPlaces

namespace NumberField
p2m_export "NumberField" "HeightOneSpectrum.one_lt_absNorm RingOfIntegers dedekindZeta AdeleRing RingOfIntegers.HeightOneSpectrum.one_lt_absNorm AdelicLevel.uniformizerUnit summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero TateGlobal.exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm localChar IsUnramifiedCharAt mem_normOneIdeles_iff localChar_apply ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg normPowChar normPowChar_eq_one_of_ideleNorm_eq_one exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one exists_eq_normPowChar_of_forall_mem_normOneIdeles exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct exists_finset_forall_isUnramifiedCharAt_of_continuous"
namespace ShiftedZeta
p2m_open "NumberField.TateGlobal NumberField"
section
p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.NumberField IsDedekindDomain AutomorphicForm"
p2m_open "NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.NumberField.TateGlobal Complex"

variable (K : Type) [Field K] [NumberField K]

private theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

private theorem absNorm_natCast_ne_zero (v : HeightOneSpectrum (𝓞 K)) :
    ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := by have := two_le_absNorm K v; omega
  exact_mod_cast this

private theorem one_sub_absNorm_cpow_neg_ne_zero (v : HeightOneSpectrum (𝓞 K)) (u : ℂ) (hu : 1 < u.re) :
    (1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-u) ≠ 0 := by
  intro h
  have heq : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-u) = 1 := by
    linear_combination -h
  have hpos : 0 < Ideal.absNorm v.asIdeal := by have := two_le_absNorm K v; omega
  have hnorm := norm_natCast_cpow_of_pos hpos (-u)
  rw [heq, norm_one] at hnorm
  have hlt : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ ((-u).re) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · have := two_le_absNorm K v
      exact_mod_cast (by omega : 1 < Ideal.absNorm v.asIdeal)
    · rw [neg_re]; linarith
  linarith

open scoped Classical in
private theorem ite_normPowChar_factor_eq (τ : ℝ) (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    (1 - (if IsUnramifiedCharAt (normPowChar K τ) v then
        (((normPowChar K τ) (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
      (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ =
    (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + I * τ)))⁻¹ := by
  have hmul : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(Complex.I * (τ : ℂ))) *
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s) =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + I * τ)) := by
    rw [← cpow_add _ _ (absNorm_natCast_ne_zero K v)]
    congr 1
    ring
  rw [NumberField.TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
    K τ v, hmul]

open scoped Classical in
private theorem tprod_ite_normPowChar_eq (τ : ℝ) (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) :
    (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
      (1 - (if IsUnramifiedCharAt (normPowChar K τ) v.1 then
          (((normPowChar K τ) (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
        (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) =
    ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
      (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s + I * τ)))⁻¹ :=
  tprod_congr fun v => ite_normPowChar_factor_eq K τ v.1 s

open scoped Classical in
private theorem apply_one_sub_ne_zero (τ : ℝ) (T : Finset (HeightOneSpectrum (𝓞 K))) (Q : ℂ → ℂ)
    (hQ : Differentiable ℂ Q)
    (hQE : ∀ s : ℂ, 1 < s.re →
      Q s = (s - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) *
        ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt (normPowChar K τ) v.1 then
                (((normPowChar K τ) (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
    (hsplit : ∀ u : ℂ, 1 < u.re → NumberField.dedekindZeta K u =
      (∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-u))⁻¹) *
        ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-u))⁻¹) :
    Q ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨R, hR, hR1, hRE, -⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero K

  set G : ℂ → ℂ := fun s => R (s + I * τ) *
    ∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + I * τ))) with hG
  have hshift : Continuous fun s : ℂ => s + I * τ := continuous_id.add continuous_const
  have hGc : Continuous G := by
    rw [hG]
    refine (hR.continuous.comp hshift).mul ?_
    refine continuous_finset_prod T fun v _ => ?_
    refine continuous_const.sub ?_
    exact Continuous.const_cpow hshift.neg (Or.inl (absNorm_natCast_ne_zero K v))

  have hEq : Set.EqOn Q G {s : ℂ | 1 < s.re} := by
    intro s hs
    simp only [Set.mem_setOf_eq] at hs
    have hu : 1 < (s + I * τ).re := by
      simp only [add_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_zero, add_zero]
      exact hs
    have h1 : Q s = (s - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) *
        ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s + I * τ)))⁻¹ := by
      rw [hQE s hs, tprod_ite_normPowChar_eq]
    have h2 : R (s + I * τ) = (s + I * τ - 1) * NumberField.dedekindZeta K (s + I * τ) := hRE _ hu
    have h3 := hsplit (s + I * τ) hu
    have h4 : (∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + I * τ)))⁻¹) *
        ∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + I * τ))) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun v _ => ?_
      exact inv_mul_cancel₀ (one_sub_absNorm_cpow_neg_ne_zero K v _ hu)
    show Q s = G s
    rw [h1, hG]
    simp only
    rw [h2, h3]
    have hs₀ : s + I * τ - 1 = s - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I) := by ring
    rw [hs₀]
    set ZT := ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
      (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(s + I * τ)))⁻¹
    set PT := ∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + I * τ)))⁻¹
    set DT := ∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + I * τ)))
    calc (s - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) * ZT
        = (s - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) * ZT * (PT * DT) := by rw [h4, mul_one]
      _ = (s - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) * (PT * ZT) * DT := by ring

  have hcl : ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I) ∈ closure {s : ℂ | 1 < s.re} := by
    rw [closure_setOf_lt_re]
    simp only [Set.mem_setOf_eq, sub_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, zero_mul, sub_self, sub_zero, le_refl]
  have hval : Q ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I) = G ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I) :=
    hEq.closure hQ.continuous hGc hcl
  have hone : ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I) + I * τ = 1 := by ring
  rw [hval, hG]
  simp only
  rw [hone]
  refine mul_ne_zero hR1 (Finset.prod_ne_zero_iff.mpr fun v _ => ?_)
  rw [cpow_neg_one]
  intro h
  have h' : (((Ideal.absNorm v.asIdeal : ℕ) : ℂ))⁻¹ = 1 := by linear_combination -h
  rw [inv_eq_one] at h'
  have h2 := two_le_absNorm K v
  have : (Ideal.absNorm v.asIdeal : ℕ) = 1 := by exact_mod_cast h'
  omega
end
end NumberField.TateGlobal.ShiftedZeta

namespace NumberField
p2m_export "NumberField" "HeightOneSpectrum.one_lt_absNorm RingOfIntegers dedekindZeta AdeleRing RingOfIntegers.HeightOneSpectrum.one_lt_absNorm AdelicLevel.uniformizerUnit summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero TateGlobal.exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm localChar IsUnramifiedCharAt mem_normOneIdeles_iff localChar_apply ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg normPowChar normPowChar_eq_one_of_ideleNorm_eq_one exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one exists_eq_normPowChar_of_forall_mem_normOneIdeles exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct exists_finset_forall_isUnramifiedCharAt_of_continuous"
namespace PartialZetaBound
p2m_open "NumberField.TateGlobal NumberField"
section
p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.NumberField IsDedekindDomain AutomorphicForm Complex"
p2m_open "NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.NumberField.TateGlobal"

variable (K : Type) [Field K] [NumberField K]

private theorem exists_forall_sub_one_mul_norm_tprod_le (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ C₁ : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (σ - 1) * ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ ≤ C₁ := by
  obtain ⟨R, hR, -, hRE, -⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero K
  have hcont : ContinuousOn (fun σ : ℝ => ‖R (σ : ℂ)‖) (Set.Icc 1 2) :=
    (continuous_norm.comp (hR.continuous.comp continuous_ofReal)).continuousOn
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).bddAbove_image hcont
  refine ⟨C * 2 ^ T.card, fun σ hσ hσ2 => ?_⟩
  have hu : 1 < ((σ : ℂ)).re := by simpa using hσ
  have hsplit := NumberField.TateGlobal.EulerFactors.dedekindZeta_eq_prod_mul_tprod K T (σ : ℂ) hu
  have hReq := hRE (σ : ℂ) hu
  have hcancel : (∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹) *
      ∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun v _ => ?_
    exact inv_mul_cancel₀ (NumberField.TateGlobal.ShiftedZeta.one_sub_absNorm_cpow_neg_ne_zero K v _ hu)
  set ZT := ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
    (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹ with hZT
  set PT := ∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹ with hPT
  set DT := ∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ))) with hDT
  have hid : ((σ : ℂ) - 1) * ZT = R (σ : ℂ) * DT := by
    rw [hReq, hsplit]
    calc ((σ : ℂ) - 1) * ZT = ((σ : ℂ) - 1) * ZT * (PT * DT) := by rw [hcancel, mul_one]
      _ = ((σ : ℂ) - 1) * (PT * ZT) * DT := by ring
  have hnorm : (σ - 1) * ‖ZT‖ = ‖R (σ : ℂ)‖ * ‖DT‖ := by
    have h := congrArg (fun z : ℂ => ‖z‖) hid
    simp only [norm_mul] at h
    have h1 : ‖((σ : ℂ) - 1)‖ = σ - 1 := by
      rw [show ((σ : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < σ - 1)]
    rw [h1] at h
    exact h
  rw [hnorm]
  have hRle : ‖R (σ : ℂ)‖ ≤ C := hC ⟨σ, ⟨hσ.le, hσ2⟩, rfl⟩
  have hN1 : ∀ v : HeightOneSpectrum (𝓞 K), (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := fun v => by
    have := NumberField.TateGlobal.ShiftedZeta.two_le_absNorm K v
    exact_mod_cast (by omega : 1 ≤ Ideal.absNorm v.asIdeal)
  have hNpos : ∀ v : HeightOneSpectrum (𝓞 K), 0 < Ideal.absNorm v.asIdeal := fun v => by
    have := NumberField.TateGlobal.ShiftedZeta.two_le_absNorm K v; omega
  have hfac : ∀ v ∈ T, ‖(1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))‖ ≤ 2 := by
    intro v _
    have hx : ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ))‖ ≤ 1 := by
      rw [norm_natCast_cpow_of_pos (hNpos v)]
      refine Real.rpow_le_one_of_one_le_of_nonpos (hN1 v) ?_
      simp only [neg_re, ofReal_re, neg_nonpos]
      linarith
    calc ‖(1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))‖
        ≤ ‖(1 : ℂ)‖ + ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ))‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; exact add_le_add le_rfl hx
      _ = 2 := by norm_num
  have hDTle : ‖DT‖ ≤ 2 ^ T.card := by
    rw [hDT, norm_prod]
    calc ∏ v ∈ T, ‖(1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))‖
        ≤ ∏ _v ∈ T, (2 : ℝ) := Finset.prod_le_prod (fun _ _ => norm_nonneg _) hfac
      _ = 2 ^ T.card := Finset.prod_const 2
  have hC0 : 0 ≤ C := (norm_nonneg _).trans hRle
  exact mul_le_mul hRle hDTle (norm_nonneg _) hC0

open scoped Classical in
private theorem exists_pos_forall_le_norm_of_two_lt_re
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχu : IsUnitaryChar (𝓞 K) K χ)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (L : ℂ → ℂ)
    (hLE : ∀ s : ℂ, 1 < s.re →
        L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    ∃ m₃ : ℝ, 0 < m₃ ∧ ∀ w : ℂ, 2 < w.re → m₃ ≤ ‖L w‖ := by

  have hc : ∀ v : HeightOneSpectrum (𝓞 K),
      ‖(if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0)‖ ≤ 1 := by
    intro v
    split_ifs
    · exact (hχu _).le
    · simp
  have hN1 : ∀ v : HeightOneSpectrum (𝓞 K), (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := fun v => by
    have := NumberField.TateGlobal.ShiftedZeta.two_le_absNorm K v
    exact_mod_cast (by omega : 1 ≤ Ideal.absNorm v.asIdeal)
  have hN2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := fun v => by
    exact_mod_cast NumberField.TateGlobal.ShiftedZeta.two_le_absNorm K v
  have hsum2 : Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} =>
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
    have h := NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K (σ := (2 : ℝ))
      (by norm_num)
    exact h.subtype _
  set S₂ : ℝ := ∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
    ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ)) with hS₂
  refine ⟨Real.exp (-(3 / 2 * S₂)), Real.exp_pos _, fun w hw => ?_⟩
  rw [hLE w (by linarith)]
  set x : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} → ℂ := fun v =>
    (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
      (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)) with hx
  have hxre : ∀ v, ‖x v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-w.re) := fun v =>
    NumberField.TateGlobal.EulerFactors.norm_coeff_mul_cpow_le (hc v.1) v.1 w
  have hxle : ∀ v, ‖x v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(2 : ℝ)) := fun v =>
    (hxre v).trans (Real.rpow_le_rpow_of_exponent_le (hN1 v.1) (by linarith))
  have hxhalf : ∀ v, ‖x v‖ ≤ 1 / 2 := by
    intro v
    refine (hxre v).trans ?_
    have h1 : ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-w.re) ≤
        ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (hN1 v.1) (by linarith)
    refine h1.trans ?_
    rw [Real.rpow_neg_one, inv_eq_one_div]
    exact one_div_le_one_div_of_le two_pos (hN2 v.1)
  have hxsum : Summable fun v => ‖x v‖ :=
    Summable.of_nonneg_of_le (fun v => norm_nonneg _) hxle hsum2
  have hlow := LineLowerBound.exp_neg_le_norm_tprod_inv_one_sub x hxhalf hxsum
  have htsum : ∑' v, ‖x v‖ ≤ S₂ := hxsum.tsum_le_tsum hxle hsum2
  calc Real.exp (-(3 / 2 * S₂)) ≤ Real.exp (-(3 / 2 * ∑' v, ‖x v‖)) := by
        apply Real.exp_le_exp.mpr; linarith
    _ ≤ ‖∏' v, (1 - x v)⁻¹‖ := hlow
end
end NumberField.TateGlobal.PartialZetaBound

namespace NumberField
p2m_export "NumberField" "HeightOneSpectrum.one_lt_absNorm RingOfIntegers dedekindZeta AdeleRing RingOfIntegers.HeightOneSpectrum.one_lt_absNorm AdelicLevel.uniformizerUnit summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero TateGlobal.exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm localChar IsUnramifiedCharAt mem_normOneIdeles_iff localChar_apply ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg normPowChar normPowChar_eq_one_of_ideleNorm_eq_one exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one exists_eq_normPowChar_of_forall_mem_normOneIdeles exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct exists_finset_forall_isUnramifiedCharAt_of_continuous"
namespace SquareCharacterBound
p2m_open "NumberField.TateGlobal NumberField"
section
p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.NumberField IsDedekindDomain AutomorphicForm Complex"
p2m_open "NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.NumberField.TateGlobal"

variable (K : Type) [Field K] [NumberField K]

private theorem le_abs_mul_two_pow_mul_of_le {A x t : ℝ} {N : ℕ} (hx : x ≤ A * (1 + |2 * t|) ^ N) :
    x ≤ |A| * 2 ^ N * (1 + |t|) ^ N := by
  have h1 : (1 + |2 * t|) ≤ 2 * (1 + |t|) := by
    rw [abs_mul, abs_two]
    linarith [abs_nonneg t]
  have h2 : (1 + |2 * t|) ^ N ≤ (2 * (1 + |t|)) ^ N :=
    pow_le_pow_left₀ (by positivity) h1 N
  calc x ≤ A * (1 + |2 * t|) ^ N := hx
    _ ≤ |A| * (1 + |2 * t|) ^ N := mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
    _ ≤ |A| * (2 * (1 + |t|)) ^ N := mul_le_mul_of_nonneg_left h2 (abs_nonneg A)
    _ = |A| * 2 ^ N * (1 + |t|) ^ N := by rw [mul_pow, mul_assoc]

private theorem re_point (σ t : ℝ) : ((σ : ℂ) + 2 * (t : ℂ) * I).re = σ := by
  first
    | simp
    | (simp; ring)

private theorem im_point (σ t : ℝ) : ((σ : ℂ) + 2 * (t : ℂ) * I).im = 2 * t := by
  first
    | simp
    | (simp; ring)

private theorem differentiable_finset_prod_one_sub_cpow (τ : ℝ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Differentiable ℂ fun s : ℂ =>
      ∏ v ∈ S, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + I * τ))) := by
  classical
  have hfac : ∀ v : HeightOneSpectrum (𝓞 K),
      Differentiable ℂ fun s : ℂ => (1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + I * τ)) := fun v => by
    refine (differentiable_const _).sub ?_
    exact Differentiable.const_cpow (differentiable_id.add_const _).neg
      (Or.inl (ShiftedZeta.absNorm_natCast_ne_zero K v))
  induction S using Finset.induction_on with
  | empty => simpa using differentiable_const (1 : ℂ)
  | @insert v S hv ih =>
    simp only [Finset.prod_insert hv]
    exact (hfac v).mul ih

private theorem re_shift (s : ℂ) (τ : ℝ) : (s + I * τ).re = s.re := by
  simp

open scoped Classical in
private theorem exists_forall_norm_tprod_ite_mul_self_le
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 K) K χ)
    (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 K) K χ) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (C : ℝ) (M : ℕ) (t₀ : ℝ), ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ t : ℝ, 1 ≤ |2 * t + t₀| →
      ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          (1 - (if IsUnramifiedCharAt (χ * χ) v.1 then (((χ * χ) (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-((σ : ℂ) + 2 * (t : ℂ) * I))))⁻¹‖ ≤ C * (1 + |t|) ^ M := by
  by_cases hcls : ∀ x ∈ normOneIdeles K, (χ * χ) x = 1
  ·
    obtain ⟨τ₂, hτ₂⟩ := exists_eq_normPowChar_of_forall_mem_normOneIdeles K (χ * χ)
      (EulerFactors.continuous_mul_self hχc) (EulerFactors.isUnitaryChar_mul_self hχu) hcls
    obtain ⟨R, hR, -, hReq, -⟩ :=
      NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero K
    have hQ₂ : Differentiable ℂ fun s : ℂ =>
        R (s + I * τ₂) * ∏ v ∈ S, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + I * τ₂))) :=
      (hR.comp (differentiable_id.add_const _)).mul (differentiable_finset_prod_one_sub_cpow K τ₂ S)
    have hQ₂E : ∀ s : ℂ, 1 < s.re →
        R (s + I * τ₂) * ∏ v ∈ S, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + I * τ₂))) =
          (s - ((1 : ℂ) - ((τ₂ : ℝ) : ℂ) * Complex.I)) *
            ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
              (1 - (if IsUnramifiedCharAt (normPowChar K τ₂) v.1 then
                    (((normPowChar K τ₂) (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
                (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
      intro s hs
      have hu : 1 < (s + I * τ₂).re := by rw [re_shift]; exact hs
      have hP : ∏ v ∈ S, ((1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(s + I * τ₂))) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun v _ => ShiftedZeta.one_sub_absNorm_cpow_neg_ne_zero K v _ hu
      have hs₀ : s + I * τ₂ - 1 = s - ((1 : ℂ) - ((τ₂ : ℝ) : ℂ) * Complex.I) := by ring
      rw [ShiftedZeta.tprod_ite_normPowChar_eq K τ₂ S s, hReq _ hu,
        EulerFactors.dedekindZeta_eq_prod_mul_tprod K S _ hu, Finset.prod_inv_distrib, hs₀]
      have hcancel : ∀ a z p : ℂ, p ≠ 0 → a * (p⁻¹ * z) * p = a * z := fun a z p hp => by
        calc a * (p⁻¹ * z) * p = a * z * (p⁻¹ * p) := by ring
          _ = a * z := by rw [inv_mul_cancel₀ hp, mul_one]
      first
        | exact hcancel _ _ _ hP
        | field_simp
    obtain ⟨A, N, hAN⟩ := exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc K τ₂ S
      0 3 _ hQ₂ hQ₂E
    refine ⟨|A| * 2 ^ N, N, τ₂, fun σ hσ1 hσ2 t ht => ?_⟩
    rw [hτ₂]
    have hw : 1 < ((σ : ℂ) + 2 * (t : ℂ) * I).re := by rw [re_point]; exact hσ1
    have hQw := hQ₂E _ hw
    have hbound := hAN ((σ : ℂ) + 2 * (t : ℂ) * I) (by rw [re_point]; linarith) (by rw [re_point]; linarith)
    rw [im_point] at hbound
    have hws : 1 ≤ ‖((σ : ℂ) + 2 * (t : ℂ) * I) - ((1 : ℂ) - ((τ₂ : ℝ) : ℂ) * Complex.I)‖ := by
      refine le_trans ?_ (Complex.abs_im_le_norm _)
      have him : (((σ : ℂ) + 2 * (t : ℂ) * I) - ((1 : ℂ) - ((τ₂ : ℝ) : ℂ) * Complex.I)).im = 2 * t + τ₂ := by
        first
          | simp
          | (simp; ring)
      rw [him]
      exact ht
    refine le_abs_mul_two_pow_mul_of_le (le_trans ?_ hbound)
    first
      | (rw [hQw, norm_mul]
         exact le_mul_of_one_le_left (norm_nonneg _) hws)
      | (beta_reduce
         rw [hQw, norm_mul]
         exact le_mul_of_one_le_left (norm_nonneg _) hws)
      | (calc _ ≤ ‖((σ : ℂ) + 2 * (t : ℂ) * I) - ((1 : ℂ) - ((τ₂ : ℝ) : ℂ) * Complex.I)‖ * _ :=
              le_mul_of_one_le_left (norm_nonneg _) hws
            _ = _ := (norm_mul _ _).symm.trans (congrArg norm hQw.symm))
  ·

    have hne : ∃ x ∈ normOneIdeles K, (χ * χ) x ≠ 1 := by
      first
        | simpa using hcls
        | (push_neg at hcls; exact hcls)
    obtain ⟨L₂, hL₂, hL₂E⟩ := exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one K (χ * χ)
      (EulerFactors.isIdeleClassChar_mul_self hχ) (EulerFactors.continuous_mul_self hχc)
      (EulerFactors.isUnitaryChar_mul_self hχu) hne S
    obtain ⟨A, N, hAN⟩ := exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc K (χ * χ)
      (EulerFactors.isIdeleClassChar_mul_self hχ) (EulerFactors.continuous_mul_self hχc)
      (EulerFactors.isUnitaryChar_mul_self hχu) hne S 0 3 L₂ hL₂ hL₂E
    refine ⟨|A| * 2 ^ N, N, 0, fun σ hσ1 hσ2 t _ => ?_⟩
    have hw : 1 < ((σ : ℂ) + 2 * (t : ℂ) * I).re := by rw [re_point]; exact hσ1
    have hbound := hAN ((σ : ℂ) + 2 * (t : ℂ) * I) (by rw [re_point]; linarith) (by rw [re_point]; linarith)
    rw [im_point, hL₂E _ hw] at hbound
    exact le_abs_mul_two_pow_mul_of_le hbound

open scoped Classical in
private theorem exists_forall_norm_tprod_ite_sq_le (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 K) K χ)
    (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 K) K χ) {T S : Finset (HeightOneSpectrum (𝓞 K))} (hTS : T ⊆ S)
    (hS : ∀ v ∉ S, IsUnramifiedCharAt χ v) (hST : ∀ v ∈ S, v ∉ T → ¬ IsUnramifiedCharAt χ v) :
    ∃ (C : ℝ) (M : ℕ) (t₀ : ℝ), ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ t : ℝ, 1 ≤ |2 * t + t₀| →
      ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) ^ 2 *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-((σ : ℂ) + 2 * (t : ℂ) * I))))⁻¹‖ ≤ C * (1 + |t|) ^ M := by
  obtain ⟨C, M, t₀, h⟩ := exists_forall_norm_tprod_ite_mul_self_le K χ hχ hχc hχu S
  refine ⟨C, M, t₀, fun σ hσ1 hσ2 t ht => ?_⟩
  rw [RamifiedPlaces.tprod_ite_sq_eq_tprod_ite_mul_self_of_subset K χ hTS hS hST]
  exact h σ hσ1 hσ2 t ht

private theorem mem_Icc_of_not_one_le_abs (t₀ t : ℝ) (h : ¬ 1 ≤ |2 * t + t₀|) :
    t ∈ Set.Icc (-t₀ / 2 - 1 / 2) (-t₀ / 2 + 1 / 2) := by
  rw [not_le] at h
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  exact ⟨by linarith, by linarith⟩
end
end NumberField.TateGlobal.SquareCharacterBound

namespace NumberField
p2m_export "NumberField" "HeightOneSpectrum.one_lt_absNorm RingOfIntegers dedekindZeta AdeleRing RingOfIntegers.HeightOneSpectrum.one_lt_absNorm AdelicLevel.uniformizerUnit summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero TateGlobal.exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "normOneIdeles ideleNorm localChar IsUnramifiedCharAt mem_normOneIdeles_iff localChar_apply ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg normPowChar normPowChar_eq_one_of_ideleNorm_eq_one exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one exists_eq_normPowChar_of_forall_mem_normOneIdeles exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct exists_finset_forall_isUnramifiedCharAt_of_continuous"
namespace StripNonvanishingChar
p2m_open "NumberField.TateGlobal NumberField"
section
p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.NumberField IsDedekindDomain AutomorphicForm"
p2m_open "NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.NumberField.TateGlobal NumberField.AdelicLevel"

variable {K : Type} [Field K] [NumberField K]

private theorem mul_normPowChar_ne_one
    {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hχ1 : ∃ x ∈ normOneIdeles K, χ x ≠ 1) (t : ℝ) :
    χ * normPowChar K t ≠ 1 := by
  intro h
  obtain ⟨x, hx, hχx⟩ := hχ1
  apply hχx
  have hx1 : ideleNorm K x = 1 := by
    first
      | exact (mem_normOneIdeles_iff x).mp hx
      | exact (mem_normOneIdeles_iff K x).mp hx
  have h1 : (χ * normPowChar K t) x = 1 := by
    rw [h]
    first
      | rfl
      | simp
  first
    | (rw [MonoidHom.mul_apply, normPowChar_eq_one_of_ideleNorm_eq_one t hx1, mul_one] at h1; exact h1)
    | (simp only [MonoidHom.mul_apply, normPowChar_eq_one_of_ideleNorm_eq_one t hx1, mul_one] at h1; exact h1)
    | simpa [MonoidHom.mul_apply, normPowChar_eq_one_of_ideleNorm_eq_one t hx1] using h1

variable (K)

open scoped Classical in
private theorem apply_ne_zero_of_one_le_re
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 K) K χ) (hχc : Continuous χ)
    (hχu : IsUnitaryChar (𝓞 K) K χ)
    (hχ1 : ∃ x ∈ normOneIdeles K, χ x ≠ 1)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (L : ℂ → ℂ) (hL : Differentiable ℂ L)
    (hLE : ∀ s : ℂ, 1 < s.re →
        L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
    {S : Finset (HeightOneSpectrum (𝓞 K))} (hTS : T ⊆ S) (hS : ∀ v ∉ S, IsUnramifiedCharAt χ v)
    (hST : ∀ v ∈ S, v ∉ T → ¬ IsUnramifiedCharAt χ v) (w : ℂ) (hw : 1 ≤ w.re) : L w ≠ 0 := by
  intro hLw
  rcases eq_or_lt_of_le hw with hre | hre
  ·
    have hw_eq : (1 : ℂ) + (w.im : ℂ) * Complex.I = w := by
      apply Complex.ext <;> simp <;> linarith
    obtain ⟨c, hc, hlim⟩ := exists_tendsto_punctured_ne_zero_of_eq_partialEulerProduct K S
      (fun v => uniformizerUnit K v) (fun v => EulerFactors.valued_uniformizerUnit_eq_ofAdd K v) χ hχc hχu hχ L
      (Complex.analyticOnNhd_univ_iff_differentiable.mpr hL).meromorphicOn
      (fun s hs => (hLE s hs).trans
        (RamifiedPlaces.tprod_ite_eq_inv_tprod_one_sub_localChar_of_subset K χ hχu hTS hS hST hs))
      w.im (mul_normPowChar_ne_one hχ1 w.im)
    have hlim2 : Filter.Tendsto L (nhdsWithin ((1 : ℂ) + (w.im : ℂ) * Complex.I) {(1 : ℂ) + (w.im : ℂ) * Complex.I}ᶜ)
        (nhds (L ((1 : ℂ) + (w.im : ℂ) * Complex.I))) :=
      hL.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hcL := tendsto_nhds_unique hlim hlim2
    rw [hw_eq, hLw] at hcL
    exact hc hcL
  ·
    rw [hLE w hre] at hLw
    have hgate : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        ‖(if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0)‖ ≤ 1 := by
      intro v
      split_ifs
      · exact (hχu _).le
      · simp
    refine EulerFactors.tprod_inv_one_sub_ne_zero (x := fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} =>
        (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)) ?_ ?_ hLw
    · exact EulerFactors.summable_norm_coeff_mul_cpow T _ hgate w hre
    · exact fun v => EulerFactors.norm_coeff_mul_cpow_lt_one (hgate v) v.1 hre
end
end NumberField.TateGlobal.StripNonvanishingChar

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.NumberField IsDedekindDomain AutomorphicForm"
p2m_open "NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.NumberField.TateGlobal"
open _root_.NumberField.TateGlobal _root_.P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.NumberField.TateGlobal _root_.NumberField _root_.P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.NumberField in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hχ : IsIdeleClassChar (𝓞 K) K χ) (_hχc : Continuous χ)
    (_hχu : IsUnitaryChar (𝓞 K) K χ)
    (_hχ1 : ∃ x ∈ normOneIdeles K, χ x ≠ 1)
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (L : ℂ → ℂ) (_hL : Differentiable ℂ L)
    (_hLE : ∀ s : ℂ, 1 < s.re →
        L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, 1 ≤ w.re → 1 ≤ A * (1 + |w.im|) ^ N * ‖L w‖ := by
  obtain ⟨S₀, hS₀⟩ := NumberField.TateGlobal.exists_finset_forall_isUnramifiedCharAt_of_continuous K χ _hχc
  obtain ⟨S, hTS, hS, hST⟩ :=
    NumberField.TateGlobal.RamifiedPlaces.exists_finset_subset_and_forall_isUnramifiedCharAt K χ T S₀ hS₀
  obtain ⟨C₁, hC₁⟩ := NumberField.TateGlobal.PartialZetaBound.exists_forall_sub_one_mul_norm_tprod_le K T
  obtain ⟨C₂, M, t₀, hP⟩ :=
    NumberField.TateGlobal.SquareCharacterBound.exists_forall_norm_tprod_ite_sq_le K χ _hχ _hχc _hχu hTS hS hST
  obtain ⟨m₃, hm₃, hIII⟩ :=
    NumberField.TateGlobal.PartialZetaBound.exists_pos_forall_le_norm_of_two_lt_re K χ _hχu T L _hLE
  refine LineLowerBound.exists_forall_one_le_of_three_four_one L _hL
    (fun σ : ℝ => ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
      (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖)
    (fun σ => norm_nonneg _) C₁ hC₁
    (fun σ t : ℝ => ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
      (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) ^ 2 *
        (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-((σ : ℂ) + 2 * (t : ℂ) * Complex.I))))⁻¹‖)
    (fun σ t => norm_nonneg _) (fun t : ℝ => 1 ≤ |2 * t + t₀|) C₂ M hP
    (-t₀ / 2 - 1 / 2) (-t₀ / 2 + 1 / 2) (by linarith)
    (fun t ht => NumberField.TateGlobal.SquareCharacterBound.mem_Icc_of_not_one_le_abs t₀ t ht)
    (fun σ hσ t =>
      NumberField.TateGlobal.ThreeFourOneSites.one_le_norm_apply_three_four_one K χ _hχu T L _hLE hσ t)
    ?_ ?_ ⟨m₃, hm₃, hIII⟩
  · exact NumberField.TateGlobal.exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc
      K χ _hχ _hχc _hχu _hχ1 T 0 3 L _hL _hLE
  · exact fun w hw _ =>
      NumberField.TateGlobal.StripNonvanishingChar.apply_ne_zero_of_one_le_re K χ _hχ _hχc _hχu _hχ1 T L _hL
        _hLE hTS hS hST w hw

#print axioms solution

end S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct (solution)
