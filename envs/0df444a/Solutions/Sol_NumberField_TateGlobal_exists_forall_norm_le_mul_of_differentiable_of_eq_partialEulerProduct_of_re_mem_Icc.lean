-- Prove2me | solution 1 for NumberField.TateGlobal.exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d2eab448-8c06-51c5-9aa0-d878b46e673f

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_NumberField_TateGlobal_exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar
import Theorems.Thm_Complex_exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero LanglandsTunnell.signEpsilon_one LanglandsTunnell.RealArchParam.epsilonFactor_principal LanglandsTunnell.RealArchParam.epsilonFactor_discrete LanglandsTunnell.signEpsilon_zero LanglandsTunnell.signShift_zero LanglandsTunnell.RealArchParam.twist_zero LanglandsTunnell.RealArchParam.discrete.sizeOf_spec LanglandsTunnell.RealArchParam.principal.injEq LanglandsTunnell.ComplexArchParam.dual_dual LanglandsTunnell.ComplexArchParam.mk.sizeOf_spec LanglandsTunnell.RealArchParam.dual_dual LanglandsTunnell.RealArchParam.discrete.injEq LanglandsTunnell.ComplexArchParam.twist_zero LanglandsTunnell.RealArchParam.principal.sizeOf_spec LanglandsTunnell.signShift_one LanglandsTunnell.ComplexArchParam.mk.injEq LanglandsTunnell.TateLocal.conductorExponentAt_one NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply LanglandsTunnell.LDatum.mk.sizeOf_spec LanglandsTunnell.LDatum.badFactor_zero LanglandsTunnell.LDatum.mk.injEq M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent"

set_option autoImplicit false

namespace StripInterpolation

open Complex Set Filter

private theorem sq_le_mul_exp (κ : ℝ) (hκ : 0 < κ) (y : ℝ) (hy : 0 ≤ y) :
    y ^ 2 ≤ 4 / κ ^ 2 * Real.exp (κ * y) := by
  have h1 : κ / 2 * y ≤ Real.exp (κ / 2 * y) := by linarith [Real.add_one_le_exp (κ / 2 * y)]
  have h0 : 0 ≤ κ / 2 * y := by positivity
  have h2 : (κ / 2 * y) ^ 2 ≤ Real.exp (κ / 2 * y) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : Real.exp (κ / 2 * y) ^ 2 = Real.exp (κ * y) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [h3] at h2
  have h4 : (κ / 2 * y) ^ 2 = y ^ 2 * κ ^ 2 / 4 := by ring
  rw [h4] at h2
  have hκ2 : 0 < κ ^ 2 := by positivity
  have h5 : y ^ 2 * κ ^ 2 ≤ 4 * Real.exp (κ * y) := by linarith
  rw [show 4 / κ ^ 2 * Real.exp (κ * y) = 4 * Real.exp (κ * y) / κ ^ 2 by ring, le_div_iff₀ hκ2]
  exact h5

private theorem exists_forall_norm_le_mul_pow (F : ℂ → ℂ) (hF : Differentiable ℂ F) (σL σR : ℝ)
    (hσ : σL < σR) (C D : ℝ)
    (hg : ∀ z : ℂ, σL ≤ z.re → z.re ≤ σR →
      ‖F z‖ ≤ D * Real.exp (C * ‖z‖ * Real.log (2 + ‖z‖)))
    (A : ℝ) (N : ℕ) (hL : ∀ t : ℝ, ‖F (σL + t * Complex.I)‖ ≤ A * (1 + |t|) ^ N)
    (hR : ∀ t : ℝ, ‖F (σR + t * Complex.I)‖ ≤ A * (1 + |t|) ^ N) :
    ∃ (A' : ℝ) (N' : ℕ), ∀ z : ℂ, σL ≤ z.re → z.re ≤ σR → ‖F z‖ ≤ A' * (1 + |z.im|) ^ N' := by

  set c : ℝ := σL - 1 with hc_def
  set W : ℝ := σR - σL + 1 with hW_def
  have hW1 : 1 ≤ W := by rw [hW_def]; linarith
  have hA0 : 0 ≤ A := by
    have h := hL 0
    simp only [abs_zero, add_zero, one_pow, mul_one] at h
    exact (norm_nonneg _).trans h

  have hgeo : ∀ z : ℂ, σL ≤ z.re → z.re ≤ σR →
      1 ≤ ‖z - c‖ ∧ (1 + |z.im|) / 2 ≤ ‖z - c‖ ∧ ‖z - c‖ ≤ W * (1 + |z.im|) ∧ z - c ≠ 0 := by
    intro z h1 h2
    have hre : (z - c).re = z.re - c := by rw [Complex.sub_re, Complex.ofReal_re]
    have him : (z - c).im = z.im := by rw [Complex.sub_im, Complex.ofReal_im, sub_zero]
    have hre1 : 1 ≤ (z - c).re := by rw [hre, hc_def]; linarith
    have hn1 : (z - c).re ≤ ‖z - c‖ := Complex.re_le_norm (z - c)
    have hn2 : |(z - c).im| ≤ ‖z - c‖ := Complex.abs_im_le_norm (z - c)
    rw [him] at hn2
    have hn3 : ‖z - c‖ ≤ |(z - c).re| + |(z - c).im| := Complex.norm_le_abs_re_add_abs_im (z - c)
    rw [him, abs_of_pos (by linarith : 0 < (z - (c : ℂ)).re), hre] at hn3
    have h3 : z.re - c ≤ W := by rw [hc_def, hW_def]; linarith
    have h4 : 0 ≤ |z.im| := abs_nonneg _
    refine ⟨by linarith, by linarith, by nlinarith, ?_⟩
    intro h0
    rw [h0, Complex.zero_re] at hre1
    linarith

  set g : ℂ → ℂ := fun z => F z / (z - c) ^ N with hg_def'

  have hbd : ∀ z : ℂ, σL ≤ z.re → z.re ≤ σR → ‖F z‖ ≤ A * (1 + |z.im|) ^ N →
      ‖g z‖ ≤ A * 2 ^ N := by
    intro z h1 h2 hFz
    obtain ⟨-, hlow, -, hne⟩ := hgeo z h1 h2
    have hpos : 0 < ‖z - c‖ ^ N := pow_pos (norm_pos_iff.2 hne) N
    simp only [hg_def']
    rw [norm_div, norm_pow, div_le_iff₀ hpos]
    calc ‖F z‖ ≤ A * (1 + |z.im|) ^ N := hFz
      _ ≤ A * (2 * ‖z - c‖) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) N) hA0
      _ = A * 2 ^ N * ‖z - c‖ ^ N := by rw [mul_pow]; ring
  have hle_a : ∀ z : ℂ, z.re = σL → ‖g z‖ ≤ A * 2 ^ N := by
    intro z hz
    have hz' : (σL : ℂ) + (z.im : ℂ) * Complex.I = z := by
      apply Complex.ext <;> simp [hz]
    have h := hL z.im
    rw [hz'] at h
    exact hbd z hz.ge (by rw [hz]; exact hσ.le) h
  have hle_b : ∀ z : ℂ, z.re = σR → ‖g z‖ ≤ A * 2 ^ N := by
    intro z hz
    have hz' : (σR : ℂ) + (z.im : ℂ) * Complex.I = z := by
      apply Complex.ext <;> simp [hz]
    have h := hR z.im
    rw [hz'] at h
    exact hbd z (by rw [hz]; exact hσ.le) hz.le h

  have hdiff : DiffContOnCl ℂ g (re ⁻¹' Ioo σL σR) := by
    apply DifferentiableOn.diffContOnCl
    have hcl : closure (re ⁻¹' Ioo σL σR) ⊆ {z : ℂ | c < z.re} := by
      refine (closure_minimal (preimage_mono Ioo_subset_Icc_self)
        (isClosed_Icc.preimage Complex.continuous_re)).trans ?_
      intro z hz
      simp only [mem_preimage, mem_Icc] at hz
      simp only [mem_setOf_eq]
      rw [hc_def]
      linarith [hz.1]
    refine DifferentiableOn.mono ?_ hcl
    intro z hz
    simp only [mem_setOf_eq] at hz
    have hne : (z - (c : ℂ)) ^ N ≠ 0 := by
      apply pow_ne_zero
      intro h0
      have hre0 : (z - (c : ℂ)).re = 0 := by rw [h0, Complex.zero_re]
      rw [Complex.sub_re, Complex.ofReal_re] at hre0
      linarith
    simp only [hg_def']
    exact (hF z).differentiableWithinAt.div
      ((differentiableWithinAt_id.sub_const (c : ℂ)).fun_pow N) hne

  set M : ℝ := |σL| + |σR| with hM_def
  have hM0 : 0 ≤ M := by rw [hM_def]; positivity
  have hnorm : ∀ z : ℂ, σL ≤ z.re → z.re ≤ σR → ‖z‖ ≤ M + |z.im| := by
    intro z h1 h2
    have h := Complex.norm_le_abs_re_add_abs_im z
    have habs : |z.re| ≤ M :=
      abs_le.2 ⟨by linarith [neg_abs_le σL, abs_nonneg σR, hM_def],
        by linarith [le_abs_self σR, abs_nonneg σL, hM_def]⟩
    linarith
  set κ : ℝ := Real.pi / (2 * (σR - σL)) with hκ_def
  have hκpos : 0 < κ := by
    rw [hκ_def]
    exact div_pos Real.pi_pos (by linarith)
  have hκlt : κ < Real.pi / (σR - σL) := by
    rw [hκ_def]
    exact div_lt_div_of_pos_left Real.pi_pos (by linarith) (by linarith)
  have hB : ∃ c' < Real.pi / (σR - σL), ∃ B,
      g =O[comap (_root_.abs ∘ im) atTop ⊓ 𝓟 (re ⁻¹' Ioo σL σR)]
        fun z ↦ Real.exp (B * Real.exp (c' * |z.im|)) := by
    refine ⟨κ, hκlt, |D| + |C| * (4 / κ ^ 2) * Real.exp (κ * (1 + M)), ?_⟩
    refine Asymptotics.IsBigO.of_bound 1
      (Filter.eventually_inf_principal.2 (Filter.Eventually.of_forall fun z hz => ?_))
    simp only [mem_preimage, mem_Ioo] at hz
    obtain ⟨h1c, -, -, -⟩ := hgeo z hz.1.le hz.2.le
    rw [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

    have h1 : ‖g z‖ ≤ ‖F z‖ := by
      simp only [hg_def']
      rw [norm_div, norm_pow]
      exact div_le_self (norm_nonneg _) (one_le_pow₀ h1c)

    have hlogpos : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
    have hp : 0 ≤ ‖z‖ * Real.log (2 + ‖z‖) := mul_nonneg (norm_nonneg _) hlogpos
    have h2 : ‖F z‖ ≤ |D| * Real.exp (|C| * ‖z‖ * Real.log (2 + ‖z‖)) := by
      refine (hg z hz.1.le hz.2.le).trans ?_
      have e1 : Real.exp (C * ‖z‖ * Real.log (2 + ‖z‖)) ≤
          Real.exp (|C| * ‖z‖ * Real.log (2 + ‖z‖)) := by
        apply Real.exp_le_exp.2
        have e2 : C * (‖z‖ * Real.log (2 + ‖z‖)) ≤ |C| * (‖z‖ * Real.log (2 + ‖z‖)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hp
        calc C * ‖z‖ * Real.log (2 + ‖z‖) = C * (‖z‖ * Real.log (2 + ‖z‖)) := by ring
          _ ≤ |C| * (‖z‖ * Real.log (2 + ‖z‖)) := e2
          _ = |C| * ‖z‖ * Real.log (2 + ‖z‖) := by ring
      calc D * Real.exp (C * ‖z‖ * Real.log (2 + ‖z‖)) ≤
          |D| * Real.exp (C * ‖z‖ * Real.log (2 + ‖z‖)) :=
            mul_le_mul_of_nonneg_right (le_abs_self D) (Real.exp_pos _).le
        _ ≤ |D| * Real.exp (|C| * ‖z‖ * Real.log (2 + ‖z‖)) :=
            mul_le_mul_of_nonneg_left e1 (abs_nonneg D)

    have hz1 : ‖z‖ ≤ M + |z.im| := hnorm z hz.1.le hz.2.le
    have hlog : Real.log (2 + ‖z‖) ≤ 1 + ‖z‖ := by
      have hl := Real.log_le_sub_one_of_pos (show 0 < 2 + ‖z‖ by linarith [norm_nonneg z])
      linarith
    set y : ℝ := 1 + M + |z.im| with hy_def
    have hy0 : 0 ≤ y := by rw [hy_def]; positivity
    have h3 : ‖z‖ * Real.log (2 + ‖z‖) ≤ y ^ 2 := by
      have h31 : ‖z‖ * Real.log (2 + ‖z‖) ≤ (M + |z.im|) * (1 + M + |z.im|) :=
        mul_le_mul hz1 (hlog.trans (by linarith)) hlogpos (by positivity)
      have h32 : (M + |z.im|) * (1 + M + |z.im|) ≤ (1 + M + |z.im|) * (1 + M + |z.im|) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      calc ‖z‖ * Real.log (2 + ‖z‖) ≤ (1 + M + |z.im|) * (1 + M + |z.im|) := h31.trans h32
        _ = y ^ 2 := by rw [hy_def]; ring
    have h4 : y ^ 2 ≤ 4 / κ ^ 2 * Real.exp (κ * y) := sq_le_mul_exp κ hκpos y hy0
    have h5 : Real.exp (κ * y) = Real.exp (κ * (1 + M)) * Real.exp (κ * |z.im|) := by
      rw [← Real.exp_add]
      congr 1
      rw [hy_def]
      ring
    have h6 : |C| * ‖z‖ * Real.log (2 + ‖z‖) ≤
        |C| * (4 / κ ^ 2) * Real.exp (κ * (1 + M)) * Real.exp (κ * |z.im|) := by
      have h61 := mul_le_mul_of_nonneg_left (h3.trans h4) (abs_nonneg C)
      rw [h5] at h61
      calc |C| * ‖z‖ * Real.log (2 + ‖z‖) = |C| * (‖z‖ * Real.log (2 + ‖z‖)) := by ring
        _ ≤ |C| * (4 / κ ^ 2 * (Real.exp (κ * (1 + M)) * Real.exp (κ * |z.im|))) := h61
        _ = |C| * (4 / κ ^ 2) * Real.exp (κ * (1 + M)) * Real.exp (κ * |z.im|) := by ring
    have h7 : |D| ≤ Real.exp (|D| * Real.exp (κ * |z.im|)) := by
      have e0 : 1 ≤ Real.exp (κ * |z.im|) := Real.one_le_exp (by positivity)
      calc |D| ≤ |D| * Real.exp (κ * |z.im|) := le_mul_of_one_le_right (abs_nonneg D) e0
        _ ≤ Real.exp (|D| * Real.exp (κ * |z.im|)) := by
            linarith [Real.add_one_le_exp (|D| * Real.exp (κ * |z.im|))]
    calc ‖g z‖ ≤ ‖F z‖ := h1
      _ ≤ |D| * Real.exp (|C| * ‖z‖ * Real.log (2 + ‖z‖)) := h2
      _ ≤ Real.exp (|D| * Real.exp (κ * |z.im|)) *
            Real.exp (|C| * (4 / κ ^ 2) * Real.exp (κ * (1 + M)) * Real.exp (κ * |z.im|)) :=
          mul_le_mul h7 (Real.exp_le_exp.2 h6) (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp ((|D| + |C| * (4 / κ ^ 2) * Real.exp (κ * (1 + M))) *
            Real.exp (κ * |z.im|)) := by
          rw [← Real.exp_add]
          congr 1
          ring

  have hPL : ∀ z : ℂ, σL ≤ z.re → z.re ≤ σR → ‖g z‖ ≤ A * 2 ^ N :=
    fun z h1 h2 => PhragmenLindelof.vertical_strip hdiff hB hle_a hle_b h1 h2

  refine ⟨A * 2 ^ N * W ^ N, N, fun z h1 h2 => ?_⟩
  obtain ⟨-, -, hup, hne⟩ := hgeo z h1 h2
  have hpow : (z - (c : ℂ)) ^ N ≠ 0 := pow_ne_zero _ hne
  have hFg : F z = g z * (z - c) ^ N := by
    simp only [hg_def']
    rw [div_mul_cancel₀ _ hpow]
  rw [hFg, norm_mul, norm_pow]
  have hA2 : 0 ≤ A * 2 ^ N := mul_nonneg hA0 (by positivity)
  calc ‖g z‖ * ‖z - c‖ ^ N ≤ A * 2 ^ N * (W * (1 + |z.im|)) ^ N :=
        mul_le_mul (hPL z h1 h2) (pow_le_pow_left₀ (norm_nonneg _) hup N) (by positivity) hA2
    _ = A * 2 ^ N * W ^ N * (1 + |z.im|) ^ N := by rw [mul_pow]; ring

end StripInterpolation

namespace EulerBound

open NumberField IsDedekindDomain

private theorem prod_le_of_hasProd_of_one_le {ι : Type*} {g : ι → ℝ} {L : ℝ} (hg : HasProd g L)
    (h1 : ∀ i, 1 ≤ g i) (s : Finset ι) : ∏ i ∈ s, g i ≤ L := by
  classical
  have hmono : ∀ t : Finset ι, s ⊆ t → ∏ i ∈ s, g i ≤ ∏ i ∈ t, g i := by
    intro t hst
    rw [← Finset.prod_sdiff hst]
    have hone : 1 ≤ ∏ i ∈ t \ s, g i :=
      Finset.prod_induction _ (fun x => 1 ≤ x)
        (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl (fun i _ => h1 i)
    have hnn : 0 ≤ ∏ i ∈ s, g i := Finset.prod_nonneg fun i _ => zero_le_one.trans (h1 i)
    exact le_mul_of_one_le_left hnn hone
  have hg' : Filter.Tendsto (fun t : Finset ι => ∏ i ∈ t, g i) Filter.atTop (nhds L) := by
    simpa [HasProd] using hg
  exact ge_of_tendsto hg' (Filter.eventually_atTop.2 ⟨s, hmono⟩)

private theorem _root_.EulerBound.one_lt_absNorm (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    1 < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast lt_of_lt_of_le one_lt_two h2

p2m_export "EulerBound" "one_lt_absNorm"

private theorem norm_inv_one_sub_cpow_eq (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (σ₀ : ℝ) (hσ₀ : 1 < σ₀) :
    ‖(1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ₀ : ℂ)))⁻¹‖ =
      (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ₀))⁻¹ := by
  have hN := one_lt_absNorm K v
  have hlt : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hN (by linarith)
  have hcast : (1 : ℂ) - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ₀ : ℂ)) =
      (((1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ₀) : ℝ)) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_cpow (Nat.cast_nonneg _),
      Complex.ofReal_natCast, Complex.ofReal_neg]
  rw [norm_inv, hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]

private theorem one_le_inv_one_sub_rpow (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (σ₀ : ℝ) (hσ₀ : 1 < σ₀) :
    1 ≤ (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ₀))⁻¹ := by
  have hN := one_lt_absNorm K v
  have hlt : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hN (by linarith)
  have hnn : 0 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ₀) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  exact (one_le_inv₀ (by linarith)).2 (by linarith)

private theorem norm_inv_one_sub_mul_cpow_le (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (a : ℂ) (ha : ‖a‖ ≤ 1) (σ₀ : ℝ) (hσ₀ : 1 < σ₀) (w : ℂ)
    (hw : σ₀ ≤ w.re) :
    ‖(1 - a * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹‖ ≤
      (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ₀))⁻¹ := by
  have hN := one_lt_absNorm K v
  have hNpos : 0 < Ideal.absNorm v.asIdeal := by exact_mod_cast zero_lt_one.trans hN
  set N : ℝ := ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) with hN_def
  have hx : ‖a * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))‖ ≤ N ^ (-σ₀) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hNpos, Complex.neg_re]
    calc ‖a‖ * N ^ (-w.re) ≤ 1 * N ^ (-w.re) :=
          mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg (zero_le_one.trans hN.le) _)
      _ = N ^ (-w.re) := one_mul _
      _ ≤ N ^ (-σ₀) := Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
  have hlt : N ^ (-σ₀) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hN (by linarith)
  have hpos : 0 < 1 - N ^ (-σ₀) := by linarith
  have hlow : 1 - N ^ (-σ₀) ≤ ‖1 - a * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w))‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (a * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))
    rw [norm_one] at h
    linarith
  rw [norm_inv]
  exact inv_anti₀ hpos hlow

private theorem exists_forall_norm_tprod_le (K : Type) [Field K] [NumberField K]
    (T : Finset (HeightOneSpectrum (𝓞 K))) (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ v, ‖a v‖ ≤ 1)
    (σ₀ : ℝ) (hσ₀ : 1 < σ₀) :
    ∃ B : ℝ, ∀ w : ℂ, σ₀ ≤ w.re →
      ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - a v.1 * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹‖ ≤ B := by

  have hσ₀' : 1 < ((σ₀ : ℂ)).re := by rwa [Complex.ofReal_re]
  have hkey : ∀ v : HeightOneSpectrum (𝓞 K),
      ‖(1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(σ₀ : ℂ)))⁻¹‖ =
        (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ₀))⁻¹ :=
    fun v => norm_inv_one_sub_cpow_eq K v σ₀ hσ₀
  have hP : HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
      (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ₀))⁻¹)
      ‖NumberField.dedekindZeta K (σ₀ : ℂ)‖ := by
    have h := (NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta K (σ₀ : ℂ) hσ₀').norm
    simp only [hkey] at h
    exact h
  have h1g : ∀ v : HeightOneSpectrum (𝓞 K),
      1 ≤ (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ₀))⁻¹ :=
    fun v => one_le_inv_one_sub_rpow K v σ₀ hσ₀
  have h1B : 1 ≤ ‖NumberField.dedekindZeta K (σ₀ : ℂ)‖ := by
    simpa using prod_le_of_hasProd_of_one_le hP h1g ∅
  refine ⟨‖NumberField.dedekindZeta K (σ₀ : ℂ)‖, fun w hw => ?_⟩
  set f : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} → ℂ :=
    fun v => (1 - a v.1 * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹ with hf_def
  by_cases hm : Multipliable f
  · rw [hm.norm_tprod]
    refine tprod_le_of_prod_le' h1B fun s => ?_
    have hle : ∀ i ∈ s, ‖f i‖ ≤ (1 - ((Ideal.absNorm i.1.asIdeal : ℕ) : ℝ) ^ (-σ₀))⁻¹ := by
      intro i _
      simp only [hf_def]
      exact norm_inv_one_sub_mul_cpow_le K i.1 (a i.1) (ha i.1) σ₀ hσ₀ w hw
    calc ∏ i ∈ s, ‖f i‖ ≤ ∏ i ∈ s, (1 - ((Ideal.absNorm i.1.asIdeal : ℕ) : ℝ) ^ (-σ₀))⁻¹ :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) hle
      _ = ∏ v ∈ s.map (Function.Embedding.subtype _),
            (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ₀))⁻¹ := by
          rw [Finset.prod_map]
          rfl
      _ ≤ ‖NumberField.dedekindZeta K (σ₀ : ℂ)‖ := prod_le_of_hasProd_of_one_le hP h1g _
  · rw [tprod_eq_one_of_not_multipliable hm, norm_one]
    exact h1B

end EulerBound

namespace EulerSpellingBridge

private theorem one_lt_absNorm (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    1 < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast lt_of_lt_of_le one_lt_two h2

private theorem one_sub_mul_cpow_ne_zero (K : Type) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a : ℂ) (ha : ‖a‖ ≤ 1) (s : ℂ) (hs : 0 < s.re) :
    1 - a * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) ≠ 0 := by
  have hN := one_lt_absNorm K v
  have hNpos : 0 < Ideal.absNorm v.asIdeal := by exact_mod_cast zero_lt_one.trans hN
  intro h0
  have h1 : a * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) = 1 := (sub_eq_zero.1 h0).symm
  have h2 : ‖a * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hNpos, Complex.neg_re]
    have hlt : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hN (by linarith)
    have hnn : 0 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    nlinarith [norm_nonneg a]
  rw [h1, norm_one] at h2
  exact lt_irrefl _ h2

private theorem norm_prod_one_sub_mul_cpow_le (K : Type) [Field K] [NumberField K]
    (U : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (a : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℂ) (ha : ∀ v, ‖a v‖ ≤ 1)
    (σ : ℝ) (s : ℂ) (hs : σ ≤ s.re) :
    ‖∏ v ∈ U, (1 - a v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))‖ ≤
      ∏ v ∈ U, (1 + ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ)) := by
  rw [norm_prod]
  refine Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => ?_
  have hN := one_lt_absNorm K v
  have hNpos : 0 < Ideal.absNorm v.asIdeal := by exact_mod_cast zero_lt_one.trans hN
  have h1 : ‖a v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))‖ ≤
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hNpos, Complex.neg_re]
    have hnn : 0 ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hmono :
        ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-s.re) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
    nlinarith [ha v, norm_nonneg (a v)]
  calc ‖1 - a v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))‖
      ≤ ‖(1 : ℂ)‖ + ‖a v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))‖ := norm_sub_le _ _
    _ ≤ 1 + ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) := by rw [norm_one]; linarith

private theorem euler_compare (K : Type) [Field K] [NumberField K]
    (χ : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ →* ℂˣ)
    (hcf : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ‖((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ)‖ ≤ 1)
    (S T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (b : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℂ) (hbS : ∀ v, v ∈ S → b v = 0)
    (hbS' : ∀ v, v ∉ S → b v = ((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ))
    (s : ℂ) (hs : 1 < s.re) (Ls : ℂ)
    (hLs : Ls = ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ T},
          (1 - b v.1 * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    (∏' v : {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S},
        (1 - ((χ (AutomorphicForm.uniformizerIdele K v.1) : ℂˣ) : ℂ) * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^
            (-s)))⁻¹) =
      (∏ v ∈ T, (1 - b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) * Ls := by
  classical

  obtain ⟨g, hg_def⟩ : ∃ g : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℂ, g = fun v =>
      if v ∈ S then 1 else
        (1 - ((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ) * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ :=
    ⟨_, rfl⟩
  have hg_mem : ∀ v, v ∈ S → g v = 1 := fun v hv => by rw [hg_def]; exact if_pos hv
  have hg_nmem : ∀ v, v ∉ S → g v =
      (1 - ((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ) * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ :=
    fun v hv => by rw [hg_def]; exact if_neg hv

  have h1 : Ls = ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ T}, g v.1 := by
    rw [hLs]
    refine tprod_congr fun v => ?_
    by_cases hv : v.1 ∈ S
    · rw [hbS v.1 hv, hg_mem v.1 hv]
      simp
    · rw [hbS' v.1 hv, hg_nmem v.1 hv]

  have h2 : (∏' v : {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S},
        (1 - ((χ (AutomorphicForm.uniformizerIdele K v.1) : ℂˣ) : ℂ) * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^
            (-s)))⁻¹) =
      ∏' v, g v := by
    have h := tprod_subtype ((↑S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))ᶜ) (fun v =>
      (1 - ((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ) * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
    refine h.trans (tprod_congr fun v => ?_)
    rw [Set.mulIndicator_apply]
    by_cases hv : v ∈ S
    · rw [if_neg (by simpa using hv), hg_mem v hv]
    · rw [if_pos (by simpa using hv), hg_nmem v hv]

  have hR := fun (U : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (z : {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ U} → ℂ) (hz : ∀ v, ‖z v‖ ≤ 1) =>
    (NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one K U z hz).1 s hs
  have hgm : Multipliable g := by
    have h := hR S (fun v => ((χ (AutomorphicForm.uniformizerIdele K v.1) : ℂˣ) : ℂ)) (fun v => hcf v.1)
    have h' : Multipliable
        (((↑S : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))ᶜ).mulIndicator fun v =>
        (1 - ((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ) * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^
            (-s)))⁻¹) :=
      multipliable_subtype_iff_mulIndicator.1 h
    refine h'.congr fun v => ?_
    rw [Set.mulIndicator_apply]
    by_cases hv : v ∈ S
    · rw [if_neg (by simpa using hv), hg_mem v hv]
    · rw [if_pos (by simpa using hv), hg_nmem v hv]
  have hgT : Multipliable
      fun v : {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ T} => g v.1 := by
    have h := hR T (fun v => b v.1)
      (fun v => by
        by_cases hv : v.1 ∈ S
        · rw [hbS v.1 hv, norm_zero]; exact zero_le_one
        · rw [hbS' v.1 hv]; exact hcf v.1)
    refine h.congr fun v => ?_
    by_cases hv : v.1 ∈ S
    · rw [hbS v.1 hv, hg_mem v.1 hv]
      simp
    · rw [hbS' v.1 hv, hg_nmem v.1 hv]

  have hsplit : (∏' v, g v) = (∏ v ∈ T, g v) *
      ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ T}, g v.1 :=
    hgm.hasProd.unique ((T.hasProd g).mul_compl hgT.hasProd)
  have hfin : (∏ v ∈ T, g v) = ∏ v ∈ T, (1 - b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
    refine Finset.prod_congr rfl fun v _ => ?_
    by_cases hv : v ∈ S
    · rw [hg_mem v hv, hbS v hv]
      simp
    · rw [hg_nmem v hv, hbS' v hv]
  rw [h2, hsplit, hfin, ← h1]

private theorem euler_compare_empty (K : Type) [Field K] [NumberField K]
    (χ : (NumberField.AdeleRing (NumberField.RingOfIntegers K) K)ˣ →* ℂˣ)
    (hcf : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      ‖((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ)‖ ≤ 1)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))
    (b : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) → ℂ) (hbS : ∀ v, v ∈ S → b v = 0)
    (hbS' : ∀ v, v ∉ S → b v = ((χ (AutomorphicForm.uniformizerIdele K v) : ℂˣ) : ℂ))
    (s : ℂ) (hs : 1 < s.re) (Ls : ℂ)
    (hLs : Ls = ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) //
        v ∉ (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)))},
          (1 - b v.1 * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    (∏' v : {v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) // v ∉ S},
        (1 - ((χ (AutomorphicForm.uniformizerIdele K v.1) : ℂˣ) : ℂ) * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^
            (-s)))⁻¹) =
      Ls := by
  have h := euler_compare K χ hcf S ∅ b hbS hbS' s hs Ls hLs
  rw [Finset.prod_empty, one_mul] at h
  exact h

end EulerSpellingBridge

namespace HeckeCharacterConvexity

open Complex

private theorem isCompact_rect (σa σb : ℝ) : IsCompact {z : ℂ | σa ≤ z.re ∧ z.re ≤ σb ∧ |z.im| ≤ 2} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have h1 : IsClosed {z : ℂ | σa ≤ z.re} := isClosed_le continuous_const Complex.continuous_re
    have h2 : IsClosed {z : ℂ | z.re ≤ σb} := isClosed_le Complex.continuous_re continuous_const
    have h3 : IsClosed {z : ℂ | |z.im| ≤ 2} :=
      isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
    simpa only [Set.setOf_and] using h1.inter (h2.inter h3)
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨|σa| + |σb| + 2, fun z hz => ?_⟩
    obtain ⟨hza, hzb, hzi⟩ := hz
    have hre : |z.re| ≤ |σa| + |σb| := by
      rw [abs_le]
      constructor <;> linarith [neg_abs_le σa, le_abs_self σb, abs_nonneg σa, abs_nonneg σb]
    linarith [Complex.norm_le_abs_re_add_abs_im z]

private theorem norm_Gamma_inv_le_of_exp_le {w : ℂ} {A : ℝ} {N : ℕ}
    (hlow : Real.exp (-(Real.pi / 2) * |w.im|) ≤ A * (1 + |w.im|) ^ N * ‖Complex.Gamma w‖) :
    ‖Complex.Gamma w‖⁻¹ ≤ Real.exp (Real.pi / 2 * |w.im|) * (A * (1 + |w.im|) ^ N) := by
  have hΓ : Complex.Gamma w ≠ 0 := by
    intro h0
    rw [h0, norm_zero, mul_zero] at hlow
    exact absurd hlow (not_le.2 (Real.exp_pos _))
  have hΓpos : 0 < ‖Complex.Gamma w‖ := norm_pos_iff.2 hΓ
  have h1 : Real.exp (-(Real.pi / 2) * |w.im|) * ‖Complex.Gamma w‖⁻¹ ≤ A * (1 + |w.im|) ^ N := by
    have h := mul_le_mul_of_nonneg_right hlow (inv_nonneg.2 (norm_nonneg (Complex.Gamma w)))
    rwa [mul_assoc, mul_inv_cancel₀ hΓpos.ne', mul_one] at h
  have h2 : ‖Complex.Gamma w‖⁻¹ =
      Real.exp (Real.pi / 2 * |w.im|) * (Real.exp (-(Real.pi / 2) * |w.im|) * ‖Complex.Gamma w‖⁻¹) := by
    rw [← mul_assoc, ← Real.exp_add, show Real.pi / 2 * |w.im| + -(Real.pi / 2) * |w.im| = 0 by ring,
      Real.exp_zero, one_mul]
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le

private theorem exists_norm_Gammaℝ_inv_le (σa σb : ℝ) :
    ∃ (A : ℝ) (N : ℕ), 0 ≤ A ∧ ∀ z : ℂ, σa ≤ z.re → z.re ≤ σb →
      ‖(Gammaℝ z)⁻¹‖ ≤ A * (1 + |z.im|) ^ N * Real.exp (Real.pi / 4 * |z.im|) := by
  obtain ⟨A, N, hG⟩ :=
    Complex.exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im
      (σa / 2) (σb / 2)
  obtain ⟨M, hM⟩ :=
    (isCompact_rect σa σb).exists_bound_of_continuousOn differentiable_Gammaℝ_inv.continuous.continuousOn
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
  refine ⟨max M 0 + Real.pi ^ (σb / 2) * max A 0, N, by positivity, fun z hza hzb => ?_⟩
  have hK0 : 0 ≤ Real.pi ^ (σb / 2) * max A 0 := by positivity
  have hpow1 : (1 : ℝ) ≤ (1 + |z.im|) ^ N := one_le_pow₀ (by linarith [abs_nonneg z.im])
  have hexp1 : (1 : ℝ) ≤ Real.exp (Real.pi / 4 * |z.im|) := Real.one_le_exp (by positivity)
  by_cases him : |z.im| ≤ 2
  · have h1 : ‖(Gammaℝ z)⁻¹‖ ≤ M := hM z ⟨hza, hzb, him⟩
    calc ‖(Gammaℝ z)⁻¹‖ ≤ max M 0 + Real.pi ^ (σb / 2) * max A 0 :=
          (h1.trans (le_max_left _ _)).trans (le_add_of_nonneg_right hK0)
      _ = (max M 0 + Real.pi ^ (σb / 2) * max A 0) * 1 * 1 := by ring
      _ ≤ (max M 0 + Real.pi ^ (σb / 2) * max A 0) * (1 + |z.im|) ^ N *
            Real.exp (Real.pi / 4 * |z.im|) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hpow1 (by positivity)) hexp1 zero_le_one (by positivity)
  · push Not at him
    have hw1 : σa / 2 ≤ (z / 2).re := by rw [Complex.div_ofNat_re]; linarith
    have hw2 : (z / 2).re ≤ σb / 2 := by rw [Complex.div_ofNat_re]; linarith
    have hyi : (z / 2).im = z.im / 2 := Complex.div_ofNat_im z 2
    have hw3 : 1 ≤ |(z / 2).im| := by rw [hyi, abs_div, abs_two]; linarith
    have hinv := norm_Gamma_inv_le_of_exp_le (hG (z / 2) hw1 hw2 hw3).2
    rw [hyi] at hinv
    have hpre : ‖(Real.pi : ℂ) ^ (-z / 2)‖⁻¹ ≤ Real.pi ^ (σb / 2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, ← Real.rpow_neg Real.pi_pos.le]
      apply Real.rpow_le_rpow_of_exponent_le hpi1
      have : (-z / 2).re = -z.re / 2 := by rw [Complex.div_ofNat_re, Complex.neg_re]
      rw [this]
      linarith
    have hsplit : ‖(Gammaℝ z)⁻¹‖ = ‖(Real.pi : ℂ) ^ (-z / 2)‖⁻¹ * ‖Complex.Gamma (z / 2)‖⁻¹ := by
      rw [Complex.Gammaℝ_def, mul_inv, norm_mul, norm_inv, norm_inv]
    have habs2 : |z.im / 2| = |z.im| / 2 := by rw [abs_div, abs_two]
    have hpoly : (1 + |z.im / 2|) ^ N ≤ (1 + |z.im|) ^ N := by
      rw [habs2]
      exact pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg z.im]) N
    have hexp : Real.exp (Real.pi / 2 * |z.im / 2|) = Real.exp (Real.pi / 4 * |z.im|) := by
      rw [habs2]; congr 1; ring
    rw [hsplit]
    calc ‖(Real.pi : ℂ) ^ (-z / 2)‖⁻¹ * ‖Complex.Gamma (z / 2)‖⁻¹
        ≤ Real.pi ^ (σb / 2) * (Real.exp (Real.pi / 2 * |z.im / 2|) * (A * (1 + |z.im / 2|) ^ N)) :=
          mul_le_mul hpre hinv (inv_nonneg.2 (norm_nonneg _)) (by positivity)
      _ ≤ Real.pi ^ (σb / 2) * (Real.exp (Real.pi / 4 * |z.im|) * (max A 0 * (1 + |z.im|) ^ N)) := by
          rw [hexp]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          exact mul_le_mul (le_max_left _ _) hpoly (by positivity) (le_max_right _ _)
      _ = Real.pi ^ (σb / 2) * max A 0 * (1 + |z.im|) ^ N * Real.exp (Real.pi / 4 * |z.im|) := by ring
      _ ≤ (max M 0 + Real.pi ^ (σb / 2) * max A 0) * (1 + |z.im|) ^ N *
            Real.exp (Real.pi / 4 * |z.im|) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact le_add_of_nonneg_left (le_max_right _ _)

private theorem exists_norm_Gammaℝ_le (σa σb : ℝ) (hσa : 0 < σa) :
    ∃ (A : ℝ) (N : ℕ), 0 ≤ A ∧ ∀ z : ℂ, σa ≤ z.re → z.re ≤ σb →
      ‖Gammaℝ z‖ ≤ A * (1 + |z.im|) ^ N * Real.exp (-(Real.pi / 4) * |z.im|) := by
  obtain ⟨A, N, hG⟩ :=
    Complex.exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im
      (σa / 2) (σb / 2)
  have hcont : ContinuousOn Gammaℝ {z : ℂ | σa ≤ z.re ∧ z.re ≤ σb ∧ |z.im| ≤ 2} := by
    intro z hz
    have hre : ∀ m : ℕ, z / 2 ≠ -m := by
      intro m hm
      have h := congrArg Complex.re hm
      rw [Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re] at h
      linarith [hz.1, m.cast_nonneg (α := ℝ)]
    have h1 : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) z :=
      ((differentiableAt_id.neg).div_const 2).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.2 Real.pi_ne_zero))
    have h2 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) z :=
      (Complex.differentiableAt_Gamma _ hre).comp z (differentiableAt_id.div_const 2)
    have h3 : DifferentiableAt ℂ Gammaℝ z := h1.mul h2
    exact h3.continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_rect σa σb).exists_bound_of_continuousOn hcont
  have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
  refine ⟨max M 0 * Real.exp (Real.pi / 2) + Real.pi ^ (-σa / 2) * max A 0, N, by positivity,
    fun z hza hzb => ?_⟩
  have hK0 : 0 ≤ Real.pi ^ (-σa / 2) * max A 0 := by positivity
  have hpow1 : (1 : ℝ) ≤ (1 + |z.im|) ^ N := one_le_pow₀ (by linarith [abs_nonneg z.im])
  by_cases him : |z.im| ≤ 2
  · have h1 : ‖Gammaℝ z‖ ≤ M := hM z ⟨hza, hzb, him⟩
    have hE : (1 : ℝ) ≤ Real.exp (Real.pi / 2) * Real.exp (-(Real.pi / 4) * |z.im|) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [Real.pi_pos, him, abs_nonneg z.im])
    calc ‖Gammaℝ z‖ ≤ max M 0 := h1.trans (le_max_left _ _)
      _ = max M 0 * 1 * 1 := by ring
      _ ≤ max M 0 * (Real.exp (Real.pi / 2) * Real.exp (-(Real.pi / 4) * |z.im|)) * (1 + |z.im|) ^ N :=
          mul_le_mul (mul_le_mul_of_nonneg_left hE (le_max_right _ _)) hpow1 zero_le_one (by positivity)
      _ = max M 0 * Real.exp (Real.pi / 2) * (1 + |z.im|) ^ N * Real.exp (-(Real.pi / 4) * |z.im|) := by
          ring
      _ ≤ (max M 0 * Real.exp (Real.pi / 2) + Real.pi ^ (-σa / 2) * max A 0) * (1 + |z.im|) ^ N *
            Real.exp (-(Real.pi / 4) * |z.im|) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact le_add_of_nonneg_right hK0
  · push Not at him
    have hw1 : σa / 2 ≤ (z / 2).re := by rw [Complex.div_ofNat_re]; linarith
    have hw2 : (z / 2).re ≤ σb / 2 := by rw [Complex.div_ofNat_re]; linarith
    have hyi : (z / 2).im = z.im / 2 := Complex.div_ofNat_im z 2
    have hw3 : 1 ≤ |(z / 2).im| := by rw [hyi, abs_div, abs_two]; linarith
    have hup := (hG (z / 2) hw1 hw2 hw3).1
    rw [hyi] at hup
    have hpre : ‖(Real.pi : ℂ) ^ (-z / 2)‖ ≤ Real.pi ^ (-σa / 2) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      apply Real.rpow_le_rpow_of_exponent_le hpi1
      have : (-z / 2).re = -z.re / 2 := by rw [Complex.div_ofNat_re, Complex.neg_re]
      rw [this]
      linarith
    have habs2 : |z.im / 2| = |z.im| / 2 := by rw [abs_div, abs_two]
    have hpoly : (1 + |z.im / 2|) ^ N ≤ (1 + |z.im|) ^ N := by
      rw [habs2]
      exact pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg z.im]) N
    have hexp : Real.exp (-(Real.pi / 2) * |z.im / 2|) = Real.exp (-(Real.pi / 4) * |z.im|) := by
      rw [habs2]; congr 1; ring
    rw [Complex.Gammaℝ_def, norm_mul]
    calc ‖(Real.pi : ℂ) ^ (-z / 2)‖ * ‖Complex.Gamma (z / 2)‖
        ≤ Real.pi ^ (-σa / 2) * (A * (1 + |z.im / 2|) ^ N * Real.exp (-(Real.pi / 2) * |z.im / 2|)) :=
          mul_le_mul hpre hup (norm_nonneg _) (by positivity)
      _ ≤ Real.pi ^ (-σa / 2) * (max A 0 * (1 + |z.im|) ^ N * Real.exp (-(Real.pi / 4) * |z.im|)) := by
          rw [hexp]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          exact mul_le_mul (le_max_left _ _) hpoly (by positivity) (le_max_right _ _)
      _ = Real.pi ^ (-σa / 2) * max A 0 * (1 + |z.im|) ^ N * Real.exp (-(Real.pi / 4) * |z.im|) := by ring
      _ ≤ (max M 0 * Real.exp (Real.pi / 2) + Real.pi ^ (-σa / 2) * max A 0) * (1 + |z.im|) ^ N *
            Real.exp (-(Real.pi / 4) * |z.im|) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact le_add_of_nonneg_left (by positivity)

private theorem exists_pair_bound (α β p q : ℝ) (hα : 0 < α) :
    ∃ (A : ℝ) (N : ℕ), 0 ≤ A ∧ ∀ t : ℝ,
      ‖Gammaℝ ((α : ℂ) + ((p : ℂ) - (t : ℂ)) * I)‖ * ‖(Gammaℝ ((β : ℂ) + ((q : ℂ) + (t : ℂ)) * I))⁻¹‖ ≤
        A * (1 + |t|) ^ N := by
  obtain ⟨A₁, N₁, hA₁, h₁⟩ := exists_norm_Gammaℝ_le α α hα
  obtain ⟨A₂, N₂, hA₂, h₂⟩ := exists_norm_Gammaℝ_inv_le β β
  refine ⟨A₁ * A₂ * ((1 + |p|) ^ N₁ * (1 + |q|) ^ N₂ * Real.exp (Real.pi / 4 * (|p| + |q|))), N₁ + N₂,
    mul_nonneg (mul_nonneg hA₁ hA₂) (by positivity), fun t => ?_⟩
  have hre₁ : ((α : ℂ) + ((p : ℂ) - (t : ℂ)) * I).re = α := by simp
  have him₁ : ((α : ℂ) + ((p : ℂ) - (t : ℂ)) * I).im = p - t := by simp
  have hre₂ : ((β : ℂ) + ((q : ℂ) + (t : ℂ)) * I).re = β := by simp
  have him₂ : ((β : ℂ) + ((q : ℂ) + (t : ℂ)) * I).im = q + t := by simp
  have hb₁ := h₁ _ hre₁.ge hre₁.le
  have hb₂ := h₂ _ hre₂.ge hre₂.le
  rw [him₁] at hb₁
  rw [him₂] at hb₂
  have hpt : |p - t| ≤ |p| + |t| := by
    have h := abs_add_le p (-t)
    rwa [← sub_eq_add_neg, abs_neg] at h
  have hqt : |q + t| ≤ |q| + |t| := abs_add_le q t
  have hdiff : |q + t| - |p - t| ≤ |p| + |q| := by
    have h := abs_add_le (t - p) p
    rw [sub_add_cancel, abs_sub_comm] at h
    linarith
  have hP₁ : (1 + |p - t|) ^ N₁ ≤ ((1 + |p|) * (1 + |t|)) ^ N₁ :=
    pow_le_pow_left₀ (by positivity) (by nlinarith [abs_nonneg p, abs_nonneg t]) N₁
  have hP₂ : (1 + |q + t|) ^ N₂ ≤ ((1 + |q|) * (1 + |t|)) ^ N₂ :=
    pow_le_pow_left₀ (by positivity) (by nlinarith [abs_nonneg q, abs_nonneg t]) N₂
  have hE : Real.exp (-(Real.pi / 4) * |p - t|) * Real.exp (Real.pi / 4 * |q + t|) ≤
      Real.exp (Real.pi / 4 * (|p| + |q|)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, hdiff])
  have hnn₁ : 0 ≤ A₁ * (1 + |p - t|) ^ N₁ := mul_nonneg hA₁ (by positivity)
  calc ‖Gammaℝ ((α : ℂ) + ((p : ℂ) - (t : ℂ)) * I)‖ *
        ‖(Gammaℝ ((β : ℂ) + ((q : ℂ) + (t : ℂ)) * I))⁻¹‖
      ≤ (A₁ * (1 + |p - t|) ^ N₁ * Real.exp (-(Real.pi / 4) * |p - t|)) *
          (A₂ * (1 + |q + t|) ^ N₂ * Real.exp (Real.pi / 4 * |q + t|)) :=
        mul_le_mul hb₁ hb₂ (norm_nonneg _) (mul_nonneg hnn₁ (Real.exp_pos _).le)
    _ = (A₁ * A₂) * ((1 + |p - t|) ^ N₁ * (1 + |q + t|) ^ N₂) *
          (Real.exp (-(Real.pi / 4) * |p - t|) * Real.exp (Real.pi / 4 * |q + t|)) := by ring
    _ ≤ (A₁ * A₂) * (((1 + |p|) * (1 + |t|)) ^ N₁ * ((1 + |q|) * (1 + |t|)) ^ N₂) *
          Real.exp (Real.pi / 4 * (|p| + |q|)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul hP₁ hP₂ (by positivity) (by positivity))
          (mul_nonneg hA₁ hA₂)) hE (by positivity) (mul_nonneg (mul_nonneg hA₁ hA₂) (by positivity))
    _ = A₁ * A₂ * ((1 + |p|) ^ N₁ * (1 + |q|) ^ N₂ * Real.exp (Real.pi / 4 * (|p| + |q|))) *
          (1 + |t|) ^ (N₁ + N₂) := by
        rw [mul_pow, mul_pow, pow_add]; ring

private theorem one_add_pow_le_exp (x : ℝ) (N : ℕ) : (1 + |x|) ^ N ≤ Real.exp (N * |x|) := by
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp |x|]) N

private theorem exists_norm_Gammaℝ_inv_shift_le (σa σb : ℝ) (e : ℂ) :
    ∃ (D C : ℝ), 0 ≤ D ∧ 0 ≤ C ∧ ∀ w : ℂ, σa ≤ w.re → w.re ≤ σb →
      ‖(Gammaℝ (w + e))⁻¹‖ ≤ D * Real.exp (C * ‖w‖) := by
  obtain ⟨A, N, hA, h⟩ := exists_norm_Gammaℝ_inv_le (σa + e.re) (σb + e.re)
  refine ⟨A * Real.exp ((N + Real.pi / 4) * ‖e‖), N + Real.pi / 4, mul_nonneg hA (Real.exp_pos _).le,
    by positivity, fun w hwa hwb => ?_⟩
  have h1 : σa + e.re ≤ (w + e).re := by rw [Complex.add_re]; linarith
  have h2 : (w + e).re ≤ σb + e.re := by rw [Complex.add_re]; linarith
  have him : |(w + e).im| ≤ ‖w‖ + ‖e‖ := (Complex.abs_im_le_norm _).trans (norm_add_le _ _)
  calc ‖(Gammaℝ (w + e))⁻¹‖ ≤ A * (1 + |(w + e).im|) ^ N * Real.exp (Real.pi / 4 * |(w + e).im|) :=
        h _ h1 h2
    _ ≤ A * Real.exp (N * |(w + e).im|) * Real.exp (Real.pi / 4 * |(w + e).im|) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (one_add_pow_le_exp _ _) hA)
          (Real.exp_pos _).le
    _ = A * Real.exp ((N + Real.pi / 4) * |(w + e).im|) := by
        rw [mul_assoc, ← Real.exp_add,
          show (N : ℝ) * |(w + e).im| + Real.pi / 4 * |(w + e).im| = (N + Real.pi / 4) * |(w + e).im| by ring]
    _ ≤ A * Real.exp ((N + Real.pi / 4) * (‖w‖ + ‖e‖)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left him (by positivity))) hA
    _ = A * Real.exp ((N + Real.pi / 4) * ‖e‖) * Real.exp ((N + Real.pi / 4) * ‖w‖) := by
        rw [mul_add, Real.exp_add]; ring

private theorem eq_of_eqOn_one_lt_re (f g : ℂ → ℂ) (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : ∀ s : ℂ, 1 < s.re → f s = g s) : f = g := by
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
    show (1 : ℝ) < (2 : ℂ).re
    norm_num
  exact AnalyticOnNhd.eq_of_eventuallyEq (hf.differentiableOn.analyticOnNhd isOpen_univ)
    (hg.differentiableOn.analyticOnNhd isOpen_univ)
    (Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds h2)
      fun s hs => h s hs)

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal

open scoped Classical in

private theorem main (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hχ : IsIdeleClassChar (𝓞 K) K χ) (hχc : Continuous χ)
    (hχu : IsUnitaryChar (𝓞 K) K χ)
    (hχ1 : ∃ x ∈ normOneIdeles K, χ x ≠ 1)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (σ₁ σ₂ : ℝ)
    (L : ℂ → ℂ) (hL : Differentiable ℂ L)
    (hLE : ∀ s : ℂ, 1 < s.re →
        L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → ‖L w‖ ≤ A * (1 + |w.im|) ^ N := by
  classical
  obtain ⟨S, S', m, c, d, Z, D, C₀, hS, -, hC₀, hc, hd, hZ, hZb, hE, hDb, hDual⟩ :=
    exists_differentiable_forall_norm_le_and_eq_mul_prod_GammaReal_mul_tprod_of_isUnitaryChar
      K χ hχ hχc hχu hχ1

  have hu : ∀ x : (AdeleRing (𝓞 K) K)ˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1 := hχu
  have hcf : ∀ v : HeightOneSpectrum (𝓞 K), ‖((χ (uniformizerIdele K v) : ℂˣ) : ℂ)‖ ≤ 1 :=
    fun v => (hu _).le
  have hcf' : ∀ v : HeightOneSpectrum (𝓞 K), ‖(((χ (uniformizerIdele K v))⁻¹ : ℂˣ) : ℂ)‖ ≤ 1 :=
    fun v => le_of_eq (by rw [Units.val_inv_eq_inv_val, norm_inv, hu, inv_one])

  obtain ⟨b, hb_def⟩ : ∃ b : HeightOneSpectrum (𝓞 K) → ℂ,
      b = fun v => if IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0 := ⟨_, rfl⟩
  have hbS : ∀ v, v ∈ S → b v = 0 := fun v hv => by
    simp only [hb_def]
    exact if_neg ((hS v).1 hv)
  have hbS' : ∀ v, v ∉ S → b v = ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) := fun v hv => by
    simp only [hb_def]
    exact if_pos (not_not.1 fun h => hv ((hS v).2 h))
  have hb1 : ∀ v, ‖b v‖ ≤ 1 := fun v => by
    by_cases hv : v ∈ S
    · rw [hbS v hv, norm_zero]; exact zero_le_one
    · rw [hbS' v hv]; exact hcf v
  have hLEb : ∀ s : ℂ, 1 < s.re → L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
      (1 - b v.1 * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := fun s hs => by
    rw [hb_def]; exact hLE s hs

  obtain ⟨σL, hσL_def⟩ : ∃ σL : ℝ, σL = min σ₁ (-1) := ⟨_, rfl⟩
  obtain ⟨σR, hσR_def⟩ : ∃ σR : ℝ, σR = max σ₂ 2 := ⟨_, rfl⟩
  have hσL1 : σL ≤ -1 := by rw [hσL_def]; exact min_le_right _ _
  have hσLσ : σL ≤ σ₁ := by rw [hσL_def]; exact min_le_left _ _
  have hσR2 : 2 ≤ σR := by rw [hσR_def]; exact le_max_right _ _
  have hσRσ : σ₂ ≤ σR := by rw [hσR_def]; exact le_max_left _ _
  have hσ : σL < σR := by linarith

  obtain ⟨Φ, hΦ_def⟩ : ∃ Φ : ℂ → ℂ, Φ = fun s => C₀⁻¹ * (∏ j, (Gammaℝ (s + c j))⁻¹) *
      (∏ v ∈ T, (1 - b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))) * Z s := ⟨_, rfl⟩
  have hΦ_apply : ∀ s : ℂ, Φ s = C₀⁻¹ * (∏ j, (Gammaℝ (s + c j))⁻¹) *
      (∏ v ∈ T, (1 - b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))) * Z s :=
    fun s => by rw [hΦ_def]

  have hΓd : Differentiable ℂ (fun s : ℂ => ∏ j, (Gammaℝ (s + c j))⁻¹) := fun s =>
    (HasFDerivAt.finsetProd (u := Finset.univ) (g := fun j s => (Gammaℝ (s + c j))⁻¹)
      (fun j _ => ((differentiable_Gammaℝ_inv.comp (differentiable_id.add_const (c j))) s).hasFDerivAt)
      ).differentiableAt
  have hPd : Differentiable ℂ (fun s : ℂ => ∏ v ∈ T,
      (1 - b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))) := by
    have hfac : ∀ v : HeightOneSpectrum (𝓞 K), Differentiable ℂ (fun s : ℂ =>
        (1 - b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))) := by
      intro v
      have hN : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
        have h := EulerSpellingBridge.one_lt_absNorm K v
        exact_mod_cast (zero_lt_one.trans h).ne'
      exact (differentiable_const _).sub ((differentiable_const _).mul
        (differentiable_id.neg.const_cpow (Or.inl hN)))
    exact fun s => (HasFDerivAt.finsetProd (u := T) (g := fun v s =>
      (1 - b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))))
      (fun v _ => ((hfac v) s).hasFDerivAt)).differentiableAt
  have hΦd : Differentiable ℂ Φ := by
    rw [hΦ_def]
    exact (((differentiable_const _).mul hΓd).mul hPd).mul hZ

  have hLΦ : ∀ s : ℂ, 1 < s.re → L s = Φ s := by
    intro s hs
    have hZs : Z s = C₀ * (∏ j, Gammaℝ (s + c j)) *
        ((∏ v ∈ T, (1 - b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) * L s) := by
      rw [hE s hs, EulerSpellingBridge.euler_compare K χ hcf S T b hbS hbS' s hs (L s) (hLEb s hs)]
    have hΓne : ∀ j, Gammaℝ (s + c j) ≠ 0 := fun j =>
      Gammaℝ_ne_zero_of_re_pos (by rw [Complex.add_re]; linarith [hc j])
    have hEne : ∀ v : HeightOneSpectrum (𝓞 K),
        (1 - b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))) ≠ 0 :=
      fun v => EulerSpellingBridge.one_sub_mul_cpow_ne_zero K v _ (hb1 v) s (by linarith)
    have hA : C₀⁻¹ * C₀ = 1 := inv_mul_cancel₀ hC₀
    have hB : (∏ j, (Gammaℝ (s + c j))⁻¹) * (∏ j, Gammaℝ (s + c j)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun j _ => inv_mul_cancel₀ (hΓne j)
    have hC : (∏ v ∈ T, (1 - b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))) *
        (∏ v ∈ T, (1 - b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun v _ => mul_inv_cancel₀ (hEne v)
    rw [hΦ_apply, hZs]
    calc L s = 1 * 1 * 1 * L s := by ring
      _ = (C₀⁻¹ * C₀) * ((∏ j, (Gammaℝ (s + c j))⁻¹) * (∏ j, Gammaℝ (s + c j))) *
            ((∏ v ∈ T, (1 - b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))) *
              (∏ v ∈ T, (1 - b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)) * L s := by
          rw [hA, hB, hC]
      _ = _ := by ring

  have hLΦ' : ∀ w : ℂ, L w = Φ w := fun w => congrFun (eq_of_eqOn_one_lt_re L Φ hL hΦd hLΦ) w

  obtain ⟨P₀, hP₀_def⟩ : ∃ P₀ : ℝ, P₀ = ∏ v ∈ T, (1 + ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σL)) :=
    ⟨_, rfl⟩
  have hP₀ : 0 ≤ P₀ := by rw [hP₀_def]; positivity
  have hPT : ∀ w : ℂ, σL ≤ w.re →
      ‖∏ v ∈ T, (1 - b v * (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w)))‖ ≤ P₀ :=
    fun w hw => by
      rw [hP₀_def]
      exact EulerSpellingBridge.norm_prod_one_sub_mul_cpow_le K _ b hb1 σL w hw
  obtain ⟨CZ, hCZ⟩ := hZb σL σR
  have hCZ0 : 0 ≤ CZ := (norm_nonneg _).trans (hCZ (σR : ℂ) (by simp; linarith) (by simp))

  choose Dj Cj hDj hCj hinvj using fun j => exists_norm_Gammaℝ_inv_shift_le σL σR (c j)
  have hCtot : 0 ≤ ∑ j, Cj j := Finset.sum_nonneg fun j _ => hCj j
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hg : ∀ z : ℂ, σL ≤ z.re → z.re ≤ σR →
      ‖L z‖ ≤ (‖C₀⁻¹‖ * (∏ j, Dj j) * P₀ * CZ) *
        Real.exp ((∑ j, Cj j) / Real.log 2 * ‖z‖ * Real.log (2 + ‖z‖)) := by
    intro z hz1 hz2
    have hΓ : ‖∏ j, (Gammaℝ (z + c j))⁻¹‖ ≤ (∏ j, Dj j) * Real.exp ((∑ j, Cj j) * ‖z‖) := by
      rw [norm_prod, Finset.sum_mul, Real.exp_sum, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => hinvj j z hz1 hz2
    have hexp : Real.exp ((∑ j, Cj j) * ‖z‖) ≤
        Real.exp ((∑ j, Cj j) / Real.log 2 * ‖z‖ * Real.log (2 + ‖z‖)) := by
      apply Real.exp_le_exp.2
      have hlogle : Real.log 2 ≤ Real.log (2 + ‖z‖) := Real.log_le_log two_pos (by linarith [norm_nonneg z])
      have h := mul_le_mul_of_nonneg_left hlogle
        (mul_nonneg (div_nonneg hCtot hlog2.le) (norm_nonneg z))
      have hc2 : (∑ j, Cj j) / Real.log 2 * Real.log 2 = ∑ j, Cj j := div_mul_cancel₀ _ hlog2.ne'
      calc (∑ j, Cj j) * ‖z‖ = (∑ j, Cj j) / Real.log 2 * Real.log 2 * ‖z‖ := by rw [hc2]
        _ = (∑ j, Cj j) / Real.log 2 * ‖z‖ * Real.log 2 := by ring
        _ ≤ _ := h
    rw [hLΦ' z, hΦ_apply, norm_mul, norm_mul, norm_mul]
    have s1 : ‖C₀⁻¹‖ * ‖∏ j, (Gammaℝ (z + c j))⁻¹‖ ≤
        ‖C₀⁻¹‖ * ((∏ j, Dj j) * Real.exp ((∑ j, Cj j) * ‖z‖)) :=
      mul_le_mul_of_nonneg_left hΓ (norm_nonneg _)
    have hD0 : 0 ≤ (∏ j, Dj j) := Finset.prod_nonneg fun j _ => hDj j
    have s2 := mul_le_mul s1 (hPT z hz1) (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (mul_nonneg hD0 (Real.exp_pos _).le))
    have s3 := mul_le_mul s2 (hCZ z hz1 hz2) (norm_nonneg _)
      (mul_nonneg (mul_nonneg (norm_nonneg _) (mul_nonneg hD0 (Real.exp_pos _).le)) hP₀)
    refine s3.trans ?_
    have h4 : 0 ≤ ‖C₀⁻¹‖ * (∏ j, Dj j) * P₀ * CZ :=
      mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) hD0) hP₀) hCZ0
    calc ‖C₀⁻¹‖ * ((∏ j, Dj j) * Real.exp ((∑ j, Cj j) * ‖z‖)) * P₀ * CZ
        = (‖C₀⁻¹‖ * (∏ j, Dj j) * P₀ * CZ) * Real.exp ((∑ j, Cj j) * ‖z‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp h4

  obtain ⟨B, hB⟩ := EulerBound.exists_forall_norm_tprod_le K T b hb1 2 one_lt_two
  have hRline : ∀ t : ℝ, ‖L (σR + t * Complex.I)‖ ≤ B := fun t => by
    have hw : 1 < ((σR : ℂ) + (t : ℂ) * Complex.I).re := by simp; linarith
    rw [hLEb _ hw]
    exact hB _ (by simp; linarith)

  obtain ⟨D₀, hD₀⟩ := hDb (1 - σL)
  obtain ⟨B', hB'⟩ := EulerBound.exists_forall_norm_tprod_le K S'
    (fun v => (((χ (uniformizerIdele K v))⁻¹ : ℂˣ) : ℂ)) hcf' 2 one_lt_two
  choose Aj Nj hAj hpair using fun j =>
    exists_pair_bound (1 - σL + (d j).re) (σL + (c j).re) (d j).im (c j).im (by linarith [hd j])
  have hD₀0 : 0 ≤ D₀ := (norm_nonneg _).trans (hD₀ ((1 - σL : ℝ) : ℂ) (by simp; linarith) (by simp))
  have hB'0 : 0 ≤ B' := (norm_nonneg _).trans (hB' ((2 : ℝ) : ℂ) (by simp))
  have hAprod : 0 ≤ ∏ j, Aj j := Finset.prod_nonneg fun j _ => hAj j
  have hLline : ∀ t : ℝ, ‖L (σL + t * Complex.I)‖ ≤
      (‖C₀⁻¹‖ * D₀ * B' * P₀ * ∏ j, Aj j) * (1 + |t|) ^ (∑ j, Nj j) := by
    intro t
    have hs : 1 < (1 - ((σL : ℂ) + (t : ℂ) * Complex.I)).re := by simp; linarith
    have hZw : Z ((σL : ℂ) + (t : ℂ) * Complex.I) =
        D (1 - ((σL : ℂ) + (t : ℂ) * Complex.I)) *
          (∏ j, Gammaℝ (1 - ((σL : ℂ) + (t : ℂ) * Complex.I) + d j)) *
          ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S'},
            (1 - (((χ (uniformizerIdele K v.1))⁻¹ : ℂˣ) : ℂ) *
              (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(1 - ((σL : ℂ) + (t : ℂ) * Complex.I)))))⁻¹ := by
      have h := hDual (1 - ((σL : ℂ) + (t : ℂ) * Complex.I)) hs
      rwa [sub_sub_cancel] at h

    have hpairs : ‖∏ j, (Gammaℝ (1 - ((σL : ℂ) + (t : ℂ) * Complex.I) + d j) *
        (Gammaℝ (((σL : ℂ) + (t : ℂ) * Complex.I) + c j))⁻¹)‖ ≤ (∏ j, Aj j) * (1 + |t|) ^ (∑ j, Nj j) := by
      rw [norm_prod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_le_prod (fun j _ => norm_nonneg _) fun j _ => ?_
      have e1 : 1 - ((σL : ℂ) + (t : ℂ) * Complex.I) + d j =
          ((1 - σL + (d j).re : ℝ) : ℂ) + ((((d j).im : ℝ) : ℂ) - (t : ℂ)) * I := by
        apply Complex.ext <;> simp
        ring
      have e2 : ((σL : ℂ) + (t : ℂ) * Complex.I) + c j =
          ((σL + (c j).re : ℝ) : ℂ) + ((((c j).im : ℝ) : ℂ) + (t : ℂ)) * I := by
        apply Complex.ext <;> simp
        ring
      rw [norm_mul, e1, e2]
      exact hpair j t
    rw [hLΦ' _, hΦ_apply, hZw]
    have hrearr : ∀ (a gi pt dd gd ls : ℂ), a * gi * pt * (dd * gd * ls) = a * dd * ls * pt * (gd * gi) := by
      intros; ring
    rw [hrearr, ← Finset.prod_mul_distrib, norm_mul, norm_mul, norm_mul, norm_mul]
    have hDv : ‖D (1 - ((σL : ℂ) + (t : ℂ) * Complex.I))‖ ≤ D₀ := hD₀ _ (by simp; linarith) (by simp)
    have hLSv := hB' (1 - ((σL : ℂ) + (t : ℂ) * Complex.I)) (by simp; linarith)
    have hPTv := hPT ((σL : ℂ) + (t : ℂ) * Complex.I) (by simp)
    have s1 : ‖C₀⁻¹‖ * ‖D (1 - ((σL : ℂ) + (t : ℂ) * Complex.I))‖ ≤ ‖C₀⁻¹‖ * D₀ :=
      mul_le_mul_of_nonneg_left hDv (norm_nonneg _)
    have s2 := mul_le_mul s1 hLSv (norm_nonneg _) (mul_nonneg (norm_nonneg _) hD₀0)
    have s3 := mul_le_mul s2 hPTv (norm_nonneg _) (mul_nonneg (mul_nonneg (norm_nonneg _) hD₀0) hB'0)
    have s4 := mul_le_mul s3 hpairs (norm_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) hD₀0) hB'0) hP₀)
    refine s4.trans (le_of_eq ?_)
    ring

  have hK : 0 ≤ ‖C₀⁻¹‖ * D₀ * B' * P₀ * ∏ j, Aj j :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) hD₀0) hB'0) hP₀) hAprod
  have hAbig : 0 ≤ max B 1 + ‖C₀⁻¹‖ * D₀ * B' * P₀ * ∏ j, Aj j := add_nonneg (by positivity) hK
  have hL2 : ∀ t : ℝ, ‖L (σL + t * Complex.I)‖ ≤
      (max B 1 + ‖C₀⁻¹‖ * D₀ * B' * P₀ * ∏ j, Aj j) * (1 + |t|) ^ (∑ j, Nj j) := fun t =>
    (hLline t).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by positivity))
  have hR2 : ∀ t : ℝ, ‖L (σR + t * Complex.I)‖ ≤
      (max B 1 + ‖C₀⁻¹‖ * D₀ * B' * P₀ * ∏ j, Aj j) * (1 + |t|) ^ (∑ j, Nj j) := fun t => by
    have h1 : B ≤ max B 1 + ‖C₀⁻¹‖ * D₀ * B' * P₀ * ∏ j, Aj j :=
      (le_max_left _ _).trans (le_add_of_nonneg_right hK)
    have h2 : (1 : ℝ) ≤ (1 + |t|) ^ (∑ j, Nj j) := one_le_pow₀ (by linarith [abs_nonneg t])
    calc ‖L (σR + t * Complex.I)‖ ≤ B := hRline t
      _ ≤ (max B 1 + ‖C₀⁻¹‖ * D₀ * B' * P₀ * ∏ j, Aj j) * 1 := by rw [mul_one]; exact h1
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hAbig

  obtain ⟨A', N', hPL⟩ := StripInterpolation.exists_forall_norm_le_mul_pow L hL σL σR hσ
    ((∑ j, Cj j) / Real.log 2) (‖C₀⁻¹‖ * (∏ j, Dj j) * P₀ * CZ) hg
    (max B 1 + ‖C₀⁻¹‖ * D₀ * B' * P₀ * ∏ j, Aj j) (∑ j, Nj j) hL2 hR2
  exact ⟨A', N', fun w h1 h2 => hPL w (hσLσ.trans h1) (h2.trans hσRσ)⟩

end HeckeCharacterConvexity

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal

open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hχ : IsIdeleClassChar (𝓞 K) K χ) (_hχc : Continuous χ)
    (_hχu : IsUnitaryChar (𝓞 K) K χ)
    (_hχ1 : ∃ x ∈ normOneIdeles K, χ x ≠ 1)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (σ₁ σ₂ : ℝ)
    (L : ℂ → ℂ) (_hL : Differentiable ℂ L)
    (_hLE : ∀ s : ℂ, 1 < s.re →
        L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt χ v.1 then ((χ (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → ‖L w‖ ≤ A * (1 + |w.im|) ^ N := by
  exact HeckeCharacterConvexity.main K χ _hχ _hχc _hχu _hχ1 T σ₁ σ₂ L _hL _hLE

end S_NumberField_TateGlobal_exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_forall_norm_le_mul_of_differentiable_of_eq_partialEulerProduct_of_re_mem_Icc (solution)
