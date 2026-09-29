-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.forall_integral_mul_modulus_det_cpow_eq_finsum_of_eqOn_of_forall_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/db3d7a45-b886-5330-9c5e-1a91adb35c05

import Mathlib
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_TateLocalZeta

import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_forall_integral_mul_modulus_det_cpow_eq_finsum_of_eqOn_of_forall_integrable
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm MeasureTheory LanglandsTunnell.TateLocal

namespace K2PullDown

noncomputable section

open scoped Classical

theorem norm_natCast_cpow_real (n : ℕ) (hn : 0 < n) (ℓ : ℤ) (σ : ℝ) :
    ‖(n : ℂ) ^ (-(ℓ : ℂ) * (σ : ℂ))‖ = (n : ℝ) ^ (-(ℓ : ℝ) * σ) := by
  have h : ((n : ℝ) : ℂ) = (n : ℂ) := by push_cast; rfl
  rw [← h, Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hn)]
  congr 1
  simp [Complex.mul_re]

theorem eq_zero_of_forall_tsum_cpow_mul_eq_zero (n : ℕ) (hn : 1 < n) (d : ℤ → ℂ) (ℓ₀ : ℤ) (hd : ∀ ℓ : ℤ, ℓ < ℓ₀ → d ℓ = 0)
    (σ₀ : ℝ)
    (hs : ∀ σ : ℝ, σ₀ < σ → Summable fun ℓ : ℤ => ‖(n : ℂ) ^ (-(ℓ : ℂ) * (σ : ℂ)) * d ℓ‖)
    (h0 : ∀ σ : ℝ, σ₀ < σ → ∑' ℓ : ℤ, (n : ℂ) ^ (-(ℓ : ℂ) * (σ : ℂ)) * d ℓ = 0) :
    d = 0 := by
  by_contra hne
  have hex : ∃ ℓ : ℤ, d ℓ ≠ 0 := by
    by_contra hall; push_neg at hall; exact hne (funext hall)
  obtain ⟨m, hm, hmin⟩ := Int.exists_least_of_bdd (P := fun ℓ => d ℓ ≠ 0)
    ⟨ℓ₀, fun z hz => by by_contra hlt; push_neg at hlt; exact hz (hd z hlt)⟩ hex
  have hn0 : (0 : ℝ) < n := by exact_mod_cast lt_trans zero_lt_one hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  set σ₁ : ℝ := σ₀ + 1 with hσ₁
  have hσ₁gt : σ₀ < σ₁ := by rw [hσ₁]; linarith
  set C : ℝ := ∑' ℓ : ℤ, ‖(n : ℂ) ^ (-(ℓ : ℂ) * (σ₁ : ℂ)) * d ℓ‖ with hC
  have hC0 : 0 ≤ C := by rw [hC]; exact tsum_nonneg fun _ => norm_nonneg _

  have key : ∀ σ : ℝ, σ₁ ≤ σ → ‖d m‖ ≤ C * (n : ℝ) ^ (((m : ℝ) + 1) * σ₁) * (n : ℝ) ^ (-σ) := by
    intro σ hσ
    have hσ0 : σ₀ < σ := lt_of_lt_of_le hσ₁gt hσ
    have hsum := hs σ hσ0
    have hsum' : Summable fun ℓ : ℤ => (n : ℂ) ^ (-(ℓ : ℂ) * (σ : ℂ)) * d ℓ := Summable.of_norm hsum
    have hsplit := hsum'.tsum_eq_add_tsum_ite m
    rw [h0 σ hσ0] at hsplit
    set T : ℂ := ∑' ℓ : ℤ, (if ℓ = m then 0 else (n : ℂ) ^ (-(ℓ : ℂ) * (σ : ℂ)) * d ℓ) with hT
    have hmain : (n : ℂ) ^ (-(m : ℂ) * (σ : ℂ)) * d m = -T := by linear_combination (-1 : ℂ) * hsplit
    have hpt : ∀ ℓ : ℤ, ‖(if ℓ = m then 0 else (n : ℂ) ^ (-(ℓ : ℂ) * (σ : ℂ)) * d ℓ)‖ ≤
        (n : ℝ) ^ (-((m : ℝ) + 1) * (σ - σ₁)) * ‖(n : ℂ) ^ (-(ℓ : ℂ) * (σ₁ : ℂ)) * d ℓ‖ := by
      intro ℓ
      by_cases hℓ : ℓ = m
      · simp only [hℓ, if_true, norm_zero]; positivity
      · rw [if_neg hℓ]
        by_cases hdℓ : d ℓ = 0
        · simp [hdℓ]
        · have hge : m + 1 ≤ ℓ := by
            have := hmin ℓ hdℓ; omega
          rw [norm_mul, norm_mul, norm_natCast_cpow_real n (by omega) ℓ σ, norm_natCast_cpow_real n (by omega) ℓ σ₁,
            ← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [← Real.rpow_add hn0]
          apply Real.rpow_le_rpow_of_exponent_le hn1.le
          have hσ' : 0 ≤ σ - σ₁ := by linarith
          have hℓR : ((m : ℝ) + 1) ≤ (ℓ : ℝ) := by exact_mod_cast hge
          nlinarith
    have hTsum : Summable fun ℓ : ℤ => ‖(if ℓ = m then 0 else (n : ℂ) ^ (-(ℓ : ℂ) * (σ : ℂ)) * d ℓ)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt ((hs σ₁ hσ₁gt).mul_left _)
    have hTle : ‖T‖ ≤ (n : ℝ) ^ (-((m : ℝ) + 1) * (σ - σ₁)) * C := by
      rw [hT]
      refine le_trans (norm_tsum_le_tsum_norm hTsum) ?_
      rw [hC, ← tsum_mul_left]
      exact hTsum.tsum_le_tsum hpt ((hs σ₁ hσ₁gt).mul_left _)
    have hnorm : ‖d m‖ = (n : ℝ) ^ ((m : ℝ) * σ) * ‖T‖ := by
      have h1 := congrArg (fun z : ℂ => ‖z‖) hmain
      simp only [norm_neg, norm_mul, norm_natCast_cpow_real n (by omega) m σ] at h1
      have hpos : (0 : ℝ) < (n : ℝ) ^ (-(m : ℝ) * σ) := Real.rpow_pos_of_pos hn0 _
      have h2 : ‖d m‖ = ((n : ℝ) ^ (-(m : ℝ) * σ))⁻¹ * ‖T‖ := by
        rw [← h1, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
      rw [h2, ← Real.rpow_neg (le_of_lt hn0)]
      ring_nf
    rw [hnorm]
    calc (n : ℝ) ^ ((m : ℝ) * σ) * ‖T‖ ≤ (n : ℝ) ^ ((m : ℝ) * σ) * ((n : ℝ) ^ (-((m : ℝ) + 1) * (σ - σ₁)) * C) :=
          mul_le_mul_of_nonneg_left hTle (Real.rpow_nonneg hn0.le _)
      _ = C * (n : ℝ) ^ (((m : ℝ) + 1) * σ₁) * (n : ℝ) ^ (-σ) := by
          rw [← mul_assoc, ← Real.rpow_add hn0,
            show (m : ℝ) * σ + -((m : ℝ) + 1) * (σ - σ₁) = ((m : ℝ) + 1) * σ₁ + (-σ) by ring, Real.rpow_add hn0]
          ring

  apply hm
  by_contra hdm
  have hpos : 0 < ‖d m‖ := norm_pos_iff.2 hdm
  set K : ℝ := C * (n : ℝ) ^ (((m : ℝ) + 1) * σ₁) with hK
  have hK0 : 0 ≤ K := by rw [hK]; exact mul_nonneg hC0 (Real.rpow_nonneg hn0.le _)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hpos (lt_of_le_of_lt hK0 (lt_add_one K)))
    (show (1 : ℝ) / n < 1 from (div_lt_one hn0).2 hn1)
  have hσ : σ₁ ≤ max σ₁ (k : ℝ) := le_max_left _ _
  have hle := key (max σ₁ (k : ℝ)) hσ
  have hdec : (n : ℝ) ^ (-(max σ₁ (k : ℝ))) ≤ ((1 : ℝ) / n) ^ k := by
    rw [one_div, ← Real.rpow_natCast, Real.inv_rpow hn0.le, ← Real.rpow_neg hn0.le]
    apply Real.rpow_le_rpow_of_exponent_le hn1.le
    simp only [neg_le_neg_iff]; exact le_max_right _ _
  have h3 : ‖d m‖ ≤ K * ((1 : ℝ) / n) ^ k := le_trans hle (by rw [hK]; exact mul_le_mul_of_nonneg_left hdec hK0)
  have h4 : ‖d m‖ < ‖d m‖ := by
    calc ‖d m‖ ≤ K * ((1 : ℝ) / n) ^ k := h3
      _ ≤ (K + 1) * ((1 : ℝ) / n) ^ k := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ < (K + 1) * (‖d m‖ / (K + 1)) := mul_lt_mul_of_pos_left hk (by linarith)
      _ = ‖d m‖ := by field_simp
  exact lt_irrefl _ h4

end

end K2PullDown

namespace K2PullDown

noncomputable section

open scoped Classical

attribute [local instance] AutomorphicForm.localGLBorel
attribute [local instance] AutomorphicForm.borelSpace_localGLBorel

variable (p : HeightOneSpectrum (𝓞 ℚ))

local notation "F" => (HeightOneSpectrum.adicCompletion ℚ p)
local notation "G" => (GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ p))

def detShell (ℓ : ℤ) : Set G :=
  {g : G | Valued.v ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = WithZero.exp (-ℓ)}

theorem isClosed_vball (γ : WithZero (Multiplicative ℤ)) : IsClosed {x : F | Valued.v x ≤ γ} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
  have hx0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' hx)
  filter_upwards [Valued.locally_const hx0] with y hy
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, hy]; exact hx

theorem setOf_v_eq_exp (m : ℤ) :
    {x : F | Valued.v x = WithZero.exp m} = {x : F | Valued.v x ≤ WithZero.exp m} ∩ {x : F | Valued.v x ≤ WithZero.exp (m - 1)}ᶜ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_le]
  constructor
  · intro h; rw [h]; exact ⟨le_rfl, by rw [WithZero.exp_lt_exp]; omega⟩
  · rintro ⟨h1, h2⟩
    have hx0 : (Valued.v x : WithZero (Multiplicative ℤ)) ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' h2)
    rw [← WithZero.exp_log hx0] at h1 h2 ⊢
    rw [WithZero.exp_le_exp] at h1; rw [WithZero.exp_lt_exp] at h2
    congr 1; omega

theorem measurableSet_detShell (ℓ : ℤ) : MeasurableSet (detShell p ℓ) := by
  have hc : Continuous fun g : G => ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) :=
    Units.continuous_val.comp Matrix.GeneralLinearGroup.continuous_det
  have hS : IsClosed {x : F | Valued.v x ≤ WithZero.exp (-ℓ)} ∧ IsClosed {x : F | Valued.v x ≤ WithZero.exp (-ℓ - 1)} :=
    ⟨isClosed_vball p _, isClosed_vball p _⟩
  have : detShell p ℓ = (fun g : G => ((Matrix.GeneralLinearGroup.det g : Fˣ) : F)) ⁻¹' {x : F | Valued.v x = WithZero.exp (-ℓ)} := rfl
  rw [this, setOf_v_eq_exp]
  exact ((hS.1.preimage hc).measurableSet).inter (hS.2.preimage hc).measurableSet.compl

theorem pairwise_disjoint_detShell : Pairwise (Function.onFun Disjoint (detShell p)) := by
  intro i j hij
  simp only [Function.onFun]
  rw [Set.disjoint_iff]
  rintro g ⟨hi, hj⟩
  apply hij
  have h : WithZero.exp (-i) = WithZero.exp (-j) := by
    rw [← show Valued.v ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = WithZero.exp (-i) from hi]; exact hj
  have := WithZero.exp_injective h
  omega

theorem iUnion_detShell : (⋃ ℓ : ℤ, detShell p ℓ) = Set.univ := by
  ext g
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true, detShell, Set.mem_setOf_eq]
  have h0 : (Valued.v ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (Matrix.GeneralLinearGroup.det g).ne_zero
  refine ⟨-Multiplicative.toAdd (WithZero.unzero h0), ?_⟩
  rw [neg_neg]
  conv_lhs => rw [← WithZero.coe_unzero h0]
  rfl

theorem hasSum_integral_detShell (ν : Measure G) (f : G → ℂ) (hf : Integrable f ν) :
    HasSum (fun ℓ : ℤ => ∫ g, (if Valued.v ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = WithZero.exp (-ℓ) then (1 : ℂ) else 0) * f g ∂ν)
      (∫ g, f g ∂ν) := by
  have h := hasSum_integral_iUnion (μ := ν) (f := f) (measurableSet_detShell p) (pairwise_disjoint_detShell p)
    (by rw [iUnion_detShell]; exact hf.integrableOn)
  rw [iUnion_detShell, setIntegral_univ] at h
  refine h.congr_fun fun ℓ => ?_
  rw [← integral_indicator (measurableSet_detShell p ℓ)]
  congr 1
  funext g
  simp only [Set.indicator_apply, detShell, Set.mem_setOf_eq]
  split_ifs <;> simp

theorem one_lt_absNorm : 1 < Ideal.absNorm p.asIdeal := by
  have h0 : Ideal.absNorm p.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot
  have h1 : Ideal.absNorm p.asIdeal ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact p.isPrime.ne_top
  omega

theorem norm_eq_zpow_of_valued {x : F} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    ‖x‖ = (Ideal.absNorm p.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx,
    show (WithZero.exp m) = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd,
    NNReal.coe_zpow, NNReal.coe_natCast]

theorem coe_modulus_of_valued {x : F} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    (modulus x : ℝ) = (Ideal.absNorm p.asIdeal : ℝ) ^ m := by
  rw [modulus_adicCompletion_eq_nnnorm ℚ p x, coe_nnnorm, norm_eq_zpow_of_valued p hx]

theorem cpow_natCast_zpow (n : ℕ) (hn : 0 < n) (m : ℤ) (z : ℂ) :
    (((n : ℝ) ^ m : ℝ) : ℂ) ^ z = (n : ℂ) ^ ((m : ℂ) * z) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (0 : ℝ) < (n : ℝ) ^ m := zpow_pos hnR m
  have hC1 : (((n : ℝ) ^ m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpow.ne'
  have hC2 : ((n : ℂ)) ≠ 0 := by exact_mod_cast hnR.ne'
  rw [Complex.cpow_def_of_ne_zero hC1, Complex.cpow_def_of_ne_zero hC2]
  congr 1
  rw [← Complex.ofReal_log hpow.le, Real.log_zpow, show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_log hnR.le]
  push_cast
  ring

theorem pullDown (μ₂ : Measure G) (f : G → ℂ) (τ : ℂ) (B : ℤ)
    (hB : ∀ g : G, f g ≠ 0 → Valued.v ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) ≤ WithZero.exp B)
    (σu σ₂ : ℝ) (a : ℤ → ℂ) (ha : (Function.support a).Finite)
    (hint : ∀ s : ℂ, σu < s.re →
      Integrable (fun g : G => f g * ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ (s + τ)) μ₂)
    (h : ∀ s : ℂ, σ₂ < s.re →
      ∫ g, f g * ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ (s + τ) ∂μ₂ =
        ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * s) * a i)
    (s : ℂ) (hs : σu < s.re) :
    ∫ g, f g * ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ (s + τ) ∂μ₂ =
      ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * s) * a i := by
  set N : ℕ := Ideal.absNorm p.asIdeal with hNdef
  have hN1 : 1 < N := one_lt_absNorm p
  have hN0 : 0 < N := lt_trans zero_lt_one hN1
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'

  set c : ℤ → ℂ := fun ℓ => (N : ℂ) ^ (-(ℓ : ℂ) * τ) *
      ∫ g, (if Valued.v ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = WithZero.exp (-ℓ) then (1 : ℂ) else 0) * f g ∂μ₂ with hc

  have hpt : ∀ (z : ℂ) (ℓ : ℤ) (g : G),
      (if Valued.v ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = WithZero.exp (-ℓ) then (1 : ℂ) else 0) *
          (f g * ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ (z + τ)) =
        ((N : ℂ) ^ (-(ℓ : ℂ) * z) * (N : ℂ) ^ (-(ℓ : ℂ) * τ)) *
          ((if Valued.v ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = WithZero.exp (-ℓ) then (1 : ℂ) else 0) * f g) := by
    intro z ℓ g
    by_cases hg : Valued.v ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = WithZero.exp (-ℓ)
    · simp only [if_pos hg]
      rw [coe_modulus_of_valued p hg, hNdef, cpow_natCast_zpow _ hN0,
        show (((-ℓ : ℤ)) : ℂ) * (z + τ) = -(ℓ : ℂ) * z + -(ℓ : ℂ) * τ by push_cast; ring, Complex.cpow_add _ _ hNC]
      ring
    · simp only [if_neg hg]; ring
  have hshell : ∀ (z : ℂ) (ℓ : ℤ),
      ∫ g, (if Valued.v ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = WithZero.exp (-ℓ) then (1 : ℂ) else 0) *
          (f g * ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ (z + τ)) ∂μ₂ =
        (N : ℂ) ^ (-(ℓ : ℂ) * z) * c ℓ := by
    intro z ℓ
    simp_rw [hpt z ℓ]
    rw [integral_const_mul, hc]
    ring

  have hsum : ∀ z : ℂ, σu < z.re →
      HasSum (fun ℓ : ℤ => (N : ℂ) ^ (-(ℓ : ℂ) * z) * c ℓ)
        (∫ g, f g * ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ (z + τ) ∂μ₂) := by
    intro z hz
    have h1 := hasSum_integral_detShell p μ₂ _ (hint z hz)
    simp_rw [hshell z] at h1
    exact h1

  have habs : ∀ σ : ℝ, σu < σ → Summable (fun ℓ : ℤ => ‖(N : ℂ) ^ (-(ℓ : ℂ) * (σ : ℂ)) * c ℓ‖) := by
    intro σ hσ
    have hI := hint (σ : ℂ) (by simpa using hσ)
    have hIn := hI.norm
    have hparts := hasSum_integral_iUnion (μ := μ₂) (f := fun g : G =>
        ‖f g * ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ ((σ : ℂ) + τ)‖)
      (measurableSet_detShell p) (pairwise_disjoint_detShell p) (by rw [iUnion_detShell]; exact hIn.integrableOn)
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ℓ => ?_) hparts.summable
    rw [← hshell (σ : ℂ) ℓ]
    have : (fun g : G => (if Valued.v ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = WithZero.exp (-ℓ) then (1 : ℂ) else 0) *
        (f g * ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ ((σ : ℂ) + τ))) =
        (detShell p ℓ).indicator (fun g : G => f g * ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ ((σ : ℂ) + τ)) := by
      funext g
      simp only [Set.indicator_apply, detShell, Set.mem_setOf_eq]
      split_ifs <;> simp
    rw [this, integral_indicator (measurableSet_detShell p ℓ)]
    exact norm_integral_le_integral_norm _

  have hc0 : ∀ ℓ : ℤ, ℓ < -B → c ℓ = 0 := by
    intro ℓ hℓ
    have hz : (fun g : G => (if Valued.v ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = WithZero.exp (-ℓ) then (1 : ℂ) else 0) * f g) =
        fun _ => 0 := by
      funext g
      by_cases hg : Valued.v ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = WithZero.exp (-ℓ)
      · have hf : f g = 0 := by
          by_contra hfg
          have := hB g hfg
          rw [hg, WithZero.exp_le_exp] at this
          omega
        rw [hf, mul_zero]
      · rw [if_neg hg, zero_mul]
    rw [hc]
    show (N : ℂ) ^ (-(ℓ : ℂ) * τ) * ∫ g, (if Valued.v ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) = WithZero.exp (-ℓ) then (1 : ℂ) else 0) * f g ∂μ₂ = 0
    rw [hz, integral_zero, mul_zero]

  obtain ⟨bA, hbA⟩ : ∃ b : ℤ, ∀ ℓ : ℤ, ℓ < b → a ℓ = 0 := by
    obtain ⟨b, hb⟩ := ha.bddBelow
    exact ⟨b, fun ℓ hℓ => by by_contra hne; exact absurd (hb hne) (not_le.2 hℓ)⟩

  set σ₀ : ℝ := max σu σ₂ with hσ₀
  have hfinN : ∀ z : ℂ, (Function.support fun i : ℤ => (N : ℂ) ^ (-(i : ℂ) * z) * a i).Finite :=
    fun z => ha.subset (Function.support_mul_subset_right _ _)
  have hsumA : ∀ z : ℂ, Summable fun i : ℤ => (N : ℂ) ^ (-(i : ℂ) * z) * a i :=
    fun z => summable_of_finite_support (hfinN z)
  have hd : (fun ℓ : ℤ => c ℓ - a ℓ) = 0 := by
    refine eq_zero_of_forall_tsum_cpow_mul_eq_zero N hN1 (fun ℓ => c ℓ - a ℓ) (min (-B) bA)
      (fun ℓ hℓ => by
        show c ℓ - a ℓ = 0
        rw [hc0 ℓ (lt_of_lt_of_le hℓ (min_le_left _ _)), hbA ℓ (lt_of_lt_of_le hℓ (min_le_right _ _)), sub_zero])
      σ₀ (fun σ hσ => ?_) (fun σ hσ => ?_)
    ·
      have h1 := habs σ (lt_of_le_of_lt (le_max_left _ _) hσ)
      have h2 : Summable fun ℓ : ℤ => ‖(N : ℂ) ^ (-(ℓ : ℂ) * (σ : ℂ)) * a ℓ‖ := (hsumA (σ : ℂ)).norm
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ℓ => ?_) (h1.add h2)
      rw [mul_sub]
      exact norm_sub_le _ _
    · have hσu : σu < σ := lt_of_le_of_lt (le_max_left _ _) hσ
      have hσ2 : σ₂ < σ := lt_of_le_of_lt (le_max_right _ _) hσ
      have h1 : ∑' ℓ : ℤ, (N : ℂ) ^ (-(ℓ : ℂ) * (σ : ℂ)) * c ℓ = ∑ᶠ i : ℤ, (N : ℂ) ^ (-(i : ℂ) * (σ : ℂ)) * a i := by
        rw [(hsum (σ : ℂ) (by simpa using hσu)).tsum_eq]
        exact h (σ : ℂ) (by simpa using hσ2)
      have h2 : ∑ᶠ i : ℤ, (N : ℂ) ^ (-(i : ℂ) * (σ : ℂ)) * a i = ∑' i : ℤ, (N : ℂ) ^ (-(i : ℂ) * (σ : ℂ)) * a i :=
        (tsum_eq_finsum (hfinN (σ : ℂ))).symm
      have hcS : Summable fun ℓ : ℤ => (N : ℂ) ^ (-(ℓ : ℂ) * (σ : ℂ)) * c ℓ := (hsum (σ : ℂ) (by simpa using hσu)).summable
      calc ∑' ℓ : ℤ, (N : ℂ) ^ (-(ℓ : ℂ) * (σ : ℂ)) * (c ℓ - a ℓ)
          = ∑' ℓ : ℤ, ((N : ℂ) ^ (-(ℓ : ℂ) * (σ : ℂ)) * c ℓ - (N : ℂ) ^ (-(ℓ : ℂ) * (σ : ℂ)) * a ℓ) := by
            congr 1; funext ℓ; ring
        _ = ∑' ℓ : ℤ, (N : ℂ) ^ (-(ℓ : ℂ) * (σ : ℂ)) * c ℓ - ∑' ℓ : ℤ, (N : ℂ) ^ (-(ℓ : ℂ) * (σ : ℂ)) * a ℓ :=
            hcS.tsum_sub (hsumA (σ : ℂ))
        _ = 0 := by rw [h1, h2, sub_self]
  have hca : c = a := by
    funext ℓ
    have := congrFun hd ℓ
    simpa [sub_eq_zero] using this

  calc ∫ g, f g * ((modulus ((Matrix.GeneralLinearGroup.det g : Fˣ) : F) : ℝ) : ℂ) ^ (s + τ) ∂μ₂
      = ∑' ℓ : ℤ, (N : ℂ) ^ (-(ℓ : ℂ) * s) * c ℓ := ((hsum s hs).tsum_eq).symm
    _ = ∑' ℓ : ℤ, (N : ℂ) ^ (-(ℓ : ℂ) * s) * a ℓ := by rw [hca]
    _ = ∑ᶠ i : ℤ, (N : ℂ) ^ (-(i : ℂ) * s) * a i := tsum_eq_finsum (hfinN s)

end

end K2PullDown

theorem solution
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (μ₂ : Measure (GL (Fin 2) (p.adicCompletion ℚ))) (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (τ : ℂ) (B : ℤ),
      (∀ g : GL (Fin 2) (p.adicCompletion ℚ), f g ≠ 0 →
        Valued.v ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) ≤ WithZero.exp B) →
      ∀ (σu σ₂ : ℝ) (a : ℤ → ℂ), (Function.support a).Finite →
        (∀ s : ℂ, σu < s.re →
          Integrable (fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
            f g * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + τ)) μ₂) →
        (∀ s : ℂ, σ₂ < s.re →
          ∫ g, f g * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + τ) ∂μ₂ =
            ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * s) * a i) →
        ∀ s : ℂ, σu < s.re →
          ∫ g, f g * ((modulus ((Matrix.GeneralLinearGroup.det g : (p.adicCompletion ℚ)ˣ) : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s + τ) ∂μ₂ =
            ∑ᶠ i : ℤ, (Ideal.absNorm p.asIdeal : ℂ) ^ (-(i : ℂ) * s) * a i := by
  intro μ₂ f τ B hB σu σ₂ a ha hint h s hs
  exact K2PullDown.pullDown p μ₂ f τ B hB σu σ₂ a ha hint h s hs

end S_LanglandsTunnell_RankinSelberg_forall_integral_mul_modulus_det_cpow_eq_finsum_of_eqOn_of_forall_integrable
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_forall_integral_mul_modulus_det_cpow_eq_finsum_of_eqOn_of_forall_integrable (solution)
