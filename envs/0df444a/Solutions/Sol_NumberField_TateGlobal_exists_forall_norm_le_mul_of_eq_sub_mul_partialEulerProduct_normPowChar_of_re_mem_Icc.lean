-- Prove2me | solution 1 for NumberField.TateGlobal.exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c6f33915-93e0-59e0-8240-2adac6be67b3

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_NormPowChar
import Theorems.Thm_NumberField_exists_completedDedekindZeta_package
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Theorems.Thm_NumberField_TateGlobal_ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg
import Theorems.Thm_Complex_exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open NumberField.TateGlobal

noncomputable section

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

private theorem one_lt_absNorm (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    1 < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have h2 : 2 ≤ Ideal.absNorm v.asIdeal := by omega
  exact_mod_cast lt_of_lt_of_le one_lt_two h2

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

namespace ShiftedDedekindGrowth

open Complex
open EulerBound StripInterpolation

private theorem exists_gammaR_bounds (σ₁ σ₂ : ℝ) :
    ∃ (A : ℝ) (N : ℕ), 0 ≤ A ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 2 ≤ |s.im| →
      ‖Gammaℝ s‖ ≤ A * (1 + |s.im|) ^ N * Real.exp (-(Real.pi / 4) * |s.im|) ∧
        Real.exp (-(Real.pi / 4) * |s.im|) ≤ A * (1 + |s.im|) ^ N * ‖Gammaℝ s‖ := by
  obtain ⟨A, N, hAN⟩ :=
    Complex.exists_forall_norm_Gamma_le_mul_exp_and_exp_le_mul_norm_Gamma_of_re_mem_Icc_of_one_le_abs_im
      (σ₁ / 2) (σ₂ / 2)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos

  set c₁ : ℝ := min (Real.pi ^ (-σ₂ / 2)) (Real.pi ^ (-σ₁ / 2)) with hc₁
  set c₂ : ℝ := max (Real.pi ^ (-σ₂ / 2)) (Real.pi ^ (-σ₁ / 2)) with hc₂
  have hc₁pos : 0 < c₁ := lt_min (Real.rpow_pos_of_pos hπ _) (Real.rpow_pos_of_pos hπ _)
  have hc₂pos : 0 < c₂ := lt_of_lt_of_le (Real.rpow_pos_of_pos hπ _) (le_max_left _ _)
  set A₀ : ℝ := max A 0 with hA₀
  have hA₀0 : 0 ≤ A₀ := le_max_right _ _
  have hAA₀ : A ≤ A₀ := le_max_left _ _
  refine ⟨max (A₀ * c₂) (A₀ / c₁), N, le_max_of_le_left (by positivity), fun s h₁ h₂ hs => ?_⟩
  have hs2 : (1 : ℝ) ≤ |(s / 2).im| := by
    rw [Complex.div_ofNat_im]; rw [abs_div, abs_two]; linarith
  have hre₁ : σ₁ / 2 ≤ (s / 2).re := by rw [Complex.div_ofNat_re]; linarith
  have hre₂ : (s / 2).re ≤ σ₂ / 2 := by rw [Complex.div_ofNat_re]; linarith
  obtain ⟨hup, hlow⟩ := hAN (s / 2) hre₁ hre₂ hs2
  have him : |(s / 2).im| = |s.im| / 2 := by rw [Complex.div_ofNat_im, abs_div, abs_two]
  rw [him] at hup hlow

  have hπnorm : ‖((Real.pi : ℂ)) ^ (-s / 2)‖ = Real.pi ^ (-s.re / 2) := by
    rw [norm_cpow_eq_rpow_re_of_pos hπ]; congr 1; simp [Complex.div_ofNat_re]
  have hπlo : c₁ ≤ Real.pi ^ (-s.re / 2) := by
    rcases le_total 1 Real.pi with hp | hp
    · refine le_trans (min_le_left _ _) (Real.rpow_le_rpow_of_exponent_le hp (by linarith))
    · refine le_trans (min_le_right _ _) (Real.rpow_le_rpow_of_exponent_ge hπ hp (by linarith))
  have hπhi : Real.pi ^ (-s.re / 2) ≤ c₂ := by
    rcases le_total 1 Real.pi with hp | hp
    · exact le_trans (Real.rpow_le_rpow_of_exponent_le hp (by linarith)) (le_max_right _ _)
    · exact le_trans (Real.rpow_le_rpow_of_exponent_ge hπ hp (by linarith)) (le_max_left _ _)
  have hG : ‖Gammaℝ s‖ = Real.pi ^ (-s.re / 2) * ‖Gamma (s / 2)‖ := by
    rw [Gammaℝ_def, norm_mul, hπnorm]

  have hexp : Real.exp (-(Real.pi / 2) * (|s.im| / 2)) = Real.exp (-(Real.pi / 4) * |s.im|) := by
    congr 1; ring
  have hpow : (1 + |s.im| / 2) ^ N ≤ (1 + |s.im|) ^ N := by
    gcongr; linarith [abs_nonneg s.im]
  have hpos : (0 : ℝ) ≤ (1 + |s.im|) ^ N := by positivity
  have hexppos : (0 : ℝ) < Real.exp (-(Real.pi / 4) * |s.im|) := Real.exp_pos _
  constructor
  · rw [hG]
    calc Real.pi ^ (-s.re / 2) * ‖Gamma (s / 2)‖
        ≤ c₂ * (A * (1 + |s.im| / 2) ^ N * Real.exp (-(Real.pi / 2) * (|s.im| / 2))) :=
          mul_le_mul hπhi hup (norm_nonneg _) hc₂pos.le
      _ ≤ c₂ * (A₀ * (1 + |s.im|) ^ N * Real.exp (-(Real.pi / 4) * |s.im|)) := by
          rw [hexp]
          have h0 : 0 ≤ (1 + |s.im| / 2) ^ N := by positivity
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (le_trans (mul_le_mul_of_nonneg_right hAA₀ h0) (mul_le_mul_of_nonneg_left hpow hA₀0))
            hexppos.le) hc₂pos.le
      _ = (A₀ * c₂) * (1 + |s.im|) ^ N * Real.exp (-(Real.pi / 4) * |s.im|) := by ring
      _ ≤ max (A₀ * c₂) (A₀ / c₁) * (1 + |s.im|) ^ N * Real.exp (-(Real.pi / 4) * |s.im|) := by
          gcongr
          exact le_max_left _ _
  · rw [hG]
    have hΓ0 : 0 ≤ ‖Gamma (s / 2)‖ := norm_nonneg _
    have h1 : Real.exp (-(Real.pi / 4) * |s.im|) ≤ A₀ * (1 + |s.im|) ^ N * ‖Gamma (s / 2)‖ := by
      rw [← hexp]
      refine le_trans hlow ?_
      have h0 : 0 ≤ (1 + |s.im| / 2) ^ N := by positivity
      exact mul_le_mul_of_nonneg_right
        (le_trans (mul_le_mul_of_nonneg_right hAA₀ h0) (mul_le_mul_of_nonneg_left hpow hA₀0)) hΓ0
    have h2 : ‖Gamma (s / 2)‖ ≤ (Real.pi ^ (-s.re / 2) * ‖Gamma (s / 2)‖) / c₁ := by
      rw [le_div_iff₀ hc₁pos]
      calc ‖Gamma (s / 2)‖ * c₁ = c₁ * ‖Gamma (s / 2)‖ := by ring
        _ ≤ Real.pi ^ (-s.re / 2) * ‖Gamma (s / 2)‖ := by gcongr
    calc Real.exp (-(Real.pi / 4) * |s.im|)
        ≤ A₀ * (1 + |s.im|) ^ N * ‖Gamma (s / 2)‖ := h1
      _ ≤ A₀ * (1 + |s.im|) ^ N * ((Real.pi ^ (-s.re / 2) * ‖Gamma (s / 2)‖) / c₁) := by gcongr
      _ = (A₀ / c₁) * (1 + |s.im|) ^ N * (Real.pi ^ (-s.re / 2) * ‖Gamma (s / 2)‖) := by ring
      _ ≤ max (A₀ * c₂) (A₀ / c₁) * (1 + |s.im|) ^ N * (Real.pi ^ (-s.re / 2) * ‖Gamma (s / 2)‖) := by
          gcongr
          exact le_max_right _ _

private def IsPolyBdd (f : ℂ → ℝ) (S : Set ℂ) : Prop :=
  ∃ (c : ℝ) (n : ℕ), 0 ≤ c ∧ ∀ s ∈ S, 0 ≤ f s ∧ f s ≤ c * (1 + |s.im|) ^ n

private theorem isPolyBdd_of_bdd {f : ℂ → ℝ} {S : Set ℂ} {c : ℝ}
    (h : ∀ s ∈ S, 0 ≤ f s ∧ f s ≤ c) : IsPolyBdd f S := by
  refine ⟨max c 0, 0, le_max_right _ _, fun s hs => ⟨(h s hs).1, ?_⟩⟩
  simpa using le_trans (h s hs).2 (le_max_left _ _)

private theorem IsPolyBdd.mul {f g : ℂ → ℝ} {S : Set ℂ} (hf : IsPolyBdd f S) (hg : IsPolyBdd g S) :
    IsPolyBdd (fun s => f s * g s) S := by
  obtain ⟨c, n, hc, hfS⟩ := hf
  obtain ⟨d, m, hd, hgS⟩ := hg
  refine ⟨c * d, n + m, by positivity, fun s hs => ⟨mul_nonneg (hfS s hs).1 (hgS s hs).1, ?_⟩⟩
  calc f s * g s ≤ (c * (1 + |s.im|) ^ n) * (d * (1 + |s.im|) ^ m) :=
        mul_le_mul (hfS s hs).2 (hgS s hs).2 (hgS s hs).1 (by positivity)
    _ = c * d * (1 + |s.im|) ^ (n + m) := by rw [pow_add]; ring

private theorem IsPolyBdd.of_le {f g : ℂ → ℝ} {S : Set ℂ} (hf : IsPolyBdd f S)
    (hg : ∀ s ∈ S, 0 ≤ g s ∧ g s ≤ f s) : IsPolyBdd g S := by
  obtain ⟨c, n, hc, hfS⟩ := hf
  exact ⟨c, n, hc, fun s hs => ⟨(hg s hs).1, le_trans (hg s hs).2 (hfS s hs).2⟩⟩

private theorem IsPolyBdd.mono {f : ℂ → ℝ} {S S' : Set ℂ} (hf : IsPolyBdd f S) (h : S' ⊆ S) :
    IsPolyBdd f S' := by
  obtain ⟨c, n, hc, hfS⟩ := hf
  exact ⟨c, n, hc, fun s hs => hfS s (h hs)⟩

private theorem IsPolyBdd.pow {f : ℂ → ℝ} {S : Set ℂ} (hf : IsPolyBdd f S) (k : ℕ) :
    IsPolyBdd (fun s => f s ^ k) S := by
  induction k with
  | zero => exact isPolyBdd_of_bdd (c := 1) fun s _ => by simp
  | succ k ih =>
    refine (ih.mul hf).of_le fun s hs => ?_
    obtain ⟨c, n, -, hfS⟩ := hf
    exact ⟨pow_nonneg (hfS s hs).1 _, le_of_eq (pow_succ _ _)⟩

private theorem isPolyBdd_norm_add (σ₁ σ₂ : ℝ) (a : ℂ) :
    IsPolyBdd (fun s => ‖s + a‖) {s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ σ₂} := by
  refine ⟨|σ₁| + |σ₂| + ‖a‖ + 1, 1, by positivity, fun s hs => ⟨norm_nonneg _, ?_⟩⟩
  obtain ⟨h₁, h₂⟩ := hs
  have hre : |s.re| ≤ |σ₁| + |σ₂| := by
    rcases le_total 0 s.re with h | h
    · rw [abs_of_nonneg h]; linarith [le_abs_self σ₂, abs_nonneg σ₁]
    · rw [abs_of_nonpos h]; linarith [neg_le_abs σ₁, abs_nonneg σ₂]
  calc ‖s + a‖ ≤ ‖s‖ + ‖a‖ := norm_add_le _ _
    _ ≤ (|s.re| + |s.im|) + ‖a‖ := by gcongr; exact Complex.norm_le_abs_re_add_abs_im s
    _ ≤ (|σ₁| + |σ₂| + ‖a‖ + 1) * (1 + |s.im|) ^ 1 := by
        rw [pow_one]; nlinarith [abs_nonneg s.im, norm_nonneg a, abs_nonneg σ₁, abs_nonneg σ₂]

private theorem IsPolyBdd.union {f : ℂ → ℝ} {S S' : Set ℂ} (h : IsPolyBdd f S) (h' : IsPolyBdd f S') :
    IsPolyBdd f (S ∪ S') := by
  obtain ⟨c, n, hc, hS⟩ := h
  obtain ⟨d, m, hd, hS'⟩ := h'
  refine ⟨max c d, max n m, le_max_of_le_left hc, fun s hs => ?_⟩
  have h1 : (1 : ℝ) ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
  rcases hs with hs | hs
  · refine ⟨(hS s hs).1, le_trans (hS s hs).2 ?_⟩
    exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ h1 (le_max_left _ _)) (by positivity)
      (le_max_of_le_left hc)
  · refine ⟨(hS' s hs).1, le_trans (hS' s hs).2 ?_⟩
    exact mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ h1 (le_max_right _ _)) (by positivity)
      (le_max_of_le_left hc)

private theorem isPolyBdd_norm_sub (σ₁ σ₂ : ℝ) (a : ℂ) :
    IsPolyBdd (fun s => ‖s - a‖) {s : ℂ | σ₁ ≤ s.re ∧ s.re ≤ σ₂} := by
  refine ⟨|σ₁| + |σ₂| + ‖a‖ + 1, 1, by positivity, fun s hs => ⟨norm_nonneg _, ?_⟩⟩
  obtain ⟨h₁, h₂⟩ := hs
  have hre : |s.re| ≤ |σ₁| + |σ₂| := by
    rcases le_total 0 s.re with h | h
    · rw [abs_of_nonneg h]; linarith [le_abs_self σ₂, abs_nonneg σ₁]
    · rw [abs_of_nonpos h]; linarith [neg_le_abs σ₁, abs_nonneg σ₂]
  calc ‖s - a‖ ≤ ‖s‖ + ‖a‖ := norm_sub_le _ _
    _ ≤ (|s.re| + |s.im|) + ‖a‖ := by gcongr; exact Complex.norm_le_abs_re_add_abs_im s
    _ ≤ (|σ₁| + |σ₂| + ‖a‖ + 1) * (1 + |s.im|) ^ 1 := by
        rw [pow_one]; nlinarith [abs_nonneg s.im, norm_nonneg a, abs_nonneg σ₁, abs_nonneg σ₂]

private theorem exists_gammaR_inv_le (σ₁ σ₂ : ℝ) :
    ∃ (A : ℝ) (N : ℕ), 0 ≤ A ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → 2 ≤ |s.im| →
      ‖Gammaℝ s‖⁻¹ ≤ A * (1 + |s.im|) ^ N * Real.exp ((Real.pi / 4) * |s.im|) := by
  obtain ⟨A, N, hA, hAN⟩ := exists_gammaR_bounds σ₁ σ₂
  refine ⟨A, N, hA, fun s h₁ h₂ hs => ?_⟩
  have hlow := (hAN s h₁ h₂ hs).2
  have he : 0 < Real.exp (-(Real.pi / 4) * |s.im|) := Real.exp_pos _
  have hΓ : 0 < ‖Gammaℝ s‖ := by
    by_contra hcon
    have h0 : ‖Gammaℝ s‖ = 0 := le_antisymm (not_lt.mp hcon) (norm_nonneg _)
    rw [h0, mul_zero] at hlow
    exact absurd hlow (not_le.mpr he)
  have hexp : Real.exp ((Real.pi / 4) * |s.im|) = (Real.exp (-(Real.pi / 4) * |s.im|))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [hexp]
  calc ‖Gammaℝ s‖⁻¹
      = (‖Gammaℝ s‖⁻¹ * Real.exp (-(Real.pi / 4) * |s.im|)) * (Real.exp (-(Real.pi / 4) * |s.im|))⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ he.ne', mul_one]
    _ ≤ (‖Gammaℝ s‖⁻¹ * (A * (1 + |s.im|) ^ N * ‖Gammaℝ s‖)) * (Real.exp (-(Real.pi / 4) * |s.im|))⁻¹ := by
        gcongr
    _ = A * (1 + |s.im|) ^ N * (Real.exp (-(Real.pi / 4) * |s.im|))⁻¹ * (‖Gammaℝ s‖⁻¹ * ‖Gammaℝ s‖) := by ring
    _ = A * (1 + |s.im|) ^ N * (Real.exp (-(Real.pi / 4) * |s.im|))⁻¹ := by
        rw [inv_mul_cancel₀ hΓ.ne', mul_one]

private theorem exists_gammaR_quot_le (σ₁ σ₂ : ℝ) :
    ∃ (c : ℝ) (n : ℕ), 0 ≤ c ∧ ∀ s s' : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ → σ₁ ≤ s'.re → s'.re ≤ σ₂ →
      2 ≤ |s.im| → |s'.im| = |s.im| → ‖Gammaℝ s‖ * ‖Gammaℝ s'‖⁻¹ ≤ c * (1 + |s.im|) ^ n := by
  obtain ⟨A, N, hA, hAN⟩ := exists_gammaR_bounds σ₁ σ₂
  obtain ⟨A', N', hA', hinv⟩ := exists_gammaR_inv_le σ₁ σ₂
  refine ⟨A * A', N + N', by positivity, fun s s' h₁ h₂ h₁' h₂' hs him => ?_⟩
  have hup := (hAN s h₁ h₂ hs).1
  have hs' : 2 ≤ |s'.im| := by rw [him]; exact hs
  have hi := hinv s' h₁' h₂' hs'
  rw [him] at hi
  have hepos : 0 < Real.exp ((Real.pi / 4) * |s.im|) := Real.exp_pos _
  calc ‖Gammaℝ s‖ * ‖Gammaℝ s'‖⁻¹
      ≤ (A * (1 + |s.im|) ^ N * Real.exp (-(Real.pi / 4) * |s.im|))
          * (A' * (1 + |s.im|) ^ N' * Real.exp ((Real.pi / 4) * |s.im|)) :=
        mul_le_mul hup hi (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
    _ = A * A' * (1 + |s.im|) ^ (N + N')
          * (Real.exp (-(Real.pi / 4) * |s.im|) * Real.exp ((Real.pi / 4) * |s.im|)) := by
        rw [pow_add]; ring
    _ = A * A' * (1 + |s.im|) ^ (N + N') := by
        rw [← Real.exp_add, show -(Real.pi / 4) * |s.im| + (Real.pi / 4) * |s.im| = 0 by ring, Real.exp_zero,
          mul_one]

private theorem two_le_absNorm {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

private theorem absNormC_ne_zero {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
  have := two_le_absNorm v
  exact_mod_cast (show Ideal.absNorm v.asIdeal ≠ 0 by omega)

private theorem differentiable_prod_eulerFactor {K : Type} [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Differentiable ℂ fun z : ℂ => ∏ v ∈ S, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert v S hv ih =>
    simp only [Finset.prod_insert hv]
    exact ((differentiable_const _).sub (differentiable_neg.const_cpow (Or.inl (absNormC_ne_zero v)))).mul ih

private theorem norm_absNorm_cpow {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
  have hpos : 0 < Ideal.absNorm v.asIdeal := by have := two_le_absNorm v; omega
  rw [Complex.norm_natCast_cpow_of_pos hpos]; simp

private theorem eulerFactor_ne_zero {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {s : ℂ}
    (hs : 1 < s.re) : (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹ ≠ 0 := by
  rw [Ne, inv_eq_zero, sub_eq_zero]
  intro h
  have hn : ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_absNorm_cpow]
    have h2 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
      have := two_le_absNorm v; exact_mod_cast (show 1 < Ideal.absNorm v.asIdeal by omega)
    exact Real.rpow_lt_one_of_one_lt_of_neg h2 (by linarith)
  rw [← h, norm_one] at hn
  exact lt_irrefl _ hn

private theorem tprod_compl_eq {ι : Type} {f : ι → ℂ} {P : ℂ} (hf : HasProd f P) (T : Finset ι)
    (hne : ∀ v ∈ T, f v ≠ 0) :
    ∏' v : {v : ι // v ∉ T}, f v.1 = P * ∏ v ∈ T, (f v)⁻¹ := by
  classical
  set g : ι → ℂ := fun v => if v ∈ T then (f v)⁻¹ else 1 with hg
  have hgT : HasProd g (∏ v ∈ T, (f v)⁻¹) := by
    have h : HasProd g (∏ v ∈ T, g v) := hasProd_prod_of_ne_finset_one (fun v hv => by simp [hg, hv])
    rwa [Finset.prod_congr rfl (fun v hv => by simp [hg, hv] : ∀ v ∈ T, g v = (f v)⁻¹)] at h
  have hmul := hf.mul hgT
  have hind : (fun v => f v * g v) = Set.mulIndicator {v | v ∉ T} f := by
    funext v
    by_cases hv : v ∈ T
    · simp [hg, hv, mul_inv_cancel₀ (hne v hv)]
    · simp [hg, hv]
  rw [hind] at hmul
  have h1 : ∏' v : {v : ι // v ∉ T}, f v.1 = ∏' v, Set.mulIndicator {v | v ∉ T} f v :=
    tprod_subtype {v : ι | v ∉ T} f
  rw [h1, hmul.tprod_eq]

private theorem tprod_compl_eulerFactor_eq {K : Type} [Field K] [NumberField K]
    (T : Finset (HeightOneSpectrum (𝓞 K))) {z : ℂ} (hz : 1 < z.re) :
    ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z))⁻¹
      = NumberField.dedekindZeta K z * ∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)) := by
  have h := tprod_compl_eq (NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta K z hz) T
    (fun v _ => eulerFactor_ne_zero v hz)
  rw [h]
  congr 1
  exact Finset.prod_congr rfl fun v _ => inv_inv _

private theorem dedekindZeta_eq_tprod {K : Type} [Field K] [NumberField K] {u : ℂ} (hu : 1 < u.re) :
    NumberField.dedekindZeta K u
      = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ (∅ : Finset (HeightOneSpectrum (𝓞 K)))},
          (1 - (fun _ : HeightOneSpectrum (𝓞 K) => (1 : ℂ)) v.1
            * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-u)))⁻¹ := by
  have h := tprod_compl_eulerFactor_eq (K := K) ∅ hu
  simp only [Finset.prod_empty, mul_one] at h
  rw [← h]
  simp only [one_mul]

private theorem norm_prod_eulerFactor_le {K : Type} [Field K] [NumberField K]
    (T : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ) {z : ℂ} (hz : σ ≤ z.re) :
    ‖∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z))‖
      ≤ ∏ v ∈ T, (1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) := by
  rw [Complex.norm_prod]
  refine Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => ?_
  have h1 : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    have := two_le_absNorm v; exact_mod_cast (show 1 ≤ Ideal.absNorm v.asIdeal by omega)
  calc ‖1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)‖
      ≤ ‖(1 : ℂ)‖ + ‖((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)‖ := norm_sub_le _ _
    _ = 1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (-z.re) := by rw [norm_one, norm_absNorm_cpow]
    _ ≤ 1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by
        gcongr

private theorem norm_discr_cpow (K : Type) [Field K] [NumberField K] (y : ℂ) :
    ‖(((|NumberField.discr K| : ℤ)) : ℂ) ^ y‖ = (((|NumberField.discr K| : ℤ)) : ℝ) ^ y.re := by
  have hpos : (0 : ℝ) < ((|NumberField.discr K| : ℤ) : ℝ) := by
    exact_mod_cast abs_pos.mpr (NumberField.discr_ne_zero K)
  rw [← Complex.ofReal_intCast, norm_cpow_eq_rpow_re_of_pos hpos]

private theorem one_le_discrR (K : Type) [Field K] [NumberField K] :
    (1 : ℝ) ≤ ((|NumberField.discr K| : ℤ) : ℝ) := by
  exact_mod_cast Int.one_le_abs (NumberField.discr_ne_zero K)

private theorem exists_bound_rect (f : ℂ → ℂ) (hf : Continuous f) (a b : ℝ) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ z : ℂ, a ≤ z.re → z.re ≤ b → |z.im| ≤ 2 → ‖f z‖ ≤ M₀ := by
  set φ : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I with hφ
  have hφc : Continuous φ :=
    (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hK : IsCompact (φ '' (Set.Icc a b ×ˢ Set.Icc (-2 : ℝ) 2)) :=
    (isCompact_Icc.prod isCompact_Icc).image hφc
  obtain ⟨M₀, hM₀⟩ := hK.bddAbove_image (hf.norm.continuousOn)
  refine ⟨max M₀ 0, le_max_right _ _, fun z h₁ h₂ h₃ => ?_⟩
  have hz : z ∈ φ '' (Set.Icc a b ×ˢ Set.Icc (-2 : ℝ) 2) := by
    refine ⟨(z.re, z.im), ⟨⟨h₁, h₂⟩, abs_le.mp h₃⟩, ?_⟩
    simp only [hφ]
    exact Complex.re_add_im z
  exact le_trans (hM₀ (Set.mem_image_of_mem _ hz)) (le_max_left _ _)

private def eulerT (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) (z : ℂ) : ℂ :=
  ∏ v ∈ T, (1 - ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z))

private theorem differentiable_eulerT (K : Type) [Field K] [NumberField K]
    (T : Finset (HeightOneSpectrum (𝓞 K))) : Differentiable ℂ (eulerT K T) :=
  differentiable_prod_eulerFactor T

private theorem norm_eulerT_le (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : ℝ) {z : ℂ} (hz : σ ≤ z.re) :
    ‖eulerT K T z‖ ≤ ∏ v ∈ T, (1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)) :=
  norm_prod_eulerFactor_le T σ hz

private def compFn (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) (ξ : ℂ → ℂ)
    (r₁ r₂ : ℕ) (z : ℂ) : ℂ :=
  ξ z * eulerT K T z * z⁻¹ * (((|NumberField.discr K| : ℤ)) : ℂ) ^ (-(z / 2)) * ((Gammaℝ z)⁻¹) ^ r₁
    * ((Gammaℝ z)⁻¹ * (Gammaℝ (z + 1))⁻¹) ^ r₂

open scoped Classical in

private theorem shift_eq_of_eq_eulerProduct (K : Type) [Field K] [NumberField K] (τ : ℝ)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (Q : ℂ → ℂ)
    (hQE : ∀ s : ℂ, 1 < s.re →
      Q s = (s - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) *
        ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt (normPowChar K τ) v.1 then
                (((normPowChar K τ) (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    ∀ z : ℂ, 1 < z.re →
      Q (z - ((τ : ℝ) : ℂ) * Complex.I) = (z - 1) * (NumberField.dedekindZeta K z * eulerT K T z) := by
  intro z hz
  have hτre : (((τ : ℝ) : ℂ) * Complex.I).re = 0 := by simp
  have hzre : 1 < (z - ((τ : ℝ) : ℂ) * Complex.I).re := by rw [Complex.sub_re, hτre]; linarith
  rw [hQE _ hzre]
  have hfac : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
      (1 - (if IsUnramifiedCharAt (normPowChar K τ) v.1 then
          (((normPowChar K τ) (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
        (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(z - ((τ : ℝ) : ℂ) * Complex.I))))⁻¹
      = (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z))⁻¹ := by
    intro v
    rw [NumberField.TateGlobal.ite_isUnramifiedCharAt_normPowChar_apply_uniformizerIdele_eq_absNorm_cpow_neg,
      ← cpow_add _ _ (absNormC_ne_zero v.1)]
    congr 3
    ring
  rw [tprod_congr hfac, tprod_compl_eulerFactor_eq T hz, eulerT]
  ring

private theorem compFn_differentiableOn (K : Type) [Field K] [NumberField K]
    (T : Finset (HeightOneSpectrum (𝓞 K))) {ξ : ℂ → ℂ} (hξd : Differentiable ℂ ξ) (r₁ r₂ : ℕ) :
    DifferentiableOn ℂ (compFn K T ξ r₁ r₂) ({0}ᶜ : Set ℂ) := by
  have hd0 : (((|NumberField.discr K| : ℤ)) : ℂ) ≠ 0 := by
    exact_mod_cast (abs_pos.mpr (NumberField.discr_ne_zero K)).ne'
  have h : DifferentiableOn ℂ (fun z : ℂ => ξ z * eulerT K T z * z⁻¹
      * (((|NumberField.discr K| : ℤ)) : ℂ) ^ (-(z / 2)) * ((Gammaℝ z)⁻¹) ^ r₁
      * ((Gammaℝ z)⁻¹ * (Gammaℝ (z + 1))⁻¹) ^ r₂) ({0}ᶜ : Set ℂ) := by
    refine DifferentiableOn.mul (DifferentiableOn.mul (DifferentiableOn.mul (DifferentiableOn.mul
      (hξd.differentiableOn.mul (differentiable_eulerT K T).differentiableOn) ?_) ?_) ?_) ?_
    · exact differentiableOn_inv.mono fun z hz => hz
    · exact ((differentiable_id.div_const (2 : ℂ)).neg.const_cpow (Or.inl hd0)).differentiableOn
    · exact (differentiable_Gammaℝ_inv.pow r₁).differentiableOn
    · exact ((differentiable_Gammaℝ_inv.mul
        (differentiable_Gammaℝ_inv.comp (differentiable_id.add_const (1 : ℂ)))).pow r₂).differentiableOn
  exact h

private theorem eq_compFn (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K)))
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (Λ ξ : ℂ → ℂ) (hξd : Differentiable ℂ ξ)
    (hξeq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s)
    (hΛprod : ∀ s : ℂ, 1 < s.re → Λ s =
      (((|NumberField.discr K| : ℤ)) : ℂ) ^ (s / 2) * Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
        * (Gammaℝ s * Gammaℝ (s + 1)) ^ NumberField.InfinitePlace.nrComplexPlaces K * NumberField.dedekindZeta K s)
    (hFA : ∀ s : ℂ, 1 < s.re → F s = (s - 1) * (NumberField.dedekindZeta K s * eulerT K T s)) :
    ∀ z : ℂ, z ≠ 0 →
      F z = compFn K T ξ (NumberField.InfinitePlace.nrRealPlaces K)
        (NumberField.InfinitePlace.nrComplexPlaces K) z := by
  have hd0 : (((|NumberField.discr K| : ℤ)) : ℂ) ≠ 0 := by
    exact_mod_cast (abs_pos.mpr (NumberField.discr_ne_zero K)).ne'

  have hright : ∀ z : ℂ, 1 < z.re →
      F z = compFn K T ξ (NumberField.InfinitePlace.nrRealPlaces K)
        (NumberField.InfinitePlace.nrComplexPlaces K) z := by
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      norm_num at hz
    have hz1 : z ≠ 1 := by
      rintro rfl
      norm_num at hz
    have hΓ : Gammaℝ z ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
    have hΓ1 : Gammaℝ (z + 1) ≠ 0 := by
      refine Gammaℝ_ne_zero_of_re_pos ?_
      rw [Complex.add_re, Complex.one_re]
      linarith
    have hdz : (((|NumberField.discr K| : ℤ)) : ℂ) ^ (z / 2) ≠ 0 := by
      intro h
      exact hd0 ((cpow_eq_zero_iff _ _).mp h).1
    rw [hFA z hz, compFn, hξeq z hz0 hz1, hΛprod z hz, cpow_neg]
    set dz : ℂ := (((|NumberField.discr K| : ℤ)) : ℂ) ^ (z / 2)
    set g₀ : ℂ := Gammaℝ z
    set g₁ : ℂ := Gammaℝ (z + 1)
    set n₁ : ℕ := NumberField.InfinitePlace.nrRealPlaces K
    set n₂ : ℕ := NumberField.InfinitePlace.nrComplexPlaces K
    have h₁ : z * z⁻¹ = 1 := mul_inv_cancel₀ hz0
    have h₂ : dz * dz⁻¹ = 1 := mul_inv_cancel₀ hdz
    have h₃ : g₀ ^ n₁ * g₀⁻¹ ^ n₁ = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hΓ, one_pow]
    have h₄ : (g₀ * g₁) ^ n₂ * (g₀⁻¹ * g₁⁻¹) ^ n₂ = 1 := by
      rw [← mul_pow, ← mul_inv, mul_inv_cancel₀ (mul_ne_zero hΓ hΓ1), one_pow]
    linear_combination
      (-((z - 1) * (NumberField.dedekindZeta K z * eulerT K T z))) * h₁ +
        (-((z - 1) * (NumberField.dedekindZeta K z * eulerT K T z)) * (z * z⁻¹)) * h₂ +
        (-((z - 1) * (NumberField.dedekindZeta K z * eulerT K T z)) * (z * z⁻¹) * (dz * dz⁻¹)) * h₃ +
        (-((z - 1) * (NumberField.dedekindZeta K z * eulerT K T z)) * (z * z⁻¹) * (dz * dz⁻¹) *
          (g₀ ^ n₁ * g₀⁻¹ ^ n₁)) * h₄

  have hF_an : AnalyticOnNhd ℂ F ({0}ᶜ : Set ℂ) :=
    (Complex.analyticOnNhd_univ_iff_differentiable.2 hF).mono (Set.subset_univ _)
  have hC_an : AnalyticOnNhd ℂ (compFn K T ξ (NumberField.InfinitePlace.nrRealPlaces K)
      (NumberField.InfinitePlace.nrComplexPlaces K)) ({0}ᶜ : Set ℂ) :=
    (compFn_differentiableOn K T hξd (NumberField.InfinitePlace.nrRealPlaces K)
      (NumberField.InfinitePlace.nrComplexPlaces K)).analyticOnNhd isOpen_compl_singleton
  have hconn : IsPreconnected ({0}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; exact Cardinal.one_lt_two) (0 : ℂ)).isPreconnected
  have hev : F =ᶠ[nhds (2 : ℂ)] compFn K T ξ (NumberField.InfinitePlace.nrRealPlaces K)
      (NumberField.InfinitePlace.nrComplexPlaces K) := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : (2 : ℂ) ∈ {w : ℂ | 1 < w.re} := by simp
    exact Filter.eventually_of_mem (hopen.mem_nhds h2) fun w hw => hright w hw
  intro z hz
  exact hF_an.eqOn_of_preconnected_of_eventuallyEq hC_an hconn
    (Set.mem_compl_singleton_iff.mpr two_ne_zero) hev (Set.mem_compl_singleton_iff.mpr hz)

private theorem isPolyBdd_compFn_left (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K)))
    (Λ ξ : ℂ → ℂ) (hξeq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s)
    (hΛfe : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ (1 - s) = Λ s)
    (r₁ r₂ : ℕ)
    (hΛprod : ∀ s : ℂ, 1 < s.re → Λ s =
      (((|NumberField.discr K| : ℤ)) : ℂ) ^ (s / 2) * Gammaℝ s ^ r₁ * (Gammaℝ s * Gammaℝ (s + 1)) ^ r₂
        * NumberField.dedekindZeta K s)
    (σL : ℝ) (hσL : σL ≤ -1) :
    IsPolyBdd (fun z => ‖compFn K T ξ r₁ r₂ z‖) {z : ℂ | z.re = σL ∧ 2 ≤ |z.im|} := by
  have hq := exists_gammaR_quot_le σL (2 - σL)
  obtain ⟨cq, nq, hcq, hquot⟩ := hq
  have hζ := exists_forall_norm_tprod_le K ∅ (fun _ => (1 : ℂ)) (fun _ => by simp) 2 one_lt_two
  obtain ⟨Bζ, hBζ⟩ := hζ

  have him0 : ∀ z : ℂ, z ∈ {z : ℂ | z.re = σL ∧ 2 ≤ |z.im|} → z.im ≠ 0 := by
    intro z hz h
    have h2 := hz.2
    rw [h, abs_zero] at h2
    linarith

  have h1 : IsPolyBdd (fun z => ‖z - 1‖) {z : ℂ | z.re = σL ∧ 2 ≤ |z.im|} :=
    (isPolyBdd_norm_sub σL σL 1).mono fun z hz => ⟨le_of_eq hz.1.symm, le_of_eq hz.1⟩

  have h2 : IsPolyBdd (fun z => ‖eulerT K T z‖) {z : ℂ | z.re = σL ∧ 2 ≤ |z.im|} :=
    isPolyBdd_of_bdd fun z hz => ⟨norm_nonneg _, norm_eulerT_le K T σL (le_of_eq hz.1.symm)⟩

  have h3 : IsPolyBdd (fun z => ‖(((|NumberField.discr K| : ℤ)) : ℂ) ^ ((1 - z) / 2)‖ *
      ‖(((|NumberField.discr K| : ℤ)) : ℂ) ^ (-(z / 2))‖) {z : ℂ | z.re = σL ∧ 2 ≤ |z.im|} := by
    refine isPolyBdd_of_bdd (c := ((|NumberField.discr K| : ℤ) : ℝ) ^ ((1 - σL) / 2) *
      ((|NumberField.discr K| : ℤ) : ℝ) ^ (-(σL / 2))) fun z hz => ⟨?_, le_of_eq ?_⟩
    · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    · have e1 : ((1 - z) / 2).re = (1 - σL) / 2 := by simp [hz.1]
      have e2 : (-(z / 2)).re = -(σL / 2) := by simp [hz.1]
      rw [norm_discr_cpow, norm_discr_cpow, e1, e2]

  have h4 : IsPolyBdd (fun z => ‖Gammaℝ (1 - z)‖ * ‖Gammaℝ z‖⁻¹) {z : ℂ | z.re = σL ∧ 2 ≤ |z.im|} := by
    refine ⟨cq, nq, hcq, fun z hz => ⟨mul_nonneg (norm_nonneg _) (inv_nonneg.2 (norm_nonneg _)), ?_⟩⟩
    have habs : |(1 - z).im| = |z.im| := by simp
    have h := hquot (1 - z) z (by simp only [Complex.sub_re, Complex.one_re]; linarith [hz.1])
      (by simp only [Complex.sub_re, Complex.one_re]; linarith [hz.1]) (by linarith [hz.1])
      (by linarith [hz.1]) (by rw [habs]; exact hz.2) habs.symm
    rwa [habs] at h
  have h5 : IsPolyBdd (fun z => ‖Gammaℝ (1 - z + 1)‖ * ‖Gammaℝ (z + 1)‖⁻¹)
      {z : ℂ | z.re = σL ∧ 2 ≤ |z.im|} := by
    refine ⟨cq, nq, hcq, fun z hz => ⟨mul_nonneg (norm_nonneg _) (inv_nonneg.2 (norm_nonneg _)), ?_⟩⟩
    have habs : |(1 - z + 1).im| = |z.im| := by simp
    have habs' : |(z + 1).im| = |z.im| := by simp
    have h := hquot (1 - z + 1) (z + 1)
      (by simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; linarith [hz.1])
      (by simp only [Complex.sub_re, Complex.add_re, Complex.one_re]; linarith [hz.1])
      (by simp only [Complex.add_re, Complex.one_re]; linarith [hz.1])
      (by simp only [Complex.add_re, Complex.one_re]; linarith [hz.1]) (by rw [habs]; exact hz.2)
      (by rw [habs, habs'])
    rwa [habs] at h

  have h6 : IsPolyBdd (fun z => ‖NumberField.dedekindZeta K (1 - z)‖) {z : ℂ | z.re = σL ∧ 2 ≤ |z.im|} := by
    refine isPolyBdd_of_bdd (c := Bζ) fun z hz => ⟨norm_nonneg _, ?_⟩
    have hre : 1 < (1 - z).re := by simp only [Complex.sub_re, Complex.one_re]; linarith [hz.1]
    rw [dedekindZeta_eq_tprod hre]
    exact hBζ (1 - z) (by simp only [Complex.sub_re, Complex.one_re]; linarith [hz.1])

  have hF := ((((h1.mul h2).mul h3).mul (h4.pow r₁)).mul ((h4.mul h5).pow r₂)).mul h6
  refine hF.of_le fun z hz => ⟨norm_nonneg _, ?_⟩
  beta_reduce
  have hz0 : z ≠ 0 := fun h => him0 z hz (by rw [h, Complex.zero_im])
  have hz1 : z ≠ 1 := fun h => him0 z hz (by rw [h, Complex.one_im])
  have hre : 1 < (1 - z).re := by simp only [Complex.sub_re, Complex.one_re]; linarith [hz.1]
  have hξz : ξ z = z * (z - 1) * Λ z := hξeq z hz0 hz1
  have hΛz : Λ z = Λ (1 - z) := (hΛfe z hz0 hz1).symm
  have hcomp : compFn K T ξ r₁ r₂ z = (z - 1) * eulerT K T z *
      ((((|NumberField.discr K| : ℤ)) : ℂ) ^ ((1 - z) / 2) * (((|NumberField.discr K| : ℤ)) : ℂ) ^ (-(z / 2))) *
      (Gammaℝ (1 - z) * (Gammaℝ z)⁻¹) ^ r₁ *
      ((Gammaℝ (1 - z) * (Gammaℝ z)⁻¹) * (Gammaℝ (1 - z + 1) * (Gammaℝ (z + 1))⁻¹)) ^ r₂ *
      NumberField.dedekindZeta K (1 - z) := by
    rw [compFn, hξz, hΛz, hΛprod (1 - z) hre]
    linear_combination ((z - 1) * eulerT K T z *
      ((((|NumberField.discr K| : ℤ)) : ℂ) ^ ((1 - z) / 2) * (((|NumberField.discr K| : ℤ)) : ℂ) ^ (-(z / 2))) *
      (Gammaℝ (1 - z) * (Gammaℝ z)⁻¹) ^ r₁ *
      ((Gammaℝ (1 - z) * (Gammaℝ z)⁻¹) * (Gammaℝ (1 - z + 1) * (Gammaℝ (z + 1))⁻¹)) ^ r₂ *
      NumberField.dedekindZeta K (1 - z)) * (mul_inv_cancel₀ hz0 : z * z⁻¹ = 1)
  rw [hcomp]
  simp only [norm_mul, norm_pow, norm_inv]
  exact le_of_eq (by ring)

private theorem exists_compFn_growth (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K)))
    (ξ : ℂ → ℂ) (Cξ : ℝ) (hξg : ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ Cξ * ‖s‖ * Real.log ‖s‖) (r₁ r₂ : ℕ)
    (σL σR : ℝ) :
    ∃ (Cg Dg : ℝ), 0 ≤ Cg ∧ 0 ≤ Dg ∧ ∀ z : ℂ, σL ≤ z.re → z.re ≤ σR → 2 ≤ |z.im| →
      ‖compFn K T ξ r₁ r₂ z‖ ≤ Dg * Real.exp (Cg * ‖z‖ * Real.log (2 + ‖z‖)) := by
  have hgam := exists_gammaR_inv_le σL (σR + 1)
  obtain ⟨Ai, Ni, hAi, hΓ⟩ := hgam
  have hdR : (1 : ℝ) ≤ ((|NumberField.discr K| : ℤ) : ℝ) := one_le_discrR K
  refine ⟨max Cξ 0 + (Ni + Real.pi / 4) * ((r₁ + 2 * r₂ : ℕ) : ℝ),
    (∏ v ∈ T, (1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (-σL))) *
      ((|NumberField.discr K| : ℤ) : ℝ) ^ (-(σL / 2)) * Ai ^ (r₁ + 2 * r₂),
    by positivity, by positivity, fun z hzL hzR hzim => ?_⟩
  have hz2 : 2 ≤ ‖z‖ := le_trans hzim (Complex.abs_im_le_norm z)
  have hz1 : 1 ≤ ‖z‖ := by linarith
  have hL1 : 1 ≤ Real.log (2 + ‖z‖) :=
    (Real.le_log_iff_exp_le (by positivity)).2 (by linarith [Real.exp_one_lt_d9])
  have hL0 : 0 ≤ Real.log (2 + ‖z‖) := by linarith
  set L := Real.log (2 + ‖z‖) with hL

  have hξ : ‖ξ z‖ ≤ Real.exp (max Cξ 0 * ‖z‖ * L) := by
    have hlz0 : 0 ≤ Real.log ‖z‖ := Real.log_nonneg hz1
    have hlzL : Real.log ‖z‖ ≤ L := Real.log_le_log (by linarith) (by linarith)
    have h1 : Real.log ‖ξ z‖ ≤ max Cξ 0 * ‖z‖ * L :=
      calc Real.log ‖ξ z‖ ≤ Cξ * ‖z‖ * Real.log ‖z‖ := hξg z hz2
        _ ≤ max Cξ 0 * ‖z‖ * Real.log ‖z‖ := by gcongr; exact le_max_left _ _
        _ ≤ max Cξ 0 * ‖z‖ * L := by gcongr
    rcases (norm_nonneg (ξ z)).eq_or_lt with h0 | hpos
    · rw [← h0]
      exact (Real.exp_pos _).le
    · calc ‖ξ z‖ = Real.exp (Real.log ‖ξ z‖) := (Real.exp_log hpos).symm
        _ ≤ Real.exp (max Cξ 0 * ‖z‖ * L) := Real.exp_le_exp.2 h1

  have hE : ‖eulerT K T z‖ ≤ ∏ v ∈ T, (1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (-σL)) := norm_eulerT_le K T σL hzL
  have hzi : ‖z⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hz1
  have hd : ‖(((|NumberField.discr K| : ℤ)) : ℂ) ^ (-(z / 2))‖ ≤ ((|NumberField.discr K| : ℤ) : ℝ) ^ (-(σL / 2)) := by
    rw [norm_discr_cpow]
    refine Real.rpow_le_rpow_of_exponent_le hdR ?_
    have hre : (-(z / 2)).re = -(z.re / 2) := by simp
    rw [hre]
    linarith

  have hG : ∀ w : ℂ, σL ≤ w.re → w.re ≤ σR + 1 → |w.im| = |z.im| →
      ‖(Gammaℝ w)⁻¹‖ ≤ Ai * Real.exp ((Ni + Real.pi / 4) * (‖z‖ * L)) := by
    intro w h1 h2 h3
    have hw2 : 2 ≤ |w.im| := by
      rw [h3]
      exact hzim
    have h := hΓ w h1 h2 hw2
    rw [norm_inv]
    refine h.trans ?_
    rw [h3]
    have hP : (1 + |z.im|) ^ Ni ≤ Real.exp (Ni * (‖z‖ * L)) := by
      have h1' : 1 + |z.im| ≤ Real.exp L := by
        rw [hL, Real.exp_log (by positivity)]
        linarith [Complex.abs_im_le_norm z]
      calc (1 + |z.im|) ^ Ni ≤ Real.exp L ^ Ni := pow_le_pow_left₀ (by positivity) h1' Ni
        _ = Real.exp (Ni * L) := (Real.exp_nat_mul L Ni).symm
        _ ≤ Real.exp (Ni * (‖z‖ * L)) := by
          refine Real.exp_le_exp.2 ?_
          have hLz : L ≤ ‖z‖ * L := le_mul_of_one_le_left hL0 hz1
          exact mul_le_mul_of_nonneg_left hLz (Nat.cast_nonneg Ni)
    have hX : Real.exp (Real.pi / 4 * |z.im|) ≤ Real.exp (Real.pi / 4 * (‖z‖ * L)) := by
      refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ (by positivity))
      calc |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
        _ ≤ ‖z‖ * L := le_mul_of_one_le_right (norm_nonneg z) hL1
    calc Ai * (1 + |z.im|) ^ Ni * Real.exp (Real.pi / 4 * |z.im|)
        ≤ Ai * Real.exp (Ni * (‖z‖ * L)) * Real.exp (Real.pi / 4 * (‖z‖ * L)) := by gcongr
      _ = Ai * Real.exp ((Ni + Real.pi / 4) * (‖z‖ * L)) := by
        rw [mul_assoc, ← Real.exp_add,
          show (Ni : ℝ) * (‖z‖ * L) + Real.pi / 4 * (‖z‖ * L) = (Ni + Real.pi / 4) * (‖z‖ * L) by ring]
  have hGz : ‖(Gammaℝ z)⁻¹‖ ≤ Ai * Real.exp ((Ni + Real.pi / 4) * (‖z‖ * L)) :=
    hG z hzL (by linarith) rfl
  have hGz1 : ‖(Gammaℝ (z + 1))⁻¹‖ ≤ Ai * Real.exp ((Ni + Real.pi / 4) * (‖z‖ * L)) :=
    hG (z + 1) (by simp only [Complex.add_re, Complex.one_re]; linarith)
      (by simp only [Complex.add_re, Complex.one_re]; linarith) (by simp)
  calc ‖compFn K T ξ r₁ r₂ z‖
      = ‖ξ z‖ * ‖eulerT K T z‖ * ‖z⁻¹‖ * ‖(((|NumberField.discr K| : ℤ)) : ℂ) ^ (-(z / 2))‖ *
          ‖(Gammaℝ z)⁻¹‖ ^ r₁ * (‖(Gammaℝ z)⁻¹‖ * ‖(Gammaℝ (z + 1))⁻¹‖) ^ r₂ := by
        simp only [compFn, norm_mul, norm_pow]
    _ ≤ Real.exp (max Cξ 0 * ‖z‖ * L) * (∏ v ∈ T, (1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (-σL))) * 1 *
          ((|NumberField.discr K| : ℤ) : ℝ) ^ (-(σL / 2)) *
          (Ai * Real.exp ((Ni + Real.pi / 4) * (‖z‖ * L))) ^ r₁ *
          ((Ai * Real.exp ((Ni + Real.pi / 4) * (‖z‖ * L))) *
            (Ai * Real.exp ((Ni + Real.pi / 4) * (‖z‖ * L)))) ^ r₂ := by
        gcongr
    _ = (∏ v ∈ T, (1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (-σL))) *
          ((|NumberField.discr K| : ℤ) : ℝ) ^ (-(σL / 2)) * Ai ^ (r₁ + 2 * r₂) *
          Real.exp ((max Cξ 0 + (Ni + Real.pi / 4) * ((r₁ + 2 * r₂ : ℕ) : ℝ)) * ‖z‖ * L) := by
        rw [show (max Cξ 0 + (Ni + Real.pi / 4) * ((r₁ + 2 * r₂ : ℕ) : ℝ)) * ‖z‖ * L
            = max Cξ 0 * ‖z‖ * L + ((r₁ + 2 * r₂ : ℕ) : ℝ) * ((Ni + Real.pi / 4) * (‖z‖ * L)) by ring,
          Real.exp_add, Real.exp_nat_mul]
        ring

private theorem growth_of_eq (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K)))
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hFA : ∀ s : ℂ, 1 < s.re → F s = (s - 1) * (NumberField.dedekindZeta K s * eulerT K T s)) (σ₁ σ₂ : ℝ) :
    ∃ (A : ℝ) (N : ℕ), ∀ z : ℂ, σ₁ ≤ z.re → z.re ≤ σ₂ → ‖F z‖ ≤ A * (1 + |z.im|) ^ N := by

  set σL : ℝ := min σ₁ (-1) with hσL
  set σR : ℝ := max σ₂ 2 with hσR
  have hσL1 : σL ≤ -1 := min_le_right _ _
  have hσLσ₁ : σL ≤ σ₁ := min_le_left _ _
  have hσR2 : 2 ≤ σR := le_max_right _ _
  have hσ₂R : σ₂ ≤ σR := le_max_left _ _
  have hσLR : σL < σR := by linarith

  have hpkg := NumberField.exists_completedDedekindZeta_package K
  obtain ⟨Λ, -, hΛfe, hΛprod₀, ⟨ξ, hξd, hξeq, Cξ, hξg⟩, -, -⟩ := hpkg
  have hΛprod : ∀ s : ℂ, 1 < s.re → Λ s =
      (((|NumberField.discr K| : ℤ)) : ℂ) ^ (s / 2) * Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
        * (Gammaℝ s * Gammaℝ (s + 1)) ^ NumberField.InfinitePlace.nrComplexPlaces K
        * NumberField.dedekindZeta K s := by
    intro s hs
    rw [hΛprod₀ s hs]
    simp only [Gammaℝ_mul_Gammaℝ_add_one]
  have hC := eq_compFn K T F hF Λ ξ hξd hξeq hΛprod hFA

  have hB0 := exists_forall_norm_tprod_le K ∅ (fun _ => (1 : ℂ)) (fun _ => by simp) 2 one_lt_two
  obtain ⟨B, hB⟩ := hB0
  have hline_R : IsPolyBdd (fun z => ‖F z‖) {z : ℂ | z.re = σR} := by
    have hsub : IsPolyBdd (fun z => ‖z - 1‖) {z : ℂ | z.re = σR} :=
      (isPolyBdd_norm_sub σR σR 1).mono fun z hz => by
        simp only [Set.mem_setOf_eq] at hz ⊢; exact ⟨hz.ge, hz.le⟩
    have hζ : IsPolyBdd (fun z => ‖NumberField.dedekindZeta K z‖) {z : ℂ | z.re = σR} := by
      refine isPolyBdd_of_bdd (c := B) fun z hz => ⟨norm_nonneg _, ?_⟩
      beta_reduce
      have hz' : z.re = σR := hz
      have hu : 1 < z.re := by rw [hz']; linarith
      rw [dedekindZeta_eq_tprod hu]
      exact hB z (by rw [hz']; linarith)
    have hE : IsPolyBdd (fun z => ‖eulerT K T z‖) {z : ℂ | z.re = σR} := by
      refine isPolyBdd_of_bdd (c := ∏ v ∈ T, (1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (-σR))) fun z hz =>
        ⟨norm_nonneg _, ?_⟩
      beta_reduce
      have hz' : z.re = σR := hz
      exact norm_eulerT_le K T σR (le_of_eq hz'.symm)
    refine ((hsub.mul hζ).mul hE).of_le fun z hz => ⟨norm_nonneg _, ?_⟩
    beta_reduce
    have hz' : z.re = σR := hz
    rw [hFA z (by rw [hz']; linarith), norm_mul, norm_mul]
    exact le_of_eq (by ring)

  have hline_L2 : IsPolyBdd (fun z => ‖F z‖) {z : ℂ | z.re = σL ∧ 2 ≤ |z.im|} := by
    refine (isPolyBdd_compFn_left K T Λ ξ hξeq hΛfe _ _ hΛprod σL hσL1).of_le fun z hz =>
      ⟨norm_nonneg _, le_of_eq ?_⟩
    beta_reduce
    have hz0 : z ≠ 0 := by
      intro h
      have h2 := hz.2
      rw [h] at h2
      simp only [Complex.zero_im, abs_zero] at h2
      linarith
    rw [hC z hz0]

  have hM := exists_bound_rect F hF.continuous σL σR
  obtain ⟨M₀, hM₀0, hM₀⟩ := hM
  have hline_L0 : IsPolyBdd (fun z => ‖F z‖) {z : ℂ | z.re = σL ∧ |z.im| ≤ 2} :=
    isPolyBdd_of_bdd (c := M₀) fun z hz => ⟨norm_nonneg _, hM₀ z hz.1.ge (by linarith [hz.1]) hz.2⟩
  have hlines0 := (hline_L2.union hline_L0).union hline_R
  obtain ⟨A₀, N₀, -, hlines⟩ := hlines0
  have hL : ∀ t : ℝ, ‖F ((σL : ℂ) + t * Complex.I)‖ ≤ A₀ * (1 + |t|) ^ N₀ := by
    intro t
    have hre : ((σL : ℂ) + t * Complex.I).re = σL := by simp
    have him : ((σL : ℂ) + t * Complex.I).im = t := by simp
    have hmem : ((σL : ℂ) + t * Complex.I) ∈
        ({z : ℂ | z.re = σL ∧ 2 ≤ |z.im|} ∪ {z : ℂ | z.re = σL ∧ |z.im| ≤ 2}) ∪ {z : ℂ | z.re = σR} := by
      rcases le_total 2 |t| with h | h
      · exact Or.inl (Or.inl ⟨hre, by rw [him]; exact h⟩)
      · exact Or.inl (Or.inr ⟨hre, by rw [him]; exact h⟩)
    have h := (hlines _ hmem).2
    rwa [him] at h
  have hRl : ∀ t : ℝ, ‖F ((σR : ℂ) + t * Complex.I)‖ ≤ A₀ * (1 + |t|) ^ N₀ := by
    intro t
    have hre : ((σR : ℂ) + t * Complex.I).re = σR := by simp
    have him : ((σR : ℂ) + t * Complex.I).im = t := by simp
    have h := (hlines _ (Or.inr hre)).2
    rwa [him] at h

  have hg := exists_compFn_growth K T ξ Cξ hξg (NumberField.InfinitePlace.nrRealPlaces K)
    (NumberField.InfinitePlace.nrComplexPlaces K) σL σR
  obtain ⟨Cg, Dg, hCg0, hDg0, hgrow⟩ := hg
  have hgrowth : ∀ z : ℂ, σL ≤ z.re → z.re ≤ σR →
      ‖F z‖ ≤ max Dg M₀ * Real.exp (Cg * ‖z‖ * Real.log (2 + ‖z‖)) := by
    intro z h₁ h₂
    have hlog0 : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith [norm_nonneg z])
    have hX0 : 0 ≤ Cg * ‖z‖ * Real.log (2 + ‖z‖) := mul_nonneg (mul_nonneg hCg0 (norm_nonneg _)) hlog0
    have hexp1 : 1 ≤ Real.exp (Cg * ‖z‖ * Real.log (2 + ‖z‖)) := Real.one_le_exp hX0
    rcases le_or_gt 2 |z.im| with ht | ht
    · have hz0 : z ≠ 0 := by
        intro h
        rw [h] at ht
        simp only [Complex.zero_im, abs_zero] at ht
        linarith
      rw [hC z hz0]
      exact (hgrow z h₁ h₂ ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    · calc ‖F z‖ ≤ M₀ := hM₀ z h₁ h₂ ht.le
        _ ≤ max Dg M₀ := le_max_right _ _
        _ = max Dg M₀ * 1 := (mul_one _).symm
        _ ≤ max Dg M₀ * Real.exp (Cg * ‖z‖ * Real.log (2 + ‖z‖)) :=
            mul_le_mul_of_nonneg_left hexp1 (le_max_of_le_left hDg0)

  have hPL := exists_forall_norm_le_mul_pow F hF σL σR hσLR Cg (max Dg M₀) hgrowth A₀ N₀ hL hRl
  obtain ⟨A', N', h⟩ := hPL
  exact ⟨A', N', fun z h₁ h₂ => h z (by linarith) (by linarith)⟩

open scoped Classical in

private theorem main (K : Type) [Field K] [NumberField K] (τ : ℝ) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (σ₁ σ₂ : ℝ) (Q : ℂ → ℂ) (hQ : Differentiable ℂ Q)
    (hQE : ∀ s : ℂ, 1 < s.re →
      Q s = (s - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) *
        ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt (normPowChar K τ) v.1 then
                (((normPowChar K τ) (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → ‖Q w‖ ≤ A * (1 + |w.im|) ^ N := by
  have hA := shift_eq_of_eq_eulerProduct K τ T Q hQE
  have hQd : Differentiable ℂ fun z : ℂ => Q (z - ((τ : ℝ) : ℂ) * Complex.I) :=
    hQ.comp (differentiable_id.sub_const _)
  have hg := growth_of_eq K T (fun z : ℂ => Q (z - ((τ : ℝ) : ℂ) * Complex.I)) hQd (fun s hs => hA s hs) σ₁ σ₂
  obtain ⟨A', N', h⟩ := hg
  have hτre : (((τ : ℝ) : ℂ) * Complex.I).re = 0 := by simp
  have hτim : (((τ : ℝ) : ℂ) * Complex.I).im = τ := by simp
  refine ⟨max A' 0 * (1 + |τ|) ^ N', N', fun w hw₁ hw₂ => ?_⟩
  have h1 := h (w + ((τ : ℝ) : ℂ) * Complex.I) (by rw [Complex.add_re, hτre]; linarith)
    (by rw [Complex.add_re, hτre]; linarith)
  simp only [add_sub_cancel_right, Complex.add_im, hτim] at h1
  have hbase : 1 + |w.im + τ| ≤ (1 + |τ|) * (1 + |w.im|) := by
    nlinarith [abs_add_le w.im τ, mul_nonneg (abs_nonneg τ) (abs_nonneg w.im)]
  have hb0 : (0 : ℝ) ≤ 1 + |w.im + τ| := by positivity
  have hpow : (1 + |w.im + τ|) ^ N' ≤ ((1 + |τ|) * (1 + |w.im|)) ^ N' := pow_le_pow_left₀ hb0 hbase _
  calc ‖Q w‖ ≤ A' * (1 + |w.im + τ|) ^ N' := h1
    _ ≤ max A' 0 * (1 + |w.im + τ|) ^ N' := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max A' 0 * ((1 + |τ|) * (1 + |w.im|)) ^ N' := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
    _ = max A' 0 * (1 + |τ|) ^ N' * (1 + |w.im|) ^ N' := by rw [mul_pow]; ring

end ShiftedDedekindGrowth

end

open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K] (τ : ℝ) (T : Finset (HeightOneSpectrum (𝓞 K))) (σ₁ σ₂ : ℝ)
    (Q : ℂ → ℂ) (_hQ : Differentiable ℂ Q)
    (_hQE : ∀ s : ℂ, 1 < s.re →
      Q s = (s - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) *
        ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (if IsUnramifiedCharAt (normPowChar K τ) v.1 then
                (((normPowChar K τ) (uniformizerIdele K v.1) : ℂˣ) : ℂ) else 0) *
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    ∃ (A : ℝ) (N : ℕ), ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → ‖Q w‖ ≤ A * (1 + |w.im|) ^ N := by
  exact ShiftedDedekindGrowth.main K τ T σ₁ σ₂ Q _hQ _hQE

end S_NumberField_TateGlobal_exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_forall_norm_le_mul_of_eq_sub_mul_partialEulerProduct_normPowChar_of_re_mem_Icc (solution)
