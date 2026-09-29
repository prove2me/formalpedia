-- Prove2me | solution 1 for NumberField.TateGlobal.exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/57484423-f956-5938-987a-c70489cf34af

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_EulerProduct_norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp
import Theorems.Thm_PhragmenLindelof_exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip
import Theorems.Thm_NumberField_exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq
import Theorems.Thm_NumberField_exists_forall_norm_sub_one_mul_dedekindZeta_continuation_le_rpow_on_re_eq_neg_half
import Theorems.Thm_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Complex Filter Set
open scoped Topology

namespace R4LDCZstrip

theorem sq_le_four_mul_exp_abs (t : ℝ) : t ^ 2 ≤ 4 * Real.exp |t| := by
  have h1 : |t| / 2 + 1 ≤ Real.exp (|t| / 2) := Real.add_one_le_exp _
  have h0 : 0 ≤ |t| / 2 + 1 := by positivity
  have h2 : (|t| / 2 + 1) ^ 2 ≤ Real.exp (|t| / 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have h3 : Real.exp (|t| / 2) ^ 2 = Real.exp |t| := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have h4 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  nlinarith [abs_nonneg t, h2, h3, h4]

theorem gaussian_le_doubleExp (B C : ℝ) :
    ∃ B' : ℝ, ∀ t : ℝ, max B 1 * Real.exp (max C 0 * t ^ 2) ≤ Real.exp (B' * Real.exp (1 * |t|)) := by
  refine ⟨Real.log (max B 1) + 4 * max C 0, fun t => ?_⟩
  have hB1 : 1 ≤ max B 1 := le_max_right _ _
  have hB0 : 0 < max B 1 := one_pos.trans_le hB1
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hlog : 0 ≤ Real.log (max B 1) := Real.log_nonneg hB1
  have he1 : 1 ≤ Real.exp (1 * |t|) := by rw [one_mul]; exact Real.one_le_exp (abs_nonneg t)
  have hrew : max B 1 * Real.exp (max C 0 * t ^ 2) =
      Real.exp (Real.log (max B 1) + max C 0 * t ^ 2) := by
    rw [Real.exp_add, Real.exp_log hB0]
  rw [hrew, Real.exp_le_exp]
  have h1 : Real.log (max B 1) ≤ Real.log (max B 1) * Real.exp (1 * |t|) :=
    le_mul_of_one_le_right hlog he1
  have h2 : max C 0 * t ^ 2 ≤ 4 * max C 0 * Real.exp (1 * |t|) := by
    rw [one_mul]
    have := sq_le_four_mul_exp_abs t
    nlinarith
  nlinarith

theorem two_le_absNorm {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

section euler
variable {K : Type} [Field K] [NumberField K]

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

theorem norm_nC_cpow_neg_lt_one {s : ℂ} (hs : 0 < s.re) (v : HeightOneSpectrum (𝓞 K)) :
    ‖nC v ^ (-s)‖ < 1 := by
  rw [norm_nC_cpow_neg]
  have h1 : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_lt_two (two_le_absNorm v)
  exact Real.rpow_lt_one_of_one_lt_of_neg h1 (by linarith)

theorem one_sub_ne_zero {s : ℂ} (hs : 0 < s.re) (v : HeightOneSpectrum (𝓞 K)) :
    (1 : ℂ) - nC v ^ (-s) ≠ 0 := by
  intro h
  have hlt := norm_nC_cpow_neg_lt_one hs v
  rw [sub_eq_zero] at h
  rw [← h, norm_one] at hlt
  exact lt_irrefl _ hlt

theorem norm_nC_cpow_neg_le {s : ℂ} (hs : -1 / 2 ≤ s.re) (v : HeightOneSpectrum (𝓞 K)) :
    ‖nC v ^ (-s)‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ) := by
  rw [norm_nC_cpow_neg]
  exact Real.rpow_le_rpow_of_exponent_le (one_le_nR v) (by linarith)

def eulerFn (T : Finset (HeightOneSpectrum (𝓞 K))) (c : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
    (1 - c v.1 * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹

def M₁ (T : Finset (HeightOneSpectrum (𝓞 K))) : ℝ :=
  Real.exp (2 * ∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
    ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))

theorem one_le_M₁ (T : Finset (HeightOneSpectrum (𝓞 K))) : 1 ≤ M₁ (K := K) T := by
  unfold M₁
  refine Real.one_le_exp (mul_nonneg (by norm_num) (tsum_nonneg fun v => ?_))
  exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem summable_subtype_rpow (T : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} =>
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-σ) :=
  (NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K hσ).subtype _

theorem norm_eulerFn_le (T : Finset (HeightOneSpectrum (𝓞 K))) (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ v, ‖c v‖ ≤ 1) (s : ℂ) (hs : 3 / 2 ≤ s.re) : ‖eulerFn T c s‖ ≤ M₁ (K := K) T := by
  have hs1 : 1 < s.re := by linarith
  have hsum := summable_subtype_rpow (K := K) T hs1
  have h := EulerProduct.norm_tprod_inv_one_sub_mul_natCast_cpow_neg_le_exp
    (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => Ideal.absNorm v.1.asIdeal)
    (fun v => two_le_absNorm v.1) (fun v => c v.1) (fun v => hc v.1) s hs1.le hsum
  refine h.trans ?_
  unfold M₁
  rw [Real.exp_le_exp]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Summable.tsum_le_tsum (fun v => ?_) hsum (summable_subtype_rpow T (by norm_num))
  exact Real.rpow_le_rpow_of_exponent_le (one_le_nR v.1) (by linarith)

def corr (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ := ∏ v ∈ T, (1 - nC v ^ (-s))

theorem differentiable_corr (T : Finset (HeightOneSpectrum (𝓞 K))) : Differentiable ℂ (corr (K := K) T) := by
  unfold corr
  refine Differentiable.fun_finsetProd fun v _ => ?_
  refine (differentiable_const _).sub ?_
  refine Differentiable.const_cpow differentiable_neg (Or.inl ?_)
  unfold nC
  exact_mod_cast (nC_pos v).ne'

def PT (T : Finset (HeightOneSpectrum (𝓞 K))) : ℝ :=
  ∏ v ∈ T, (1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ))

theorem one_le_PT (T : Finset (HeightOneSpectrum (𝓞 K))) : 1 ≤ PT (K := K) T := by
  unfold PT
  refine Finset.one_le_prod fun v _ => ?_
  have : 0 ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  linarith

theorem norm_corr_le (T : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : -1 / 2 ≤ s.re) :
    ‖corr T s‖ ≤ PT (K := K) T := by
  unfold corr PT
  refine (Finset.norm_prod_le _ _).trans (Finset.prod_le_prod (fun v _ => norm_nonneg _) fun v _ => ?_)
  calc ‖(1 : ℂ) - nC v ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖nC v ^ (-s)‖ := norm_sub_le _ _
    _ ≤ 1 + (Ideal.absNorm v.asIdeal : ℝ) ^ (1 / 2 : ℝ) := by
        rw [norm_one]; linarith [norm_nC_cpow_neg_le hs v]

theorem hasProd_partial {s : ℂ} (hs : 1 < s.re) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => (1 - nC v.1 ^ (-s))⁻¹)
      (cexp (∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, -log (1 - nC v.1 ^ (-s)))) := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hne : ∀ v : HeightOneSpectrum (𝓞 K), (1 : ℂ) - nC v ^ (-s) ≠ 0 := one_sub_ne_zero hs0
  have hn : Summable fun v : HeightOneSpectrum (𝓞 K) => ‖nC v ^ (-s)‖ := by
    refine (NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K hs).congr fun v => ?_
    rw [norm_nC_cpow_neg]
  have hsub : Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => nC v.1 ^ (-s) :=
    (hn.subtype {v | v ∉ T}).of_norm
  have hg : Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => -log (1 - nC v.1 ^ (-s)) :=
    hsub.clog_one_sub.neg
  have H := hg.hasSum.cexp
  have hcongr : (cexp ∘ fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => -log (1 - nC v.1 ^ (-s))) =
      fun v => (1 - nC v.1 ^ (-s))⁻¹ := by
    funext v
    simp only [Function.comp_apply, exp_neg, exp_log (hne v.1)]
  rw [hcongr] at H
  exact H

theorem eulerFn_one_eq {s : ℂ} (hs : 1 < s.re) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    eulerFn T (fun _ => 1) s = dedekindZeta K s * corr T s := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  set E : ℂ := cexp (∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, -log (1 - nC v.1 ^ (-s))) with hE
  have hP := hasProd_partial (K := K) hs T
  have hEq : eulerFn T (fun _ => 1) s = E := by
    unfold eulerFn
    have := hP.tprod_eq
    simp only [one_mul]
    exact this
  have hE' : HasProd ((fun v : HeightOneSpectrum (𝓞 K) => (1 - nC v ^ (-s))⁻¹) ∘ (↑) :
      ((↑T : Set (HeightOneSpectrum (𝓞 K)))ᶜ : Set (HeightOneSpectrum (𝓞 K))) → ℂ) E := hP
  have hG : HasProd ((fun v : HeightOneSpectrum (𝓞 K) => (1 - nC v ^ (-s))⁻¹) ∘ (↑) :
      (↑T : Set (HeightOneSpectrum (𝓞 K))) → ℂ) (∏ v ∈ T, (1 - nC v ^ (-s))⁻¹) := Finset.hasProd T _
  have hall := hG.mul_isCompl isCompl_compl hE'
  have hζ : HasProd (fun v : HeightOneSpectrum (𝓞 K) => (1 - nC v ^ (-s))⁻¹) (dedekindZeta K s) :=
    NumberField.hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta K s hs
  have heq : (∏ v ∈ T, (1 - nC v ^ (-s))⁻¹) * E = dedekindZeta K s := HasProd.unique hall hζ
  have hne : corr T s ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => one_sub_ne_zero hs0 v
  have hinv : (∏ v ∈ T, (1 - nC v ^ (-s))⁻¹) = (corr T s)⁻¹ := by
    unfold corr; exact Finset.prod_inv_distrib _
  rw [hinv] at heq
  rw [hEq]
  calc E = corr T s * ((corr T s)⁻¹ * E) := by rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ = corr T s * dedekindZeta K s := by rw [heq]
    _ = dedekindZeta K s * corr T s := mul_comm _ _

end euler

section main
variable {K : Type} [Field K] [NumberField K]

theorem re_ofReal_add_mul_I (σ t : ℝ) : ((σ : ℂ) + t * I).re = σ := by simp

theorem im_ofReal_add_mul_I (σ t : ℝ) : ((σ : ℂ) + t * I).im = t := by simp

set_option maxHeartbeats 6400000 in
theorem main (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (Z : ℂ → ℂ), Differentiable ℂ Z →
        (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) →
      ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 5 / 2 → ‖Z s‖ ≤ C * (2 + |s.im|) ^ A := by

  obtain ⟨R, hRd, -, hReq, -⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero K
  obtain ⟨Cb, Ab, hCb, hAb, hleft⟩ :=
    NumberField.exists_forall_norm_sub_one_mul_dedekindZeta_continuation_le_rpow_on_re_eq_neg_half K
  set α : ℝ := Ab + 1 with hα
  have hα0 : 0 < α := by positivity
  have hα1 : 1 ≤ α := by rw [hα]; linarith
  obtain ⟨C₃, hC₃, hPL⟩ :=
    PhragmenLindelof.exists_norm_le_mul_one_add_abs_im_rpow_of_vertical_strip (-1 / 2) (3 / 2) α
      (by norm_num) hα0.le

  set M1 : ℝ := M₁ (K := K) T with hM1def
  have hM1 : 1 ≤ M1 := one_le_M₁ T
  set P : ℝ := PT (K := K) T with hPdef
  have hP1 : 1 ≤ P := one_le_PT T
  set M₀ : ℝ := max (Cb * P * (2 : ℝ) ^ Ab) (2 * M1) with hM₀
  have h2Ab : (1 : ℝ) ≤ (2 : ℝ) ^ Ab := Real.one_le_rpow (by norm_num) hAb.le
  have hM₀1 : 1 ≤ M₀ := by
    have : (1 : ℝ) ≤ 2 * M1 := by linarith
    exact this.trans (le_max_right _ _)
  have hM₀0 : 0 ≤ M₀ := zero_le_one.trans hM₀1
  set C₄ : ℝ := max C₃ 1 * M₀ with hC₄
  have hC₃C : C₃ ≤ max C₃ 1 := le_max_left _ _
  have hC₃1 : 1 ≤ max C₃ 1 := le_max_right _ _
  have hC₄1 : 1 ≤ C₄ := one_le_mul_of_one_le_of_one_le hC₃1 hM₀1
  have hC₄0 : 0 < C₄ := one_pos.trans_le hC₄1
  have hM₀C₄ : M₀ ≤ C₄ := le_mul_of_one_le_left hM₀0 hC₃1
  refine ⟨C₄, α, hC₄0, hα0, ?_⟩
  intro Z' hZ'd hZ'eq s hsa hsb

  set Z : ℂ → ℂ := fun s => R s * corr T s with hZ
  have hZd : Differentiable ℂ Z := hRd.mul (differentiable_corr T)

  have hZeq : ∀ s : ℂ, 1 < s.re → Z s = (s - 1) * eulerFn T (fun _ => 1) s := by
    intro s hs
    show R s * corr T s = (s - 1) * eulerFn T (fun _ => 1) s
    rw [hReq s hs, eulerFn_one_eq hs T, mul_assoc]

  have h1t : ∀ u : ℝ, 1 ≤ 1 + |u| := fun u => by linarith [abs_nonneg u]
  have hstrip : ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 3 / 2 → ‖Z z‖ ≤ C₃ * M₀ * (1 + |z.im|) ^ α := by
    refine hPL Z M₀ hM₀0 hZd.diffContOnCl ?_ ?_ ?_
    ·
      obtain ⟨B, Cg, hBC⟩ :=
        NumberField.exists_norm_sub_one_mul_dedekindZeta_continuation_le_mul_exp_mul_im_sq
          K R hRd hReq (-1 / 2) (3 / 2)
      obtain ⟨B', hB'⟩ := gaussian_le_doubleExp (B * P) Cg
      refine ⟨1, ?_, B', fun z hza hzb => ?_⟩
      · have : Real.pi / (3 / 2 - -1 / 2) = Real.pi / 2 := by norm_num
        rw [this]
        linarith [Real.pi_gt_three]
      · refine le_trans ?_ (hB' z.im)
        have hR := hBC z hza.le hzb.le
        have hc := norm_corr_le T hza.le
        have hZz : ‖Z z‖ ≤ B * P * Real.exp (Cg * z.im ^ 2) := by
          show ‖R z * corr T z‖ ≤ _
          rw [norm_mul]
          calc ‖R z‖ * ‖corr T z‖ ≤ (B * Real.exp (Cg * z.im ^ 2)) * P :=
                mul_le_mul hR hc (norm_nonneg _) ((norm_nonneg _).trans hR)
            _ = B * P * Real.exp (Cg * z.im ^ 2) := by ring
        refine hZz.trans ?_
        have hB1 : B * P ≤ max (B * P) 1 := le_max_left _ _
        have he : Real.exp (Cg * z.im ^ 2) ≤ Real.exp (max Cg 0 * z.im ^ 2) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
        calc B * P * Real.exp (Cg * z.im ^ 2) ≤ max (B * P) 1 * Real.exp (Cg * z.im ^ 2) :=
              mul_le_mul_of_nonneg_right hB1 (Real.exp_pos _).le
          _ ≤ max (B * P) 1 * Real.exp (max Cg 0 * z.im ^ 2) :=
              mul_le_mul_of_nonneg_left he (zero_le_one.trans (le_max_right _ _))
    ·
      intro z hz
      have hR := hleft R hRd hReq z hz
      have hc := norm_corr_le T hz.symm.le
      have h2t : (2 + |z.im|) ^ Ab ≤ (2 : ℝ) ^ Ab * (1 + |z.im|) ^ Ab := by
        rw [← Real.mul_rpow (by norm_num) (by positivity)]
        exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg z.im]) hAb.le
      have hup : (1 + |z.im|) ^ Ab ≤ (1 + |z.im|) ^ α :=
        Real.rpow_le_rpow_of_exponent_le (h1t z.im) (by rw [hα]; linarith)
      show ‖R z * corr T z‖ ≤ _
      rw [norm_mul]
      calc ‖R z‖ * ‖corr T z‖ ≤ (Cb * (2 + |z.im|) ^ Ab) * P :=
            mul_le_mul hR hc (norm_nonneg _) ((norm_nonneg _).trans hR)
        _ ≤ (Cb * ((2 : ℝ) ^ Ab * (1 + |z.im|) ^ α)) * P := by
            apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hP1)
            exact mul_le_mul_of_nonneg_left (h2t.trans (mul_le_mul_of_nonneg_left hup (by positivity)))
              hCb.le
        _ = (Cb * P * (2 : ℝ) ^ Ab) * (1 + |z.im|) ^ α := by ring
        _ ≤ M₀ * (1 + |z.im|) ^ α := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    ·
      intro z hz
      have hz1 : 1 < z.re := by rw [hz]; norm_num
      rw [hZeq z hz1, norm_mul]
      have h := norm_eulerFn_le T (fun _ => (1 : ℂ)) (fun _ => by rw [norm_one]) z (by rw [hz])
      have hz1n : ‖z - 1‖ ≤ 1 + |z.im| := by
        calc ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| := norm_le_abs_re_add_abs_im _
          _ = 1 / 2 + |z.im| := by
              rw [sub_re, one_re, hz, sub_im, one_im, sub_zero]; norm_num
          _ ≤ 1 + |z.im| := by linarith
      have hup : (1 + |z.im|) ≤ (1 + |z.im|) ^ α := by
        calc (1 + |z.im|) = (1 + |z.im|) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (1 + |z.im|) ^ α := Real.rpow_le_rpow_of_exponent_le (h1t z.im) hα1
      calc ‖z - 1‖ * ‖eulerFn T (fun _ => 1) z‖ ≤ (1 + |z.im|) * M1 :=
            mul_le_mul hz1n h (norm_nonneg _) (by positivity)
        _ ≤ (1 + |z.im|) ^ α * M1 := mul_le_mul_of_nonneg_right hup (zero_le_one.trans hM1)
        _ = M1 * (1 + |z.im|) ^ α := mul_comm _ _
        _ ≤ M₀ * (1 + |z.im|) ^ α := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact le_trans (by linarith) (le_max_right _ _)

  have hbig : ∀ z : ℂ, -1 / 2 ≤ z.re → z.re ≤ 5 / 2 → ‖Z z‖ ≤ C₄ * (1 + |z.im|) ^ α := by
    intro z hza hzb
    rcases le_or_gt z.re (3 / 2) with hle | hgt
    · calc ‖Z z‖ ≤ C₃ * M₀ * (1 + |z.im|) ^ α := hstrip z hza hle
        _ ≤ max C₃ 1 * M₀ * (1 + |z.im|) ^ α := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right hC₃C hM₀0
    · have hz1 : 1 < z.re := by linarith
      rw [hZeq z hz1, norm_mul]
      have h := norm_eulerFn_le T (fun _ => (1 : ℂ)) (fun _ => by rw [norm_one]) z hgt.le
      have hz1n : ‖z - 1‖ ≤ 2 * (1 + |z.im|) := by
        have hre : |(z - 1).re| ≤ 3 / 2 := by
          rw [sub_re, one_re]; exact abs_le.mpr ⟨by linarith, by linarith⟩
        calc ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| := norm_le_abs_re_add_abs_im _
          _ ≤ 3 / 2 + |z.im| := by rw [sub_im, one_im, sub_zero]; linarith
          _ ≤ 2 * (1 + |z.im|) := by linarith [abs_nonneg z.im]
      have hup : (1 + |z.im|) ≤ (1 + |z.im|) ^ α := by
        calc (1 + |z.im|) = (1 + |z.im|) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (1 + |z.im|) ^ α := Real.rpow_le_rpow_of_exponent_le (h1t z.im) hα1
      calc ‖z - 1‖ * ‖eulerFn T (fun _ => 1) z‖ ≤ (2 * (1 + |z.im|)) * M1 :=
            mul_le_mul hz1n h (norm_nonneg _) (by positivity)
        _ ≤ (2 * (1 + |z.im|) ^ α) * M1 := by
            apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hM1)
            exact mul_le_mul_of_nonneg_left hup (by norm_num)
        _ = (2 * M1) * (1 + |z.im|) ^ α := by ring
        _ ≤ M₀ * (1 + |z.im|) ^ α := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        _ ≤ C₄ * (1 + |z.im|) ^ α := mul_le_mul_of_nonneg_right hM₀C₄ (by positivity)

  have hVopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have h2mem : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
    show (1 : ℝ) < (2 : ℂ).re
    norm_num
  have hev : Z' =ᶠ[𝓝 (2 : ℂ)] Z := by
    refine Filter.eventuallyEq_of_mem (hVopen.mem_nhds h2mem) fun z hz => ?_
    rw [hZ'eq z hz, hZeq z hz]
    simp only [eulerFn, one_mul]
  have hEq : Set.EqOn Z' Z Set.univ :=
    (analyticOnNhd_univ_iff_differentiable.mpr hZ'd).eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_univ_iff_differentiable.mpr hZd) isPreconnected_univ (Set.mem_univ _) hev
  rw [hEq (Set.mem_univ s)]
  refine (hbig s hsa hsb).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hC₄0.le
  exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg s.im]) hα0.le

end main

end R4LDCZstrip

end

open NumberField IsDedekindDomain in
theorem solution
    (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ (Z : ℂ → ℂ), Differentiable ℂ Z →
        (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) →
      ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 5 / 2 → ‖Z s‖ ≤ C * (2 + |s.im|) ^ A :=
  R4LDCZstrip.main T

end S_NumberField_TateGlobal_exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc (solution)
