-- Prove2me | solution 1 for NumberField.TateGlobal.exists_pos_forall_sub_one_mul_partialDedekindZeta_continuation_ne_zero_of_one_sub_div_log_le_re
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/98b34fb5-22a3-5c9a-81af-6304afd4ad8e

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_Complex_div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg
import Theorems.Thm_EulerProduct_differentiableAt_and_ne_zero_and_hasSum_log_mul_div_neg_deriv_tprod_div
import Theorems.Thm_EulerProduct_three_mul_re_neg_deriv_tprod_div_add_four_mul_add_nonneg_of_norm_le_one
import Theorems.Thm_NumberField_TateGlobal_exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Theorems.Thm_NumberField_exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero
import Theorems.Thm_NumberField_hasProd_inv_one_sub_absNorm_cpow_neg_dedekindZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_pos_forall_sub_one_mul_partialDedekindZeta_continuation_ne_zero_of_one_sub_div_log_le_re

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Complex Filter Set
open scoped Topology

namespace R4ZR

theorem two_le_absNorm {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

section eulerAbstract

theorem norm_tprod_inv_one_sub_eq_exp {ι : Type} (a : ι → ℂ) (ha : Summable fun i => ‖a i‖)
    (ha1 : ∀ i, ‖a i‖ < 1) :
    ‖∏' i, (1 - a i)⁻¹‖ = Real.exp (∑' i, (-log (1 - a i)).re) := by
  have hne : ∀ i, 1 - a i ≠ 0 := fun i h => by
    have : a i = 1 := (sub_eq_zero.mp h).symm
    have := ha1 i
    rw [‹a i = 1›, norm_one] at this
    exact lt_irrefl _ this
  have hsum : Summable fun i => -log (1 - a i) := ha.of_norm.clog_one_sub.neg
  have H := hsum.hasSum.cexp.tprod_eq
  have hcongr : (cexp ∘ fun i => -log (1 - a i)) = fun i => (1 - a i)⁻¹ := by
    funext i
    simp only [Function.comp_apply, exp_neg, exp_log (hne i)]
  rw [hcongr] at H
  rw [H, norm_exp, re_tsum hsum]

theorem norm_neg_log_one_sub_le {a : ℂ} (ha : ‖a‖ ≤ 1 / 2) : ‖-log (1 - a)‖ ≤ 2 * ‖a‖ := by
  rw [norm_neg, sub_eq_add_neg]
  have h := Complex.norm_log_one_add_half_le_self (z := -a) (by rwa [norm_neg])
  rw [norm_neg] at h
  linarith [norm_nonneg a]

theorem norm_natCast_cpow_neg (n : ℕ) (hn : 0 < n) (s : ℂ) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  rw [norm_natCast_cpow_of_pos hn]; simp

theorem rpow_neg_le_half {N : ℕ} (hN : 2 ≤ N) {σ : ℝ} (hσ : 1 ≤ σ) : ((N : ℕ) : ℝ) ^ (-σ) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rw [Real.rpow_neg (Nat.cast_nonneg _)]
  have h1 : (2 : ℝ) ≤ ((N : ℕ) : ℝ) ^ σ := by
    calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ 2 ^ σ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ
      _ ≤ ((N : ℕ) : ℝ) ^ σ := Real.rpow_le_rpow (by norm_num) h2 (by linarith)
  rw [one_div]
  exact inv_anti₀ (by norm_num) h1

theorem exp_neg_le_norm_tprod {ι : Type} (N : ι → ℕ) (hN : ∀ i, 2 ≤ N i) (c : ι → ℂ) (hc : ∀ i, ‖c i‖ ≤ 1)
    (s : ℂ) (hs : 1 ≤ s.re) (hsum : Summable fun i => ((N i : ℕ) : ℝ) ^ (-s.re)) :
    Real.exp (-(2 * ∑' i, ((N i : ℕ) : ℝ) ^ (-s.re))) ≤ ‖∏' i, (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹‖ := by
  have hN0 : ∀ i, 0 < N i := fun i => by have := hN i; omega
  set a : ι → ℂ := fun i => c i * ((N i : ℕ) : ℂ) ^ (-s) with ha_def
  have ha_le : ∀ i, ‖a i‖ ≤ ((N i : ℕ) : ℝ) ^ (-s.re) := fun i => by
    show ‖c i * ((N i : ℕ) : ℂ) ^ (-s)‖ ≤ _
    rw [norm_mul, norm_natCast_cpow_neg _ (hN0 i)]
    calc ‖c i‖ * ((N i : ℕ) : ℝ) ^ (-s.re) ≤ 1 * ((N i : ℕ) : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (hc i) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := one_mul _
  have ha_half : ∀ i, ‖a i‖ ≤ 1 / 2 := fun i => (ha_le i).trans (rpow_neg_le_half (hN i) hs)
  have ha_lt : ∀ i, ‖a i‖ < 1 := fun i => (ha_half i).trans_lt (by norm_num)
  have ha_sum : Summable fun i => ‖a i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) ha_le hsum
  rw [show (fun i => (1 - c i * ((N i : ℕ) : ℂ) ^ (-s))⁻¹) = fun i => (1 - a i)⁻¹ from rfl,
    norm_tprod_inv_one_sub_eq_exp a ha_sum ha_lt, Real.exp_le_exp]
  have hlog_le : ∀ i, ‖-log (1 - a i)‖ ≤ 2 * ((N i : ℕ) : ℝ) ^ (-s.re) := fun i =>
    (norm_neg_log_one_sub_le (ha_half i)).trans (by linarith [ha_le i])
  have hlog_sum : Summable fun i => ‖-log (1 - a i)‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hlog_le (hsum.mul_left 2)
  have hre_sum : Summable fun i => (-log (1 - a i)).re :=
    (hlog_sum.of_norm).mapL Complex.reCLM
  have hneg : ∀ i, -(2 * ((N i : ℕ) : ℝ) ^ (-s.re)) ≤ (-log (1 - a i)).re := fun i => by
    have h1 := abs_re_le_norm (-log (1 - a i))
    have h2 := hlog_le i
    have := neg_le_of_abs_le h1
    linarith
  calc -(2 * ∑' i, ((N i : ℕ) : ℝ) ^ (-s.re)) = ∑' i, -(2 * ((N i : ℕ) : ℝ) ^ (-s.re)) := by
        rw [tsum_neg, tsum_mul_left]
    _ ≤ ∑' i, (-log (1 - a i)).re :=
        Summable.tsum_le_tsum hneg (hsum.mul_left 2).neg hre_sum

theorem tsum_rpow_neg_le_log_norm_tprod {ι : Type} (N : ι → ℕ) (hN : ∀ i, 2 ≤ N i)
    (σ : ℝ) (hσ : 1 ≤ σ) (hsum : Summable fun i => ((N i : ℕ) : ℝ) ^ (-σ)) :
    ∑' i, ((N i : ℕ) : ℝ) ^ (-σ) ≤ Real.log ‖∏' i, (1 - ((N i : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹‖ := by
  have hN0 : ∀ i, 0 < N i := fun i => by have := hN i; omega
  set a : ι → ℂ := fun i => ((N i : ℕ) : ℂ) ^ (-(σ : ℂ)) with ha_def
  have ha_real : ∀ i, a i = ((((N i : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) := fun i => by
    show ((N i : ℕ) : ℂ) ^ (-(σ : ℂ)) = _
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast, ofReal_neg]
  have ha_norm : ∀ i, ‖a i‖ = ((N i : ℕ) : ℝ) ^ (-σ) := fun i => by
    rw [ha_real i, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have ha_half : ∀ i, ‖a i‖ ≤ 1 / 2 := fun i => by rw [ha_norm]; exact rpow_neg_le_half (hN i) hσ
  have ha_lt : ∀ i, ‖a i‖ < 1 := fun i => (ha_half i).trans_lt (by norm_num)
  have ha_sum : Summable fun i => ‖a i‖ := hsum.congr fun i => (ha_norm i).symm
  rw [show (fun i => (1 - ((N i : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹) = fun i => (1 - a i)⁻¹ from rfl,
    norm_tprod_inv_one_sub_eq_exp a ha_sum ha_lt, Real.log_exp]

  have hterm : ∀ i, ((N i : ℕ) : ℝ) ^ (-σ) ≤ (-log (1 - a i)).re := fun i => by
    set x : ℝ := ((N i : ℕ) : ℝ) ^ (-σ) with hx
    have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hx1 : x ≤ 1 / 2 := rpow_neg_le_half (hN i) hσ
    have h1 : 1 - a i = (((1 - x : ℝ)) : ℂ) := by rw [ha_real i]; push_cast; rfl
    rw [h1, neg_re, log_ofReal_re]
    have h2 : Real.log (1 - x) ≤ (1 - x) - 1 := Real.log_le_sub_one_of_pos (by linarith)
    linarith
  have hlog_le : ∀ i, ‖-log (1 - a i)‖ ≤ 2 * ((N i : ℕ) : ℝ) ^ (-σ) := fun i =>
    (norm_neg_log_one_sub_le (ha_half i)).trans (by rw [ha_norm])
  have hlog_sum : Summable fun i => ‖-log (1 - a i)‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hlog_le (hsum.mul_left 2)
  have hre_sum : Summable fun i => (-log (1 - a i)).re :=
    (hlog_sum.of_norm).mapL Complex.reCLM
  exact Summable.tsum_le_tsum hterm hsum hre_sum

end eulerAbstract

section zeta
variable {K : Type} [Field K] [NumberField K]

def nC (v : HeightOneSpectrum (𝓞 K)) : ℂ := ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)

theorem nC_pos (v : HeightOneSpectrum (𝓞 K)) : 0 < Ideal.absNorm v.asIdeal :=
  lt_of_lt_of_le (by norm_num) (two_le_absNorm v)

theorem norm_nC_cpow_neg (v : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    ‖nC v ^ (-s)‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) := by
  unfold nC
  rw [Complex.norm_natCast_cpow_of_pos (nC_pos v) (-s), Complex.neg_re]

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

def eulerFn (T : Finset (HeightOneSpectrum (𝓞 K))) (c : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
    (1 - c v.1 * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹

def corr (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) : ℂ := ∏ v ∈ T, (1 - nC v ^ (-s))

theorem differentiable_corr (T : Finset (HeightOneSpectrum (𝓞 K))) : Differentiable ℂ (corr (K := K) T) := by
  unfold corr
  refine Differentiable.fun_finsetProd fun v _ => ?_
  refine (differentiable_const _).sub ?_
  refine Differentiable.const_cpow differentiable_neg (Or.inl ?_)
  unfold nC
  exact_mod_cast (nC_pos v).ne'

theorem corr_ne_zero (T : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 0 < s.re) : corr T s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun v _ => one_sub_ne_zero hs v

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
  have hne : corr T s ≠ 0 := corr_ne_zero T hs0
  have hinv : (∏ v ∈ T, (1 - nC v ^ (-s))⁻¹) = (corr T s)⁻¹ := by
    unfold corr; exact Finset.prod_inv_distrib _
  rw [hinv] at heq
  rw [hEq]
  calc E = corr T s * ((corr T s)⁻¹ * E) := by rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ = corr T s * dedekindZeta K s := by rw [heq]
    _ = dedekindZeta K s * corr T s := mul_comm _ _

theorem exists_Z (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 ≠ 0 ∧
      ∀ s : ℂ, 1 < s.re → Z s = (s - 1) * eulerFn T (fun _ => 1) s := by
  obtain ⟨R, hRd, hR1, hReq, -⟩ :=
    NumberField.exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero K
  refine ⟨fun s => R s * corr T s, hRd.mul (differentiable_corr T), ?_, fun s hs => ?_⟩
  · show R 1 * corr T 1 ≠ 0
    exact mul_ne_zero hR1 (corr_ne_zero T (by simp))
  · show R s * corr T s = (s - 1) * eulerFn T (fun _ => 1) s
    rw [hReq s hs, eulerFn_one_eq hs T, mul_assoc]

end zeta

section zetaTools
variable {K : Type} [Field K] [NumberField K]

theorem summable_subtype_rpow (T : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} =>
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-σ) :=
  (NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K hσ).subtype _

theorem differentiableAt_and_ne_zero (T : Finset (HeightOneSpectrum (𝓞 K)))
    (c : HeightOneSpectrum (𝓞 K) → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - c v.1 * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹) s ∧
      (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - c v.1 * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) ≠ 0 := by
  have h := EulerProduct.differentiableAt_and_ne_zero_and_hasSum_log_mul_div_neg_deriv_tprod_div
    (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => Ideal.absNorm v.1.asIdeal)
    (fun v => two_le_absNorm v.1) (fun v => c v.1) (fun v => hc v.1)
    (fun σ hσ => summable_subtype_rpow T hσ) s hs
  exact ⟨h.1, h.2.1⟩

theorem differentiableAt_and_ne_zero_one (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℂ) (hs : 1 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹) s ∧
      (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) ≠ 0 := by
  have h := differentiableAt_and_ne_zero T (fun _ => 1) (fun _ => by rw [norm_one]) s hs
  simp only [one_mul] at h
  exact h

theorem exists_C₀ (T : Finset (HeightOneSpectrum (𝓞 K))) (Z : ℂ → ℂ) (hZd : Differentiable ℂ Z)
    (hZ1 : Z 1 ≠ 0)
    (hZeq : ∀ s : ℂ, 1 < s.re → Z s = (s - 1) * ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      -(deriv (fun z : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹) (σ : ℂ) /
          ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ))))⁻¹).re ≤ 1 / (σ - 1) + C₀ := by
  set E₀ : ℂ → ℂ := fun z : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
      (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹ with hE₀

  set S : Set ℂ := (fun σ : ℝ => (σ : ℂ)) '' Set.Icc (1 : ℝ) 2 with hS
  have hScomp : IsCompact S := (isCompact_Icc).image continuous_ofReal
  have hZne : ∀ z ∈ S, Z z ≠ 0 := by
    rintro z ⟨σ, hσ, rfl⟩
    rcases eq_or_lt_of_le hσ.1 with h | h
    · rw [← h]; simpa using hZ1
    · rw [hZeq _ (by simpa using h)]
      refine mul_ne_zero ?_ (differentiableAt_and_ne_zero_one T _ (by simpa using h)).2
      rw [sub_ne_zero]
      intro h1
      have := congrArg Complex.re h1
      simp at this
      linarith
  have hcontZ : Continuous Z := hZd.continuous
  have hcontZ' : Continuous (deriv Z) :=
    (analyticOnNhd_univ_iff_differentiable.mpr hZd).deriv.continuousOn.comp_continuous continuous_id
      (fun _ => Set.mem_univ _) |>.congr (fun _ => rfl)
  have hg : ContinuousOn (fun z => deriv Z z / Z z) S :=
    (hcontZ'.continuousOn.div hcontZ.continuousOn hZne)
  obtain ⟨C₀', hC₀'⟩ := hScomp.exists_bound_of_continuousOn hg
  refine ⟨max C₀' 0, le_max_right _ _, fun σ hσ hσ2 => ?_⟩
  have hσS : (σ : ℂ) ∈ S := ⟨σ, ⟨hσ.le, hσ2⟩, rfl⟩
  have hZσ : Z σ ≠ 0 := hZne _ hσS
  have hσ1 : (σ : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := congrArg Complex.re h; simp at this; linarith

  have hVopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const continuous_re
  have hσV : (σ : ℂ) ∈ {s : ℂ | 1 < s.re} := by simpa using hσ
  have hev : E₀ =ᶠ[𝓝 (σ : ℂ)] fun s => Z s / (s - 1) := by
    refine Filter.eventuallyEq_of_mem (hVopen.mem_nhds hσV) fun z hz => ?_
    have hz1 : z - 1 ≠ 0 := by
      rw [sub_ne_zero]; intro h; rw [h] at hz; simp at hz
    show E₀ z = Z z / (z - 1)
    rw [hZeq z hz, hE₀]
    field_simp
  have hderivE₀ : deriv E₀ (σ : ℂ) = (deriv Z σ * ((σ : ℂ) - 1) - Z σ * 1) / ((σ : ℂ) - 1) ^ 2 := by
    rw [hev.deriv_eq]
    have hZ' : HasDerivAt Z (deriv Z σ) (σ : ℂ) := hZd.differentiableAt.hasDerivAt
    have hd : HasDerivAt (fun s : ℂ => s - 1) 1 (σ : ℂ) := (hasDerivAt_id _).sub_const 1
    exact (hZ'.div hd hσ1).deriv
  have hE₀σ : E₀ (σ : ℂ) = Z σ / ((σ : ℂ) - 1) := hev.eq_of_nhds
  have hratio : deriv E₀ (σ : ℂ) / E₀ (σ : ℂ) = deriv Z σ / Z σ - 1 / ((σ : ℂ) - 1) := by
    rw [hderivE₀, hE₀σ]
    field_simp
  show -(deriv E₀ (σ : ℂ) / E₀ (σ : ℂ)).re ≤ 1 / (σ - 1) + max C₀' 0
  rw [hratio, sub_re, neg_sub]
  have h1 : (1 / ((σ : ℂ) - 1)).re = 1 / (σ - 1) := by
    rw [← ofReal_one, ← ofReal_sub, ← ofReal_div, ofReal_re]
  rw [h1]
  have h2 : -(deriv Z σ / Z σ).re ≤ ‖deriv Z σ / Z σ‖ := by
    have := abs_re_le_norm (deriv Z σ / Z σ)
    have := neg_le_of_abs_le this
    linarith
  have h3 : ‖deriv Z σ / Z σ‖ ≤ max C₀' 0 := (hC₀' _ hσS).trans (le_max_left _ _)
  linarith

theorem sq_le_norm_tprod (T : Finset (HeightOneSpectrum (𝓞 K)))
    (c : HeightOneSpectrum (𝓞 K) → ℂ) (hc : ∀ v, ‖c v‖ ≤ 1)
    (Z : ℂ → ℂ)
    (hZeq : ∀ s : ℂ, 1 < s.re → Z s = (s - 1) * ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
    (C : ℝ) (hC1 : 1 ≤ C) (hZle : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖Z σ‖ ≤ C)
    (σ t : ℝ) (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    ((σ - 1) / C) ^ 2 ≤ ‖∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - c v.1 * (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-((σ : ℂ) + t * I))))⁻¹‖ := by
  have hsumσ := summable_subtype_rpow (K := K) T hσ
  have hre : ((σ : ℂ) + t * I).re = σ := by simp

  have hlow := exp_neg_le_norm_tprod
    (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => Ideal.absNorm v.1.asIdeal)
    (fun v => two_le_absNorm v.1) (fun v => c v.1) (fun v => hc v.1) ((σ : ℂ) + t * I)
    (by rw [hre]; exact hσ.le) (by rw [hre]; exact hsumσ)
  rw [hre] at hlow
  refine le_trans ?_ hlow

  have hzeta := tsum_rpow_neg_le_log_norm_tprod
    (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => Ideal.absNorm v.1.asIdeal)
    (fun v => two_le_absNorm v.1) σ hσ.le hsumσ
  set E₀σ : ℂ := ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
      (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ))))⁻¹ with hE₀σ
  have hσ1 : (σ : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]; intro h; have := congrArg Complex.re h; simp at this; linarith
  have hE₀eq : E₀σ = Z σ / ((σ : ℂ) - 1) := by
    rw [hZeq _ (by simpa using hσ), mul_div_cancel_left₀ _ hσ1]
  have hnormσ1 : ‖(σ : ℂ) - 1‖ = σ - 1 := by
    rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hE₀norm : ‖E₀σ‖ ≤ C / (σ - 1) := by
    rw [hE₀eq, norm_div, hnormσ1]
    exact div_le_div_of_nonneg_right (hZle σ hσ hσ2) (by linarith)
  have hE₀pos : 0 < ‖E₀σ‖ := by
    have h := (differentiableAt_and_ne_zero_one T (σ : ℂ) (by simpa using hσ)).2
    exact norm_pos_iff.mpr h
  have hCσ : 0 < C / (σ - 1) := by positivity
  have hlog : Real.log ‖E₀σ‖ ≤ Real.log (C / (σ - 1)) := Real.log_le_log hE₀pos hE₀norm
  have hS : ∑' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T}, ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-σ)
      ≤ Real.log (C / (σ - 1)) := hzeta.trans hlog

  have hexp : ((σ - 1) / C) ^ 2 = Real.exp (-(2 * Real.log (C / (σ - 1)))) := by
    rw [show -(2 * Real.log (C / (σ - 1))) = (2 : ℕ) * (-Real.log (C / (σ - 1))) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_neg, Real.exp_log hCσ, inv_div]
  rw [hexp, Real.exp_le_exp]
  linarith

end zetaTools

section threefourone
variable {K : Type} [Field K] [NumberField K]

theorem three_four_one_one (T : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ) (hσ : 1 < σ) (t : ℝ)
    (F₁ F₂ : ℂ → ℂ)
    (h₁ : F₁ =ᶠ[𝓝 ((σ : ℂ) + t * I)] fun z : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹)
    (h₂ : F₂ =ᶠ[𝓝 ((σ : ℂ) + 2 * t * I)] fun z : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹) :
    0 ≤ 3 * (-(deriv (fun z : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
              (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹) (σ : ℂ) /
            ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
              (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(σ : ℂ))))⁻¹)).re
      + 4 * (-(deriv F₁ ((σ : ℂ) + t * I) / F₁ ((σ : ℂ) + t * I))).re
      + (-(deriv F₂ ((σ : ℂ) + 2 * t * I) / F₂ ((σ : ℂ) + 2 * t * I))).re := by
  have hsum : ∀ σ' : ℝ, 1 < σ' → Summable fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} =>
      ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ (-σ') := fun σ' hσ' =>
    (NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt K hσ').subtype _
  have h := EulerProduct.three_mul_re_neg_deriv_tprod_div_add_four_mul_add_nonneg_of_norm_le_one
    (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T} => Ideal.absNorm v.1.asIdeal)
    (fun v => two_le_absNorm v.1) (fun _ => (1 : ℂ)) (fun _ => (1 : ℂ))
    (fun _ => by rw [norm_one]) (fun _ => by rw [norm_one]) (fun _ => Or.inr (by rw [one_pow])) hsum σ t hσ
  simp only [one_mul] at h
  rw [h₁.deriv_eq, h₁.eq_of_nhds, h₂.deriv_eq, h₂.eq_of_nhds]
  exact h

end threefourone

section main
variable (K : Type) [Field K] [NumberField K]

theorem re_ofReal_add_mul_I (σ t : ℝ) : ((σ : ℂ) + t * I).re = σ := by simp

theorem disc_bounds {σ u r : ℝ} {z : ℂ} (hz : z ∈ Metric.closedBall ((σ : ℂ) + u * I) r) :
    |z.re - σ| ≤ r ∧ |z.im - u| ≤ r := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have hre := abs_re_le_norm (z - ((σ : ℂ) + u * I))
  have him := abs_im_le_norm (z - ((σ : ℂ) + u * I))
  simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, sub_im, add_im, mul_im, zero_add] at hre him
  exact ⟨hre.trans hz, him.trans hz⟩

set_option maxHeartbeats 24000000 in
theorem main (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Z : ℂ → ℂ), Differentiable ℂ Z →
        (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) →
      ∀ s : ℂ, 1 - c / Real.log (2 + |s.im|) ≤ s.re → Z s ≠ 0 := by

  obtain ⟨CZ, AZ, hCZ, hAZ, hZs⟩ :=
    NumberField.TateGlobal.exists_forall_norm_sub_one_mul_partialDedekindZeta_continuation_le_rpow_of_re_mem_Icc K T
  obtain ⟨Z₀, hZ₀d, hZ₀1, hZ₀eq'⟩ := exists_Z (K := K) T
  have hZ₀eq : ∀ s : ℂ, 1 < s.re → Z₀ s = (s - 1) * ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
      (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
    intro s hs; rw [hZ₀eq' s hs]; simp only [eulerFn, one_mul]
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_C₀ T Z₀ hZ₀d hZ₀1 hZ₀eq
  set CZ' : ℝ := max (CZ * (2 : ℝ) ^ AZ) 1 with hCZ'def
  have hCZ'1 : 1 ≤ CZ' := le_max_right _ _
  have hZle : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖Z₀ σ‖ ≤ CZ' := by
    intro σ hσ hσ2
    have h := hZs Z₀ hZ₀d hZ₀eq σ (by rw [ofReal_re]; linarith) (by rw [ofReal_re]; linarith)
    rw [ofReal_im, abs_zero, add_zero] at h
    exact h.trans (le_max_left _ _)

  obtain ⟨δ₁, hδ₁0, hδ₁half, hpole⟩ : ∃ δ₁ : ℝ, 0 < δ₁ ∧ δ₁ ≤ 1 / 2 ∧ ∀ z : ℂ, ‖z - 1‖ ≤ δ₁ → Z₀ z ≠ 0 := by
    have hc : ContinuousAt Z₀ 1 := hZ₀d.continuous.continuousAt
    have hε : 0 < ‖Z₀ 1‖ / 2 := by positivity
    obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousAt_iff.mp hc _ hε
    refine ⟨min (δ / 2) (1 / 2), lt_min (by linarith) (by norm_num), min_le_right _ _, fun z hz h0 => ?_⟩
    have hz' : dist z 1 < δ := by
      rw [dist_eq_norm]; exact lt_of_le_of_lt (hz.trans (min_le_left _ _)) (by linarith)
    have h := hδ hz'
    rw [h0, dist_eq_norm, zero_sub, norm_neg] at h
    linarith [norm_nonneg (Z₀ 1)]

  set r : ℝ := min (1 / 2) (δ₁ / 8) with hrdef
  have hr0 : 0 < r := lt_min (by norm_num) (by linarith)
  have hrhalf : r ≤ 1 / 2 := min_le_left _ _
  have hrδ : r ≤ δ₁ / 8 := min_le_right _ _
  have hr1 : r ≤ 1 := by linarith
  set Cbig : ℝ := max (max (max (max (8 * CZ / (3 * δ₁)) (CZ' ^ 2)) (Real.exp C₀)) (Real.exp (1 / r))) 1
    with hCbigdef
  have hCbig1 : 1 ≤ Cbig := le_max_right _ _
  have hCbig0 : 0 < Cbig := one_pos.trans_le hCbig1
  have h8CZ_le : 8 * CZ / (3 * δ₁) ≤ Cbig :=
    (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hCZ'2_le : CZ' ^ 2 ≤ Cbig :=
    (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hexpC₀ : Real.exp C₀ ≤ Cbig := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hexpr : Real.exp (1 / r) ≤ Cbig := (le_max_right _ _).trans (le_max_left _ _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogCbig : 0 ≤ Real.log Cbig := Real.log_nonneg hCbig1
  set D : ℝ := Real.log Cbig / Real.log 2 + AZ * (Real.log 3 / Real.log 2 + 1) with hDdef
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hD0 : 0 < D := by
    have h1 : 0 ≤ Real.log Cbig / Real.log 2 := by positivity
    have h2 : 0 < AZ * (Real.log 3 / Real.log 2 + 1) := by positivity
    linarith
  refine ⟨min (r / (40000 * D)) (δ₁ / 4), lt_min (by positivity) (by linarith), ?_⟩
  intro Z hZd hZeq s hs hZs0

  have hZZ : Z = Z₀ := by
    have hVopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    have hev : Z =ᶠ[𝓝 (2 : ℂ)] Z₀ :=
      Filter.eventuallyEq_of_mem (hVopen.mem_nhds (by show (1 : ℝ) < (2 : ℂ).re; norm_num)) fun z hz => by
        show Z z = Z₀ z; rw [hZeq z hz, hZ₀eq z hz]
    have h := (analyticOnNhd_univ_iff_differentiable.mpr hZd).eqOn_of_preconnected_of_eventuallyEq
      (analyticOnNhd_univ_iff_differentiable.mpr hZ₀d) isPreconnected_univ (Set.mem_univ _) hev
    exact funext fun z => h (Set.mem_univ z)
  subst hZZ

  set β : ℝ := s.re with hβdef
  set γ : ℝ := s.im with hγdef
  set 𝔮 : ℝ := 2 + |γ| with h𝔮def
  have h𝔮2 : 2 ≤ 𝔮 := by rw [h𝔮def]; linarith [abs_nonneg γ]
  have h𝔮0 : 0 < 𝔮 := by linarith
  have hlog𝔮2 : Real.log 2 ≤ Real.log 𝔮 := Real.log_le_log (by norm_num) h𝔮2
  have hlog𝔮0 : 0 < Real.log 𝔮 := hlog2.trans_le hlog𝔮2
  have hsβγ : s = (β : ℂ) + γ * I := (re_add_im s).symm
  have hcmin1 : min (r / (40000 * D)) (δ₁ / 4) ≤ r / (40000 * D) := min_le_left _ _
  have hcmin2 : min (r / (40000 * D)) (δ₁ / 4) ≤ δ₁ / 4 := min_le_right _ _

  have hE₀nz : ∀ z : ℂ, 1 < z.re → (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
      (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹) ≠ 0 :=
    fun z hz => (differentiableAt_and_ne_zero_one T z hz).2
  have hZnz : ∀ z : ℂ, 1 < z.re → Z z ≠ 0 := by
    intro z hz
    rw [hZeq z hz]
    refine mul_ne_zero ?_ (hE₀nz z hz)
    rw [sub_ne_zero]; intro h; rw [h] at hz; simp at hz
  have hβ1 : β ≤ 1 := by
    by_contra h
    push Not at h
    exact hZnz s h hZs0
  have h1β : 1 - β ≤ min (r / (40000 * D)) (δ₁ / 4) / Real.log 𝔮 := by
    have := hs; rw [sub_le_comm] at this; exact this

  by_cases hγ : |γ| < δ₁ / 2
  · have h1 : 1 - β ≤ δ₁ / 2 := by
      have h2 : min (r / (40000 * D)) (δ₁ / 4) / Real.log 𝔮 ≤ (δ₁ / 4) / Real.log 2 :=
        div_le_div₀ (by linarith) hcmin2 hlog2 hlog𝔮2
      have h3 : (δ₁ / 4) / Real.log 2 ≤ δ₁ / 2 := by
        rw [div_le_iff₀ hlog2]
        have := Real.log_two_gt_d9
        nlinarith
      linarith
    refine hpole s ?_ hZs0
    rw [hsβγ]
    have hre : (((β : ℂ) + γ * I) - 1) = (((β - 1 : ℝ) : ℂ) + ((γ : ℝ) : ℂ) * I) := by push_cast; ring
    rw [hre]
    calc ‖(((β - 1 : ℝ) : ℂ) + ((γ : ℝ) : ℂ) * I)‖ ≤ ‖((β - 1 : ℝ) : ℂ)‖ + ‖((γ : ℝ) : ℂ) * I‖ := norm_add_le _ _
      _ = |β - 1| + |γ| := by
          rw [norm_mul, norm_I, mul_one, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ δ₁ / 2 + δ₁ / 2 := by
          have : |β - 1| = 1 - β := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
          rw [this]; linarith [hγ.le]
      _ = δ₁ := by ring
  · push Not at hγ

    set 𝓛 : ℝ := Real.log Cbig + AZ * Real.log (3 * 𝔮) with h𝓛def
    have h3𝔮 : 1 ≤ 3 * 𝔮 := by linarith
    have h3𝔮0 : 0 < 3 * 𝔮 := by linarith
    have hexp𝓛 : Real.exp 𝓛 = Cbig * (3 * 𝔮) ^ AZ := by
      rw [h𝓛def, Real.exp_add, Real.exp_log hCbig0, Real.rpow_def_of_pos h3𝔮0, mul_comm (Real.log _)]
    have hlog3𝔮 : 0 ≤ Real.log (3 * 𝔮) := Real.log_nonneg h3𝔮
    have h𝓛log : Real.log Cbig ≤ 𝓛 := by rw [h𝓛def]; nlinarith
    have h𝓛C₀ : C₀ ≤ 𝓛 := ((Real.le_log_iff_exp_le hCbig0).mpr hexpC₀).trans h𝓛log
    have hr𝓛 : 1 ≤ r * 𝓛 := by
      have h1 : 1 / r ≤ Real.log Cbig := (Real.le_log_iff_exp_le hCbig0).mpr hexpr
      have h2 : 1 ≤ r * Real.log Cbig := by rw [div_le_iff₀ hr0] at h1; linarith
      nlinarith
    have h𝓛0 : 0 < 𝓛 := by nlinarith
    have h𝓛D : 𝓛 ≤ D * Real.log 𝔮 := by
      rw [h𝓛def, hDdef, Real.log_mul (by norm_num) h𝔮0.ne']
      have h1 : Real.log Cbig ≤ Real.log Cbig / Real.log 2 * Real.log 𝔮 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
        exact mul_le_mul_of_nonneg_left hlog𝔮2 hlogCbig
      have h2 : Real.log 3 ≤ Real.log 3 / Real.log 2 * Real.log 𝔮 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
        exact mul_le_mul_of_nonneg_left hlog𝔮2 hlog3
      have h3 : AZ * (Real.log 3 + Real.log 𝔮) ≤ AZ * (Real.log 3 / Real.log 2 + 1) * Real.log 𝔮 := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hAZ.le
        nlinarith
      nlinarith

    have hlo_conv : ∀ σ : ℝ, (σ - 1) ^ 2 * Real.exp (-𝓛) ≤ ((σ - 1) / CZ') ^ 2 := by
      intro σ
      have h1 : CZ' ^ 2 ≤ Real.exp 𝓛 := by
        refine hCZ'2_le.trans ?_
        rw [hexp𝓛]
        exact le_mul_of_one_le_right hCbig0.le (Real.one_le_rpow h3𝔮 hAZ.le)
      rw [div_pow, Real.exp_neg, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h1) (sq_nonneg _)

    set G : ℂ → ℂ := fun z => Z z / (z - 1) with hGdef
    have hGE₀ : ∀ z : ℂ, 1 < z.re → G z = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
        (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹ := by
      intro z hz
      have hne : z - 1 ≠ 0 := by rw [sub_ne_zero]; intro h; rw [h] at hz; simp at hz
      show Z z / (z - 1) = _
      rw [hZeq z hz, mul_div_cancel_left₀ _ hne]
    have hGnz : ∀ z : ℂ, 1 < z.re → G z ≠ 0 := fun z hz => by rw [hGE₀ z hz]; exact hE₀nz z hz
    have hGev : ∀ (σ u : ℝ), 1 < σ →
        G =ᶠ[𝓝 ((σ : ℂ) + u * I)] fun z : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹ := by
      intro σ u hσ
      have hVopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
      exact Filter.eventuallyEq_of_mem (hVopen.mem_nhds (by show 1 < ((σ : ℂ) + u * I).re; simpa using hσ))
        fun z hz => hGE₀ z hz

    have hden : ∀ {σ u : ℝ} {z : ℂ}, δ₁ / 2 ≤ |u| → 1 < σ → σ ≤ 1 + r →
        z ∈ Metric.closedBall ((σ : ℂ) + u * I) r →
        3 * δ₁ / 8 ≤ ‖z - 1‖ ∧ -1 / 2 ≤ z.re ∧ z.re ≤ 5 / 2 ∧ |z.im| ≤ |u| + r := by
      intro σ u z hu hσ hσr hz
      obtain ⟨hre, him⟩ := disc_bounds hz
      have hre' := abs_le.mp hre
      have h1 : |(z - 1).im| ≤ ‖z - 1‖ := abs_im_le_norm _
      have h2 : (z - 1).im = z.im := by simp
      rw [h2] at h1
      have h3 : |u| - r ≤ |z.im| := by
        have := abs_sub_abs_le_abs_sub u z.im
        rw [abs_sub_comm] at him
        linarith
      refine ⟨by linarith, by linarith, by linarith, ?_⟩
      have := abs_sub_abs_le_abs_sub z.im u
      linarith
    have hGan : ∀ {σ u : ℝ}, δ₁ / 2 ≤ |u| → 1 < σ → σ ≤ 1 + r →
        AnalyticOnNhd ℂ G (Metric.closedBall ((σ : ℂ) + u * I) r) := by
      intro σ u hu hσ hσr
      have hUopen : IsOpen {z : ℂ | z - 1 ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
      have hGan' : AnalyticOnNhd ℂ G {z : ℂ | z - 1 ≠ 0} := by
        refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
        refine DifferentiableAt.differentiableWithinAt ?_
        show DifferentiableAt ℂ (fun z => Z z / (z - 1)) z
        exact (hZd.differentiableAt).div (differentiableAt_id.sub_const _) hz
      refine hGan'.mono fun z hz => ?_
      have h := (hden hu hσ hσr hz).1
      show z - 1 ≠ 0
      intro h0; rw [h0, norm_zero] at h; linarith
    have hGup : ∀ {σ u : ℝ}, δ₁ / 2 ≤ |u| → |u| ≤ 2 * |γ| → 1 < σ → σ ≤ 1 + r →
        ∀ z ∈ Metric.closedBall ((σ : ℂ) + u * I) r, ‖G z‖ ≤ Real.exp 𝓛 := by
      intro σ u hu hu2 hσ hσr z hz
      obtain ⟨hd, hz1, hz2, him⟩ := hden hu hσ hσr hz
      have hZb := hZs Z hZd hZeq z hz1 hz2
      have hnormG : ‖G z‖ = ‖Z z‖ / ‖z - 1‖ := by
        show ‖Z z / (z - 1)‖ = _; rw [norm_div]
      rw [hnormG, div_le_iff₀ (by linarith)]
      have hx : 2 + |z.im| ≤ 3 * 𝔮 := by rw [h𝔮def]; linarith [abs_nonneg γ]
      have h1 : CZ * (2 + |z.im|) ^ AZ ≤ (8 * CZ / (3 * δ₁)) * (3 * 𝔮) ^ AZ * (3 * δ₁ / 8) := by
        have : (8 * CZ / (3 * δ₁)) * (3 * 𝔮) ^ AZ * (3 * δ₁ / 8) = CZ * (3 * 𝔮) ^ AZ := by
          field_simp
        rw [this]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hx hAZ.le) hCZ.le
      have h2 : (8 * CZ / (3 * δ₁)) * (3 * 𝔮) ^ AZ ≤ Real.exp 𝓛 := by
        rw [hexp𝓛]
        exact mul_le_mul_of_nonneg_right h8CZ_le (Real.rpow_nonneg (by linarith) _)
      calc ‖Z z‖ ≤ CZ * (2 + |z.im|) ^ AZ := hZb
        _ ≤ (8 * CZ / (3 * δ₁)) * (3 * 𝔮) ^ AZ * (3 * δ₁ / 8) := h1
        _ ≤ Real.exp 𝓛 * (3 * δ₁ / 8) := mul_le_mul_of_nonneg_right h2 (by linarith)
        _ ≤ Real.exp 𝓛 * ‖z - 1‖ := mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le
    have hGlo : ∀ (σ u : ℝ), 1 < σ → σ ≤ 1 + r →
        (σ - 1) ^ 2 * Real.exp (-𝓛) ≤ ‖G ((σ : ℂ) + u * I)‖ := by
      intro σ u hσ hσr
      refine (hlo_conv σ).trans ?_
      rw [hGE₀ _ (by rw [re_ofReal_add_mul_I]; exact hσ)]
      have h := sq_le_norm_tprod T (fun _ => (1 : ℂ)) (fun _ => by rw [norm_one]) Z hZeq CZ' hCZ'1 hZle σ u hσ
        (by linarith)
      simp only [one_mul] at h
      exact h

    have h341 : ∀ σ : ℝ, 1 < σ → σ ≤ 1 + r →
        0 ≤ 3 * (1 / (σ - 1) + C₀)
          + 4 * (-(deriv G ((σ : ℂ) + γ * I) / G ((σ : ℂ) + γ * I))).re
          + (-(deriv G ((σ : ℂ) + 2 * γ * I) / G ((σ : ℂ) + 2 * γ * I))).re := by
      intro σ hσ hσr
      have h2 : G =ᶠ[𝓝 ((σ : ℂ) + 2 * γ * I)] fun z : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-z)))⁻¹ := by
        have := hGev σ (2 * γ) hσ
        push_cast at this
        exact this
      have h := three_four_one_one T σ hσ γ G G (hGev σ γ hσ) h2
      have h0 := hC₀ σ hσ (by linarith)
      rw [← neg_re] at h0
      linarith

    have hγ2 : δ₁ / 2 ≤ |2 * γ| := by rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
    have hfin := Complex.div_le_one_sub_of_apply_eq_zero_of_norm_le_exp_of_three_four_one_nonneg
      G G β γ r 𝓛 C₀ hr0 hr1 hr𝓛 hC₀0 h𝓛C₀ ?_ hGnz hGnz
      (fun σ hσ hσr => hGan hγ hσ hσr)
      (fun σ hσ hσr => by
        have := hGan (u := 2 * γ) hγ2 hσ hσr
        push_cast at this
        exact this)
      (fun σ hσ hσr z hz => hGup hγ (by linarith [abs_nonneg γ]) hσ hσr z hz)
      (fun σ hσ hσr z hz => hGup (u := 2 * γ) hγ2
        (by rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]) hσ hσr z (by push_cast at hz ⊢; exact hz))
      (fun σ hσ hσr => hGlo σ γ hσ hσr)
      (fun σ hσ hσr => by have := hGlo σ (2 * γ) hσ hσr; push_cast at this; exact this)
      h341
    ·
      set X : ℝ := D * Real.log 𝔮 with hXdef
      have hX0 : 0 < X := by positivity
      have h1 : r / (20000 * X) ≤ r / (20000 * 𝓛) :=
        div_le_div_of_nonneg_left hr0.le (by positivity) (by nlinarith)
      have h3 : min (r / (40000 * D)) (δ₁ / 4) / Real.log 𝔮 ≤ r / (40000 * X) := by
        rw [hXdef]
        calc min (r / (40000 * D)) (δ₁ / 4) / Real.log 𝔮 ≤ r / (40000 * D) / Real.log 𝔮 :=
              div_le_div_of_nonneg_right hcmin1 hlog𝔮0.le
          _ = r / (40000 * (D * Real.log 𝔮)) := by rw [div_div]; ring_nf
      have h4 : r / (20000 * X) ≤ r / (40000 * X) := by linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)] at h4
      nlinarith
    ·
      have hs1 : s - 1 ≠ 0 := by
        intro h
        have : s.im = 0 := by rw [sub_eq_zero.mp h]; simp
        rw [← hγdef] at this
        rw [this, abs_zero] at hγ
        linarith
      show Z ((β : ℂ) + γ * I) / (((β : ℂ) + γ * I) - 1) = 0
      rw [← hsβγ, hZs0, zero_div]

end main

end R4ZR

end

open NumberField IsDedekindDomain in
theorem solution
    (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Z : ℂ → ℂ), Differentiable ℂ Z →
        (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
            (1 - (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) →
      ∀ s : ℂ, 1 - c / Real.log (2 + |s.im|) ≤ s.re → Z s ≠ 0 :=
  R4ZR.main K T

end S_NumberField_TateGlobal_exists_pos_forall_sub_one_mul_partialDedekindZeta_continuation_ne_zero_of_one_sub_div_log_le_re
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_pos_forall_sub_one_mul_partialDedekindZeta_continuation_ne_zero_of_one_sub_div_log_le_re (solution)
