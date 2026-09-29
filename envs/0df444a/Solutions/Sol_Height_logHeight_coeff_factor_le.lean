-- Prove2me | solution 1 for Height.logHeight_coeff_factor_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/dde502f8-6ce5-5459-a986-d9802efd8052

import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.RingTheory.Polynomial.GaussNorm
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Height_logHeight_coeff_factor_le

open Polynomial NumberField Height Function

section helpers

variable {K : Type*} [Field K]

private lemma mwfac_iSup_coeff_eq_gaussNorm (v : AbsoluteValue K ℝ) {n : ℕ}
    {f : Polynomial K} (hdeg : f.natDegree ≤ n) :
    (⨆ k : Fin (n + 1), v (f.coeff k)) = f.gaussNorm v 1 := by
  refine le_antisymm (ciSup_le fun k ↦ ?_) ?_
  · simpa using f.le_gaussNorm v zero_le_one k
  · obtain ⟨i, hi⟩ := f.exists_eq_gaussNorm v 1
    rcases le_or_gt i n with hin | hin
    · rw [hi]
      have := Finite.le_ciSup (fun k : Fin (n + 1) ↦ v (f.coeff ↑k)) ⟨i, Nat.lt_succ_of_le hin⟩
      simpa using this
    · rw [hi, coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg hin)]
      simpa using Real.iSup_nonneg_of_nonnegHomClass v fun k : Fin (n + 1) ↦ f.coeff ↑k

private lemma mwfac_nonarch_iSup_coeff_le {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean (⇑v)) {n : ℕ} {p q r : Polynomial K} (hq : q.Monic) (hr : r.Monic)
    (hpqr : p = q * r) (hdeg : p.natDegree ≤ n) :
    (⨆ k : Fin (n + 1), v (q.coeff k)) ≤ ⨆ k : Fin (n + 1), v (p.coeff k) := by
  have hp0 : p ≠ 0 := hpqr ▸ mul_ne_zero hq.ne_zero hr.ne_zero
  have hdq : q.natDegree ≤ n := (natDegree_le_of_dvd ⟨r, hpqr⟩ hp0).trans hdeg
  rw [mwfac_iSup_coeff_eq_gaussNorm v hdq, mwfac_iSup_coeff_eq_gaussNorm v hdeg,
    hpqr, Polynomial.gaussNorm_mul (hna := hv) (hc := one_pos) q r]
  have h1r : 1 ≤ r.gaussNorm v 1 := by
    have := r.le_gaussNorm v zero_le_one r.natDegree
    simpa [hr.coeff_natDegree] using this
  nth_rewrite 1 [← mul_one (q.gaussNorm v 1)]
  exact mul_le_mul_of_nonneg_left h1r (q.gaussNorm_nonneg v zero_le_one)

variable [NumberField K]

omit [NumberField K] in

private lemma mwfac_infinitePlace_iSup_coeff_le (w : InfinitePlace K) {n : ℕ}
    {p q r : Polynomial K} (hq : q.Monic) (hr : r.Monic)
    (hpqr : p = q * r) (hdeg : p.natDegree ≤ n) :
    (⨆ k : Fin (n + 1), w (q.coeff k)) ≤
      (2 ^ n * Real.sqrt (n + 1)) * ⨆ k : Fin (n + 1), w (p.coeff k) := by
  have hp0 : p ≠ 0 := hpqr ▸ mul_ne_zero hq.ne_zero hr.ne_zero
  set φ : K →+* ℂ := w.embedding with hφ
  have hP0 : p.map φ ≠ 0 := (Polynomial.map_eq_zero_iff φ.injective).not.mpr hp0
  have hPdeg : (p.map φ).natDegree ≤ n := by
    rw [natDegree_map_eq_of_injective φ.injective]; exact hdeg

  have hsup : (p.map φ).supNorm ≤ ⨆ k : Fin (n + 1), w (p.coeff k) := by
    rw [supNorm_def', dif_pos (support_nonempty.mpr hP0)]
    refine Finset.sup'_le _ _ fun i hi ↦ ?_
    have hin : i < n + 1 := Nat.lt_succ_of_le ((le_natDegree_of_mem_supp i hi).trans hPdeg)
    have hcoe : ‖(p.map φ).coeff i‖ = w (p.coeff i) := by
      rw [coeff_map, w.norm_embedding_eq]
    calc (norm ∘ (p.map φ).coeff) i = w (p.coeff i) := by
          simpa [Function.comp_apply] using hcoe
      _ ≤ ⨆ k : Fin (n + 1), w (p.coeff ↑k) :=
          Finite.le_ciSup (fun k : Fin (n + 1) ↦ w (p.coeff ↑k)) ⟨i, hin⟩
  refine ciSup_le fun k ↦ ?_

  have hMr : 1 ≤ (r.map φ).mahlerMeasure := by
    refine Polynomial.one_le_mahlerMeasure_of_one_le_norm_leadingCoeff ?_
    rw [(hr.map φ).leadingCoeff]
    simp
  have hmig := Polynomial.norm_coeff_le_choose_mul_mahlerMeasure_of_one_le_mahlerMeasure
    (k : ℕ) (q.map φ) (r.map φ) hMr
  rw [← Polynomial.map_mul, ← hpqr] at hmig
  have hcoeq : w (q.coeff k) = ‖(q.map φ).coeff (k : ℕ)‖ := by
    rw [coeff_map, w.norm_embedding_eq]

  have hchoose : ((q.map φ).natDegree.choose (k : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
    have h2 : (q.map φ).natDegree ≤ n := by
      rw [natDegree_map_eq_of_injective φ.injective]
      exact (natDegree_le_of_dvd ⟨r, hpqr⟩ hp0).trans hdeg
    have h1 : (q.map φ).natDegree.choose (k : ℕ) ≤ 2 ^ n :=
      (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) h2)
    exact_mod_cast h1

  have hml : (p.map φ).mahlerMeasure ≤ Real.sqrt (n + 1) * (p.map φ).supNorm := by
    refine (Polynomial.mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm _).trans ?_
    have hnn : ((p.map φ).natDegree : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ hPdeg
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hnn) (p.map φ).supNorm_nonneg
  calc w (q.coeff k) = ‖(q.map φ).coeff (k : ℕ)‖ := hcoeq
    _ ≤ ((q.map φ).natDegree.choose (k : ℕ) : ℝ) * (p.map φ).mahlerMeasure := hmig
    _ ≤ (2 : ℝ) ^ n * (Real.sqrt (n + 1) * (p.map φ).supNorm) :=
        mul_le_mul hchoose hml (Polynomial.mahlerMeasure_nonneg _) (by positivity)
    _ ≤ (2 : ℝ) ^ n * (Real.sqrt (n + 1) * ⨆ k : Fin (n + 1), w (p.coeff ↑k)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hsup (Real.sqrt_nonneg _)
    _ = (2 ^ n * Real.sqrt (n + 1)) * ⨆ k : Fin (n + 1), w (p.coeff ↑k) := by ring

private lemma mwfac_hasFiniteMulSupport_iSup {ι : Type*} [Finite ι] {x : ι → K} (hx : x ≠ 0) :
    (fun v : FinitePlace K ↦ ⨆ i, v (x i)).HasFiniteMulSupport := by
  obtain ⟨i₀, hi₀⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.mp hx
  have : Nonempty ι := .intro i₀
  have hne : Nonempty {j // x j ≠ 0} := ⟨⟨i₀, hi₀⟩⟩
  have key : ∀ v : FinitePlace K, (⨆ i, v (x i)) = ⨆ i : {j // x j ≠ 0}, v (x i.val) := by
    intro v
    refine le_antisymm (ciSup_le fun j ↦ ?_) (ciSup_le fun i ↦ Finite.le_ciSup_of_le i.val le_rfl)
    rcases eq_or_ne (x j) 0 with h | h
    · rw [h, map_zero]
      exact Real.iSup_nonneg fun i ↦ apply_nonneg v _
    · exact Finite.le_ciSup_of_le ⟨j, h⟩ le_rfl
  have : (fun v : FinitePlace K ↦ ⨆ i, v (x i)) =
      fun v : FinitePlace K ↦ ⨆ i : {j // x j ≠ 0}, v (x i.val) := funext key
  rw [this]
  exact Function.HasFiniteMulSupport.iSup fun i ↦ FinitePlace.hasFiniteMulSupport i.prop

private lemma mwfac_mulHeight_coeff_le_of_monic {n : ℕ} {p q : Polynomial K}
    (hp : p.Monic) (hdeg : p.natDegree ≤ n) (hq : q.Monic) (hdvd : q ∣ p) :
    Height.mulHeight (fun k : Fin (n + 1) ↦ q.coeff k) ≤
      (2 ^ n * Real.sqrt (n + 1)) ^ Height.totalWeight K *
        Height.mulHeight (fun k : Fin (n + 1) ↦ p.coeff k) := by
  obtain ⟨r, hpqr⟩ := hdvd
  have hr : r.Monic := hq.of_mul_monic_left (hpqr ▸ hp)
  have hp0 : p ≠ 0 := hp.ne_zero
  have hdq : q.natDegree ≤ n := (natDegree_le_of_dvd ⟨r, hpqr⟩ hp0).trans hdeg
  have htq : (fun k : Fin (n + 1) ↦ q.coeff k) ≠ 0 := by
    refine Function.ne_iff.mpr ⟨⟨q.natDegree, Nat.lt_succ_of_le hdq⟩, ?_⟩
    simp [hq.coeff_natDegree]
  have htp : (fun k : Fin (n + 1) ↦ p.coeff k) ≠ 0 := by
    refine Function.ne_iff.mpr ⟨⟨p.natDegree, Nat.lt_succ_of_le hdeg⟩, ?_⟩
    simp [hp.coeff_natDegree]
  set A : ℝ := 2 ^ n * Real.sqrt (n + 1) with hA
  have hA0 : (0 : ℝ) ≤ A := by rw [hA]; positivity
  rw [NumberField.mulHeight_eq htq, NumberField.mulHeight_eq htp]
  have harch : (∏ w : InfinitePlace K, (⨆ k : Fin (n + 1), w (q.coeff k)) ^ w.mult) ≤
      ∏ w : InfinitePlace K,
        (A * ⨆ k : Fin (n + 1), w (p.coeff k)) ^ w.mult := by
    refine Finset.prod_le_prod (fun w _ ↦ ?_) (fun w _ ↦ ?_)
    · exact pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass w _) _
    · exact pow_le_pow_left₀ (Real.iSup_nonneg_of_nonnegHomClass w _)
        (mwfac_infinitePlace_iSup_coeff_le w hq hr hpqr hdeg) _
  have hfin : (∏ᶠ w : FinitePlace K, ⨆ k : Fin (n + 1), w (q.coeff k)) ≤
      ∏ᶠ w : FinitePlace K, ⨆ k : Fin (n + 1), w (p.coeff k) := by
    refine finprod_le_finprod (mwfac_hasFiniteMulSupport_iSup htq)
      (fun w ↦ Real.iSup_nonneg_of_nonnegHomClass w _)
      (mwfac_hasFiniteMulSupport_iSup htp) (fun w ↦ ?_)
    have hna : IsNonarchimedean (⇑(w.val) : K → ℝ) := by
      intro a b
      simpa only [FinitePlace.coe_apply] using w.add_le a b
    have h := mwfac_nonarch_iSup_coeff_le (v := w.val) hna hq hr hpqr hdeg
    simpa only [FinitePlace.coe_apply] using h
  calc (∏ w : InfinitePlace K, (⨆ k : Fin (n + 1), w (q.coeff k)) ^ w.mult) *
        ∏ᶠ w : FinitePlace K, ⨆ k : Fin (n + 1), w (q.coeff k)
      ≤ (∏ w : InfinitePlace K,
          (A * ⨆ k : Fin (n + 1), w (p.coeff k)) ^ w.mult) *
          ∏ᶠ w : FinitePlace K, ⨆ k : Fin (n + 1), w (p.coeff k) := by
        refine mul_le_mul harch hfin ?_ ?_
        · exact finprod_nonneg fun w ↦ Real.iSup_nonneg_of_nonnegHomClass w _
        · exact Finset.prod_nonneg fun w _ ↦ pow_nonneg
            (mul_nonneg hA0 (Real.iSup_nonneg_of_nonnegHomClass w _)) _
    _ = A ^ Height.totalWeight K *
          ((∏ w : InfinitePlace K, (⨆ k : Fin (n + 1), w (p.coeff k)) ^ w.mult) *
            ∏ᶠ w : FinitePlace K, ⨆ k : Fin (n + 1), w (p.coeff k)) := by
        simp_rw [mul_pow]
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
          ← NumberField.totalWeight_eq_sum_mult, mul_assoc]

end helpers

theorem solution (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    ∃ c : ℝ, ∀ p q : Polynomial K, p ≠ 0 → p.natDegree ≤ n → q.Monic → q ∣ p →
      Height.logHeight (fun k : Fin (n + 1) => q.coeff k)
        ≤ Height.logHeight (fun k : Fin (n + 1) => p.coeff k) + c := by
  refine ⟨(Height.totalWeight K : ℝ) * Real.log (2 ^ n * Real.sqrt (n + 1)),
    fun p q hp hdeg hq hdvd ↦ ?_⟩
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp

  have hdeg' : (p * C p.leadingCoeff⁻¹).natDegree ≤ n := by
    rw [Polynomial.natDegree_mul_leadingCoeff_inv p hp]; exact hdeg
  have hmain := mwfac_mulHeight_coeff_le_of_monic (n := n)
    (Polynomial.monic_mul_leadingCoeff_inv hp) hdeg' hq (hdvd.mul_right _)
  have htup : (fun k : Fin (n + 1) ↦ (p * C p.leadingCoeff⁻¹).coeff k) =
      p.leadingCoeff⁻¹ • fun k : Fin (n + 1) ↦ p.coeff k := by
    funext k
    simp only [coeff_mul_C, Pi.smul_apply, smul_eq_mul]
    ring
  rw [htup, Height.mulHeight_smul_eq_mulHeight _ (inv_ne_zero hlc)] at hmain
  have hlog : Height.logHeight (fun k : Fin (n + 1) => q.coeff k) ≤
      Real.log ((2 ^ n * Real.sqrt (n + 1)) ^ Height.totalWeight K *
        Height.mulHeight (fun k : Fin (n + 1) => p.coeff k)) := by
    rw [Height.logHeight_eq_log_mulHeight]
    exact Real.log_le_log (Height.mulHeight_pos _) hmain
  refine hlog.trans ?_
  have hAne : ((2 : ℝ) ^ n * Real.sqrt (n + 1)) ^ Height.totalWeight K ≠ 0 := by positivity
  rw [Real.log_mul hAne (Height.mulHeight_ne_zero _), Real.log_pow,
    Height.logHeight_eq_log_mulHeight]
  exact le_of_eq (add_comm _ _)

end S_Height_logHeight_coeff_factor_le
end P2MW
export P2MW.S_Height_logHeight_coeff_factor_le (solution)
