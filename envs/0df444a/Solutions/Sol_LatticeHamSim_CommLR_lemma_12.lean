-- Prove2me | solution 1 for LatticeHamSim.CommLR.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:25:22.458412+00:00
-- url     : https://prove2.me/submissions/fb888776-da89-45c7-8096-f40f4c17edf6

import Mathlib
import Definitions.Def_LatticeHamSim_CommLR_Setting
import Theorems.Thm_LatticeHamSim_CommLR_eq_32
import Theorems.Thm_LatticeHamSim_CommLR_eq_37
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

attribute [local instance] Classical.propDecidable

namespace Aux_LHS_Lemma12

open LatticeHamSim.CommLR

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}

lemma comm_bound (P B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    ‖P * B - B * P‖ ≤ 2 * ‖P‖ * ‖B‖ := by
  calc ‖P * B - B * P‖ ≤ ‖P * B‖ + ‖B * P‖ := norm_sub_le _ _
    _ ≤ ‖P‖ * ‖B‖ + ‖B‖ * ‖P‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖P‖ * ‖B‖ := by ring

lemma evolve_norm (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (t : ℝ) (O : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) :
    ‖evolve (H h) t O‖ = ‖O‖ := by
  have hsa : star (H h) = H h := by
    unfold H
    rw [star_sum]
    exact Finset.sum_congr rfl (fun X _ => hherm X)
  have key : ∀ s : ℝ, NormedSpace.exp ((Complex.I * (s : ℂ)) • H h) ∈
      unitary (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) := by
    intro s
    have hs : ((s : ℂ) • H h) ∈ selfAdjoint (Matrix (Λ → Fin q) (Λ → Fin q) ℂ) := by
      rw [selfAdjoint.mem_iff, star_smul, hsa, Complex.star_def, Complex.conj_ofReal]
    have := (selfAdjoint.expUnitary ⟨(s : ℂ) • H h, hs⟩).prop
    simp only [selfAdjoint.expUnitary_coe, smul_smul] at this
    exact this
  unfold evolve
  have hU := key t
  have hV := key (-t)
  rw [show (-(Complex.I * (t : ℂ))) = Complex.I * ((-t : ℝ) : ℂ) by push_cast; ring]
  rw [CStarRing.norm_mul_mem_unitary _ hV, CStarRing.norm_mem_unitary_mul _ hU]

lemma supportedOn_smul (X : Finset Λ) (c : ℂ) (A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hA : SupportedOn X A) : SupportedOn X (c • A) := by
  obtain ⟨m, hm⟩ := hA
  refine ⟨c • m, fun σ τ => ?_⟩
  simp only [Matrix.smul_apply, hm σ τ, smul_eq_mul, mul_ite, mul_zero]

lemma cb_bddAbove (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ) :
    BddAbove {r : ℝ | ∃ A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ,
      SupportedOn X A ∧ ‖A‖ ≤ 1 ∧
      r = ‖evolve (H h) t A * B - B * evolve (H h) t A‖} := by
  refine ⟨2 * ‖B‖, ?_⟩
  rintro r ⟨A, -, hA1, rfl⟩
  refine le_trans (comm_bound _ _) ?_
  rw [evolve_norm h hherm]
  nlinarith [norm_nonneg A, norm_nonneg B]

lemma norm_comm_evolve_le_CB (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ)
    (A : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (hA : SupportedOn X A) :
    ‖evolve (H h) t A * B - B * evolve (H h) t A‖ ≤ ‖A‖ * CB h B X t := by
  by_cases hA0 : ‖A‖ = 0
  · have hAz : A = 0 := norm_eq_zero.mp hA0
    simp [hAz, hA0, evolve]
  · have hApos : 0 < ‖A‖ := lt_of_le_of_ne (norm_nonneg A) (Ne.symm hA0)
    set c : ℂ := ((‖A‖⁻¹ : ℝ) : ℂ)
    set A' : Matrix (Λ → Fin q) (Λ → Fin q) ℂ := c • A
    have hA'supp : SupportedOn X A' := supportedOn_smul X c A hA
    have hA'norm : ‖A'‖ ≤ 1 := by
      change ‖((‖A‖⁻¹ : ℝ) : ℂ) • A‖ ≤ 1
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hApos)),
        inv_mul_cancel₀ hA0]
    have hev : evolve (H h) t A' * B - B * evolve (H h) t A' =
        c • (evolve (H h) t A * B - B * evolve (H h) t A) := by
      unfold A' evolve
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    have hmem : ‖A‖⁻¹ * ‖evolve (H h) t A * B - B * evolve (H h) t A‖ ∈
        {r : ℝ | ∃ M : Matrix (Λ → Fin q) (Λ → Fin q) ℂ,
          SupportedOn X M ∧ ‖M‖ ≤ 1 ∧
          r = ‖evolve (H h) t M * B - B * evolve (H h) t M‖} := by
      refine ⟨A', hA'supp, hA'norm, ?_⟩
      rw [hev, norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt hApos))]
    have hle : ‖A‖⁻¹ * ‖evolve (H h) t A * B - B * evolve (H h) t A‖ ≤ CB h B X t :=
      le_csSup (cb_bddAbove h hherm B X t) hmem
    calc ‖evolve (H h) t A * B - B * evolve (H h) t A‖
        = ‖A‖ * (‖A‖⁻¹ * ‖evolve (H h) t A * B - B * evolve (H h) t A‖) := by
          rw [← mul_assoc, mul_inv_cancel₀ hA0, one_mul]
      _ ≤ ‖A‖ * CB h B X t := mul_le_mul_of_nonneg_left hle (le_of_lt hApos)

lemma eta_two_pow_le (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (k : ℕ) :
    η ^ ((k + 1) / 2) * 2 ^ (k / 2) ≤ (Real.sqrt η)⁻¹ * (Real.sqrt (2 * η)) ^ (k + 1) := by
  have hsqrt_pos : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hmain : Real.sqrt η * (η ^ ((k + 1) / 2) * 2 ^ (k / 2)) ≤ (Real.sqrt (2 * η)) ^ (k + 1) := by
    have hsq2 : (Real.sqrt (2 * η)) ^ 2 = 2 * η := Real.sq_sqrt (by linarith)
    rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
    · have hd1 : (2 * m + 1) / 2 = m := by omega
      have hd2 : (2 * m) / 2 = m := by omega
      rw [hd1, hd2, pow_add, pow_one, pow_mul, hsq2]
      have hpow : η ^ m * (2 : ℝ) ^ m = (2 * η) ^ m := by rw [← mul_pow, mul_comm]
      rw [hpow]
      have hle : Real.sqrt η ≤ Real.sqrt (2 * η) := Real.sqrt_le_sqrt (by linarith)
      calc Real.sqrt η * (2 * η) ^ m
          ≤ Real.sqrt (2 * η) * (2 * η) ^ m := mul_le_mul_of_nonneg_right hle (by positivity)
        _ = (2 * η) ^ m * Real.sqrt (2 * η) := mul_comm _ _
    · have hd1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      have hd2 : (2 * m + 1) / 2 = m := by omega
      rw [hd1, hd2, show 2 * m + 1 + 1 = 2 * (m + 1) by omega, pow_mul, hsq2]
      have hpow : η ^ (m + 1) * (2 : ℝ) ^ m = η * (2 * η) ^ m := by
        rw [pow_succ', mul_assoc, ← mul_pow, mul_comm η 2]
      have hpow2 : (2 * η) ^ (m + 1) = (2 * η) * (2 * η) ^ m := pow_succ' _ _
      rw [hpow, hpow2, ← mul_assoc]
      have hsqrt1 : Real.sqrt η ≤ 2 := (Real.sqrt_le_one.mpr hη1).trans (by norm_num)
      have hle : Real.sqrt η * η ≤ 2 * η := mul_le_mul_of_nonneg_right hsqrt1 (le_of_lt hη)
      exact mul_le_mul_of_nonneg_right hle (by positivity)
  calc η ^ ((k + 1) / 2) * 2 ^ (k / 2)
      = (Real.sqrt η)⁻¹ * (Real.sqrt η * (η ^ ((k + 1) / 2) * 2 ^ (k / 2))) := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsqrt_pos), one_mul]
    _ ≤ (Real.sqrt η)⁻¹ * (Real.sqrt (2 * η)) ^ (k + 1) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)

lemma hasSum_exp_sub_one (x : ℝ) :
    HasSum (fun k : ℕ => x ^ (k + 1) / ((k + 1).factorial : ℝ)) (Real.exp x - 1) := by
  have h1 : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]
    simpa [div_eq_inv_mul] using NormedSpace.expSeries_div_hasSum_exp x
  have h2 := (hasSum_nat_add_iff' 1).mpr h1
  simpa [Finset.sum_range_one] using h2

end Aux_LHS_Lemma12

open LatticeHamSim.CommLR Aux_LHS_Lemma12 in
theorem solution {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ]
    {q : ℕ} (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (hsupp : ∀ X, SupportedOn X (h X))
    (η ζ μ : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (h14 : ∀ X Y, ‖h X * h Y - h Y * h X‖ ≤
      2 * η * ‖h X‖ * ‖h Y‖)
    (hζ : 0 < ζ) (hμ : 0 < μ)
    (h15 : ∀ x : Λ,
      ∑ Z ∈ Finset.univ.filter (fun Z : Finset Λ => x ∈ Z),
        ‖h Z‖ * (Z.card : ℝ) ^ 2 *
          Real.exp (μ * Metric.diam (Z : Set Λ)) ≤ ζ)
    (X Y : Finset Λ) (hXY : Disjoint X Y)
    (A B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hA : SupportedOn X A) (hB : SupportedOn Y B) (t : ℝ) :
    ‖evolve (H h) t A * B - B * evolve (H h) t A‖ ≤
      2 / Real.sqrt η * ‖A‖ * ‖B‖ *
        (Real.exp (ζ * |t| * Real.sqrt (8 * η)) - 1) *
        ∑ x ∈ X, Real.exp (-(μ * Metric.infDist x (Y : Set Λ))) := by
  obtain ⟨S, hS_sum, hCB_le⟩ := eq_32 h hherm hsupp η (le_of_lt hη) hη1 h14 X Y hXY B hB t
  set E : ℝ := ∑ x ∈ X, Real.exp (-(μ * Metric.infDist x (Y : Set Λ)))
  set x : ℝ := ζ * |t| * Real.sqrt (8 * η)
  set c : ℝ := (Real.sqrt η)⁻¹ * E
  have hE_nn : 0 ≤ E := Finset.sum_nonneg (fun _ _ => le_of_lt (Real.exp_pos _))
  have hx_eq : x = 2 * |t| * ζ * Real.sqrt (2 * η) := by
    unfold x
    have h8 : Real.sqrt (8 * η) = 2 * Real.sqrt (2 * η) := by
      rw [show (8 : ℝ) * η = 2 ^ 2 * (2 * η) by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [h8]
    ring
  have hterm_le : ∀ k : ℕ,
      (2 * |t|) ^ (k + 1) / ((k + 1).factorial : ℝ) *
        η ^ ((k + 1) / 2) * linkedWeight h X Y (k + 1) ≤
      c * (x ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
    intro k
    have h37 := eq_37 h η ζ μ (le_of_lt hη) hη1 hζ hμ h15 X Y t (k + 1) (Nat.le_add_left 1 k)
    simp only [Nat.add_sub_cancel] at h37
    refine h37.trans ?_
    have heta := eta_two_pow_le η hη hη1 k
    have hfac_nn : 0 ≤ (2 * |t|) ^ (k + 1) / ((k + 1).factorial : ℝ) := by positivity
    have hzeta_nn : 0 ≤ ζ ^ (k + 1) := by positivity
    calc (2 * |t|) ^ (k + 1) / ((k + 1).factorial : ℝ) * η ^ ((k + 1) / 2) * 2 ^ (k / 2) * ζ ^ (k + 1) * E
        = ((2 * |t|) ^ (k + 1) / ((k + 1).factorial : ℝ) * ζ ^ (k + 1) * E) *
            (η ^ ((k + 1) / 2) * 2 ^ (k / 2)) := by ring
      _ ≤ ((2 * |t|) ^ (k + 1) / ((k + 1).factorial : ℝ) * ζ ^ (k + 1) * E) *
            ((Real.sqrt η)⁻¹ * (Real.sqrt (2 * η)) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left heta (by positivity)
      _ = c * ((2 * |t| * ζ * Real.sqrt (2 * η)) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by
          unfold c
          rw [mul_pow, mul_pow]
          ring
      _ = c * (x ^ (k + 1) / ((k + 1).factorial : ℝ)) := by rw [← hx_eq]
  have hHasSum_rhs : HasSum (fun k : ℕ => c * (x ^ (k + 1) / ((k + 1).factorial : ℝ))) (c * (Real.exp x - 1)) :=
    (hasSum_exp_sub_one x).const_smul c
  have hS_le : S ≤ c * (Real.exp x - 1) :=
    hasSum_le hterm_le hS_sum hHasSum_rhs
  have h1 := norm_comm_evolve_le_CB h hherm B X t A hA
  calc ‖evolve (H h) t A * B - B * evolve (H h) t A‖
      ≤ ‖A‖ * CB h B X t := h1
    _ ≤ ‖A‖ * (2 * ‖B‖ * S) := mul_le_mul_of_nonneg_left hCB_le (norm_nonneg A)
    _ ≤ ‖A‖ * (2 * ‖B‖ * (c * (Real.exp x - 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hS_le (by positivity)) (norm_nonneg A)
    _ = 2 / Real.sqrt η * ‖A‖ * ‖B‖ * (Real.exp x - 1) * E := by
        unfold c
        ring
