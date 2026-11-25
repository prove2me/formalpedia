-- Prove2me | solution 1 for GroundTheory.PAdicHodge.TeichLift.exists_inv_convergesAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:40:42.636884+00:00
-- url     : https://prove2.me/submissions/29b3ee7b-0fb8-4c65-b29b-b804a981edfc

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaTeich
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Definitions.Def_GroundTheory_PAdicHodge_ExtRobbaBounded
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_isUnit_of_coeff_zero_eq_one
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_gaussNorm_single_zero_one_le
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_convergesAt_zero
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_gaussNorm_le
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_gaussNorm_nonneg
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_eq_coeff_of_sub_mem
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_ofCoeff
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_succ
import Theorems.Thm_GroundTheory_PAdicHodge_TeichLift_coeff_zero_elem
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_succ_f7b410ef729e
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0
import Theorems.Thm_P2M_GroundTheory_PAdicHodge_TeichLift_sub_teich_eq___mul_tail_219974f30227
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_ofCoeff
attribute [local simp] GroundTheory.PAdicHodge.TeichLift.coeff_zero_elem
attribute [local simp] P2M_GroundTheory_PAdicHodge_TeichLift_coeff___mul_zero_c24e500c7aa0



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.PAdicHodge
open Laurent Filter Topology
open GroundTheory.PAdicHodge.TeichLift
variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ) {ρ : ℝ}
variable {b c : T.B}
namespace GroundTheory.PAdicHodge.TeichLift
theorem _root_.solution {u : Γ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hu : ConvergesAt (T.zcoeff u) ρ) (h1 : T.coeff u 0 = 1) :
    ∃ v : Γ, u * v = 1 ∧ ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' < 1 ∧ ConvergesAt (T.zcoeff v) ρ' := by
  obtain ⟨v, hv⟩ := (T.isUnit_of_coeff_zero_eq_one h1).exists_right_inv
  refine ⟨v, hv, ?_⟩
  have hG1 : 1 ≤ gaussNorm (T.zcoeff u) ρ := by
    have := T.weight_natCast_le hu 0; simpa [h1] using this
  set G := gaussNorm (T.zcoeff u) ρ
  have he' : u - 1 = T.π * T.tail u := by
    rw [← T.sub_teich_eq_π_mul_tail, ← coeff_zero, h1, T.teich_one]
  have he_coeff : ∀ n : ℕ, T.coeff (u - 1) n = if n = 0 then 0 else T.coeff u n := by
    intro n
    rcases n with _ | n
    · rw [he', coeff_π_mul_zero]; simp
    · rw [he', coeff_π_mul_succ, ← coeff_succ]; simp
  set ρ1 := ρ / (2 * G) with hρ1def
  have hρ1pos : 0 < ρ1 := by positivity
  have hρ1le : ρ1 ≤ ρ / 2 := div_le_div_of_nonneg_left hρ0.le (by norm_num) (by linarith)
  have hρ1lt1 : ρ1 < 1 := by linarith
  have he_conv : ConvergesAt (T.zcoeff (u - 1)) ρ1 := by
    rw [sub_eq_add_neg]
    refine convergesAt_of_le (T.zcoeff_neg_exists _) (T.convergesAt_zcoeff_add hρ0 hρ1 hu
      (T.convergesAt_zcoeff_neg hρ0 hρ1 (by rw [zcoeff_one]; exact convergesAt_pi_single 0 1 ρ)))
      hρ1pos (by linarith)
  have he_norm : gaussNorm (T.zcoeff (u - 1)) ρ1 ≤ 1 / 2 := by
    refine gaussNorm_le fun n => ?_
    rcases lt_or_ge n 0 with hn | hn
    · rw [T.zcoeff_of_neg _ hn, norm_zero, zero_mul]; norm_num
    lift n to ℕ using hn
    rw [zcoeff_natCast, he_coeff]
    split_ifs with hn0
    · simp
    · have hw := T.weight_natCast_le hu n
      have ht : (1 / (2 * G)) ^ n ≤ 1 / (2 * G) :=
        pow_le_of_le_one (by positivity) (by rw [div_le_one (by positivity)]; linarith) hn0
      calc ‖T.coeff u n‖ * ρ1 ^ (n : ℤ) = (‖T.coeff u n‖ * ρ ^ (n : ℤ)) * (1 / (2 * G)) ^ n := by
            rw [zpow_natCast, zpow_natCast, hρ1def, div_eq_mul_one_div ρ, mul_pow]; ring
        _ ≤ G * (1 / (2 * G)) := mul_le_mul hw ht (by positivity) (by linarith)
        _ = 1 / 2 := by field_simp
  have hne := T.convergesAt_zcoeff_neg hρ1pos hρ1lt1 he_conv
  have hpow : ∀ k : ℕ, ConvergesAt (T.zcoeff ((-(u - 1)) ^ k)) ρ1 ∧
      gaussNorm (T.zcoeff ((-(u - 1)) ^ k)) ρ1 ≤ 1 := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, zcoeff_one]
      exact ⟨convergesAt_pi_single 0 1 ρ1, gaussNorm_single_zero_one_le hρ1pos⟩
    | succ k ih =>
      rw [pow_succ]
      refine ⟨T.convergesAt_zcoeff_mul hρ1pos hρ1lt1 ih.1 hne, ?_⟩
      rw [T.gaussNorm_zcoeff_mul hρ1pos hρ1lt1 ih.1 hne, T.gaussNorm_zcoeff_neg hρ1pos hρ1lt1 he_conv]
      have := gaussNorm_nonneg (a := T.zcoeff (u - 1)) hρ1pos
      nlinarith [ih.2, gaussNorm_nonneg (a := T.zcoeff ((-(u - 1)) ^ k)) hρ1pos]
  have hsum : ∀ K : ℕ, ConvergesAt (T.zcoeff (∑ k ∈ Finset.range K, (-(u - 1)) ^ k)) ρ1 ∧
      gaussNorm (T.zcoeff (∑ k ∈ Finset.range K, (-(u - 1)) ^ k)) ρ1 ≤ 1 := by
    intro K
    induction K with
    | zero =>
      rw [Finset.sum_range_zero, (T.zcoeff_eq_zero_iff 0).2 rfl]
      exact ⟨convergesAt_zero, by simp [gaussNorm]⟩
    | succ K ih =>
      rw [Finset.sum_range_succ]
      exact ⟨T.convergesAt_zcoeff_add hρ1pos hρ1lt1 ih.1 (hpow K).1,
        (T.gaussNorm_zcoeff_add_le hρ1pos hρ1lt1.le ih.1 (hpow K).1).trans (max_le ih.2 (hpow K).2)⟩
  have hvS : ∀ K : ℕ, v - ∑ k ∈ Finset.range K, (-(u - 1)) ^ k ∈ Ideal.span {T.π ^ K} := by
    intro K
    have hgeom := geom_sum_mul_neg (-(u - 1)) K
    rw [show 1 - -(u - 1) = u by ring] at hgeom
    have : v - ∑ k ∈ Finset.range K, (-(u - 1)) ^ k = (-(u - 1)) ^ K * v := by
      have h2 : (∑ k ∈ Finset.range K, (-(u - 1)) ^ k) * u * v = (1 - (-(u - 1)) ^ K) * v := by
        rw [hgeom]
      have h3 : (∑ k ∈ Finset.range K, (-(u - 1)) ^ k) * u * v =
          ∑ k ∈ Finset.range K, (-(u - 1)) ^ k := by rw [mul_assoc, hv, mul_one]
      rw [h3] at h2; rw [h2]; ring
    rw [this, he']
    exact T.mem_span_pow.2 ⟨(-T.tail u) ^ K * v, by ring⟩
  have hvb : ∀ n : ℕ, ‖T.coeff v n‖ * ρ1 ^ (n : ℤ) ≤ 1 := by
    intro n
    rw [T.coeff_eq_coeff_of_sub_mem (hvS (n + 1)) n le_rfl]
    exact (T.weight_natCast_le (hsum (n + 1)).1 n).trans (hsum (n + 1)).2
  refine ⟨ρ1 / 2, by positivity, by linarith, ?_⟩
  refine convergesAt_of_eventually (by positivity) (T.zcoeff_neg_exists v) fun ε hε => ?_
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨K, fun n hn => ?_⟩
  lift n to ℕ using (by omega)
  have hKn : K ≤ n := by exact_mod_cast hn
  rw [zcoeff_natCast]
  calc ‖T.coeff v n‖ * (ρ1 / 2) ^ (n : ℤ) = (‖T.coeff v n‖ * ρ1 ^ (n : ℤ)) * (1 / 2) ^ n := by
        rw [zpow_natCast, zpow_natCast, div_eq_mul_one_div ρ1 2, mul_pow]; ring
    _ ≤ 1 * (1 / 2) ^ K :=
        mul_le_mul (hvb n) (pow_le_pow_of_le_one (by norm_num) (by norm_num) hKn) (by positivity)
          zero_le_one
    _ ≤ ε := by rw [one_mul]; exact hK.le
end GroundTheory.PAdicHodge.TeichLift
