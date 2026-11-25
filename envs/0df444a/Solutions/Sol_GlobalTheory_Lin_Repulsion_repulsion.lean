-- Prove2me | solution 1 for GlobalTheory.Lin.Repulsion.repulsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:01:28.890903+00:00
-- url     : https://prove2.me/submissions/a1a18b2e-dbb6-4432-a095-8090b01a9377

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIccThreeQuartersPowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Repulsion
import Theorems.Thm_GlobalTheory_Lin_Repulsion_one_le_ord
import Theorems.Thm_GlobalTheory_Lin_Repulsion_der_pos
import Theorems.Thm_GlobalTheory_Lin_Repulsion_exists_list
import Theorems.Thm_GlobalTheory_Lin_Repulsion_exists_erase
import Theorems.Thm_GlobalTheory_Lin_Repulsion_power_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.Repulsion
namespace GlobalTheory.Lin.Repulsion
theorem _root_.solution : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (β L : ℝ) (ρ : ℂ), χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β < 1 → 1 / 2 ≤ β → LFunction χ₁ β = 0 → LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re → ρ.re < 1 → (χ ≠ χ₁ ∨ ρ ≠ β ∨ 2 ≤ ord χ₁ β) → Real.log (q * (|ρ.im| + 2)) ≤ L → c * Real.log (c / ((1 - β) * L)) / L ≤ 1 - ρ.re := by
  obtain ⟨C, hC, H⟩ := exists_list
  obtain ⟨D, hD, P⟩ := power_step
  refine ⟨1 / (D * (8 * C + 4)), by positivity, ?_⟩
  intro q _ χ₁ χ β L ρ h1 hsq hβ hβ' hz₁ hz hρ hρ' hcase hL
  set t := ρ.im with ht
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hL0 : Real.log (q * (|(0 : ℝ)| + 2)) ≤ L := by
    refine le_trans (Real.log_le_log (by positivity) ?_) hL
    rw [abs_zero]
    exact mul_le_mul_of_nonneg_left (by linarith [abs_nonneg t]) (by linarith)
  have hLh : 1 / 2 ≤ L := by
    refine le_trans ?_ hL0
    have := Real.log_two_gt_d9
    refine le_trans (by linarith : (1 : ℝ) / 2 ≤ Real.log 2) (Real.log_le_log (by norm_num) ?_)
    rw [abs_zero]; linarith
  have hβ1 : (β : ℂ) ≠ 1 := by exact_mod_cast hβ.ne
  have hρ1 : ρ ≠ 1 := by rintro rfl; simp at hρ'
  have eρ : (2 : ℂ) + t * I - ρ = ((2 - ρ.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [ht]
  have hρd : ‖ρ - (2 + t * I)‖ ≤ 3 := by
    rw [norm_sub_rev, eρ, Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
  obtain ⟨W0, -, c0, s0⟩ := H q 1 0 L hL0
  obtain ⟨W1, m1, c1, s1⟩ := H q χ₁ 0 L hL0
  obtain ⟨W2, m2, c2, s2⟩ := H q χ t L hL
  obtain ⟨W3, m3, c3, s3⟩ := H q (χ * χ₁) t L hL
  have hρ2 : ρ ∈ W2 := by
    rw [← Multiset.one_le_count_iff_mem, m2 ρ hρd hρ1 hz]; exact one_le_ord χ hρ1 hz
  obtain ⟨V1, d1, -, r1⟩ := exists_erase hβ hβ' W1 0 fun hd => by
    rw [← Multiset.one_le_count_iff_mem, m1 β hd hβ1 hz₁]; exact one_le_ord χ₁ hβ1 hz₁
  have hmul : χ * χ₁ = 1 ↔ χ = χ₁ := by
    constructor
    · intro h
      calc χ = χ * χ₁ ^ 2 := by rw [hsq, mul_one]
        _ = χ₁ := by rw [sq, ← mul_assoc, h, one_mul]
    · rintro rfl; rw [← sq, hsq]
  obtain ⟨V2, V3, d2, d3, hρV, r23⟩ : ∃ V2 V3 : Multiset ℂ, V2.card ≤ W2.card ∧ V3.card ≤ W3.card ∧
      ρ ∈ V2 ∧ ∀ j : ℕ, (powSum V2 t j).re + (powSum V3 t j).re +
        (if χ = 1 then 1 / ((2 : ℂ) + t * I - 1) ^ j else 0).re +
        (if χ * χ₁ = 1 then 1 / ((2 : ℂ) + t * I - 1) ^ j else 0).re ≤
        (powSum W2 t j).re + (powSum W3 t j).re + j * (1 - β) + 1 / 2 ^ j := by
    by_cases a : χ = 1
    · subst a
      rw [one_mul] at m3 ⊢
      obtain ⟨V, d, -, r⟩ := exists_erase hβ hβ' W3 t fun hd => by
        rw [← Multiset.one_le_count_iff_mem, m3 β hd hβ1 hz₁]; exact one_le_ord χ₁ hβ1 hz₁
      refine ⟨W2, V, le_rfl, d, hρ2, fun j => ?_⟩
      rw [if_pos rfl, if_neg h1, Complex.zero_re]
      linarith [r j]
    by_cases b : χ = χ₁
    · subst b
      obtain ⟨V, d, m, r⟩ := exists_erase hβ hβ' W2 t fun hd => by
        rw [← Multiset.one_le_count_iff_mem, m2 β hd hβ1 hz₁]; exact one_le_ord χ hβ1 hz₁
      refine ⟨V, W3, d, le_rfl, m ρ hρ2 ?_, fun j => ?_⟩
      · by_cases hb : ρ = β
        · right
          rw [m2 ρ hρd hρ1 hz, hb]
          simpa [hb] using hcase
        · exact Or.inl hb
      · rw [if_neg a, if_pos (hmul.2 rfl), Complex.zero_re]
        linarith [r j]
    · refine ⟨W2, W3, le_rfl, le_rfl, hρ2, fun j => ?_⟩
      rw [if_neg a, if_neg (mt hmul.1 b), Complex.zero_re]
      have : (0 : ℝ) ≤ j * (1 - β) := by have : 0 ≤ 1 - β := by linarith
                                         positivity
      have : (0 : ℝ) ≤ 1 / 2 ^ j := by positivity
      linarith
  have hCL : 0 ≤ C * L := by positivity
  have key := P ((W0 + V1).map (fun w => 1 / ((2 : ℂ) + (0 : ℝ) * I - w)) +
      (V2 + V3).map (fun w => 1 / ((2 : ℂ) + t * I - w))) (1 / ((2 : ℂ) + t * I - ρ))
      ((8 * C + 4) * L) (1 - β) (1 - ρ.re)
      (Multiset.mem_add.2 (Or.inr (Multiset.mem_map_of_mem _ (Multiset.mem_add.2 (Or.inl hρV)))))
      (by nlinarith) (by linarith) (by linarith) (by linarith) ?_ ?_ ?_
  · have hL' : 0 < L := by linarith
    have hδ : 0 < 1 - β := by linarith
    convert key using 1
    have e : 1 / (D * (8 * C + 4)) / ((1 - β) * L) = 1 / (D * ((8 * C + 4) * L) * (1 - β)) := by
      field_simp
    rw [e]; field_simp
  · rw [eρ, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    apply le_of_eq; congr 1; ring
  · simp only [Multiset.card_add, Multiset.card_map]
    have d1' : (V1.card : ℝ) ≤ W1.card := by exact_mod_cast d1
    have d2' : (V2.card : ℝ) ≤ W2.card := by exact_mod_cast d2
    have d3' : (V3.card : ℝ) ≤ W3.card := by exact_mod_cast d3
    push_cast
    nlinarith
  · intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have e : (Multiset.map (fun y => y ^ (k + 1)) ((W0 + V1).map (fun w => 1 / ((2 : ℂ) + (0 : ℝ) * I - w)) +
        (V2 + V3).map (fun w => 1 / ((2 : ℂ) + t * I - w)))).sum =
        powSum W0 0 (k + 1) + powSum V1 0 (k + 1) + powSum V2 t (k + 1) + powSum V3 t (k + 1) := by
      unfold powSum
      simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_map, Function.comp_def]
      ring
    rw [e]
    have hp := der_pos χ₁ χ hsq k t
    have a0 := s0 k
    have a1 := s1 k
    have a2 := s2 k
    have a3 := s3 k
    have b1 := r1 (k + 1)
    have b2 := r23 (k + 1)
    rw [if_pos rfl] at a0
    rw [if_neg h1, Complex.zero_re] at a1
    simp only [Complex.add_re] at hp ⊢
    have f : (8 * C + 4) * L / 2 ^ (k + 1) = 4 * (2 * C * L / 2 ^ (k + 1)) + 4 * L * (1 / 2 ^ (k + 1)) := by
      ring
    have g : (1 : ℝ) / 2 ^ (k + 1) * 2 ≤ 4 * L * (1 / 2 ^ (k + 1)) := by
      rw [mul_comm]; gcongr; linarith
    linarith
end GlobalTheory.Lin.Repulsion
