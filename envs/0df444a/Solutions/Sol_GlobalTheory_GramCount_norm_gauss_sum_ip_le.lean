-- Prove2me | solution 1 for GlobalTheory.GramCount.norm_gauss_sum_ip_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:43:39.925796+00:00
-- url     : https://prove2.me/submissions/72a968a2-14fa-4d3f-89e2-0dd53bef3bf5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormGaussSumHermitianFormLinearLe
import Theorems.Thm_GlobalTheory_GramCount_sum_char_unit_mul_ip_eq_zero
import Theorems.Thm_GlobalTheory_GramCount_cj_ip
import Theorems.Thm_GlobalTheory_GramCount_ip_add_left
import Theorems.Thm_GlobalTheory_GramCount_ip_add_right
import Theorems.Thm_GlobalTheory_GramCount_ip_zero_left
import Theorems.Thm_GlobalTheory_GramCount_ip_zero_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory GlobalTheory.GramCount
namespace GlobalTheory.GramCount
theorem _root_.solution {B : Type} [CommRing B] [Fintype B] (c : B →+* B)
    (hc : ∀ u, c (c u) = u) (q : ℕ) (_hq : 2 ≤ q) (hB : Fintype.card B = q ^ 2)
    (χ : AddChar B ℂ) (hχ : χ.IsPrimitive) (hinv : ∀ u, χ (c u) = χ u) (n : ℕ) (a : B)
    (ha : IsUnit (a + c a)) (v : Fin n → B) :
    ‖∑ y : Fin n → B, χ (a * ip c y y + ip c y v)‖ ≤ (q : ℝ) ^ n := by
  set Q : (Fin n → B) → B := fun y => a * ip c y y + ip c y v with hQ
  set S : ℂ := ∑ y : Fin n → B, χ (Q y) with hS
  have key : ∀ y z : Fin n → B,
      χ (Q (y + z)) * (starRingEnd ℂ) (χ (Q y)) = χ (Q z) * χ ((a + c a) * ip c y z) := by
    intro y z
    have h1 : χ (a * ip c z y) = χ (c a * ip c y z) := by
      rw [← hinv, map_mul, cj_ip c hc]
    have h2 : Q (y + z) + -Q y = Q z + a * ip c y z + a * ip c z y := by
      simp only [hQ, ip_add_left, ip_add_right]
      ring
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, h2, AddChar.map_add_eq_mul, h1,
      add_mul, AddChar.map_add_eq_mul χ (Q z), AddChar.map_add_eq_mul χ (a * ip c y z), mul_assoc]
  have hsq : S * (starRingEnd ℂ) S = (((q : ℝ) ^ n) ^ 2 : ℝ) := by
    calc S * (starRingEnd ℂ) S
        = ∑ y : Fin n → B, S * (starRingEnd ℂ) (χ (Q y)) := by
          conv_lhs => rw [hS, map_sum, ← hS, Finset.mul_sum]
      _ = ∑ y : Fin n → B, ∑ z : Fin n → B, χ (Q z) * χ ((a + c a) * ip c y z) := by
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [hS, ← Equiv.sum_comp (Equiv.addLeft y), Finset.sum_mul]
          exact Finset.sum_congr rfl fun z _ => key y z
      _ = ∑ z : Fin n → B, χ (Q z) * ∑ y : Fin n → B, χ ((a + c a) * ip c y z) := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ = (((q : ℝ) ^ n) ^ 2 : ℝ) := by
          rw [Finset.sum_eq_single (0 : Fin n → B)]
          · simp [hQ, ip_zero_left, ip_zero_right, hB, ← pow_mul, mul_comm]
          · intro z _ hz
            rw [sum_char_unit_mul_ip_eq_zero c hc χ hχ ha hz, mul_zero]
          · simp
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at hsq
  have h3 : ‖S‖ ^ 2 = ((q : ℝ) ^ n) ^ 2 := by exact_mod_cast hsq
  exact ((pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h3).le
end GlobalTheory.GramCount
