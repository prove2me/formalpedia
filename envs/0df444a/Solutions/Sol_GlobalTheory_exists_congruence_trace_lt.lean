-- Prove2me | solution 1 for GlobalTheory.exists_congruence_trace_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:44:33.320536+00:00
-- url     : https://prove2.me/submissions/a49b0625-1ff8-49d4-9c8d-e1f85b9f7c24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNatMulQuadraticLt
import Theorems.Thm_GlobalTheory_exists_nat_mul_quadratic_lt
import Theorems.Thm_GlobalTheory_trace_transvection_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (g N : ℕ), 2 ≤ g → 1 ≤ N → ∀ T : Matrix (Fin g) (Fin g) ℚ, T.IsSymm →
      (∃ v : Fin g → ℚ, v ⬝ᵥ T.mulVec v < 0) →
      ∀ c : ℚ, ∃ U : Matrix (Fin g) (Fin g) ℤ, U.det = 1 ∧
        (∀ i j, (N : ℤ) ∣ U i j - (1 : Matrix (Fin g) (Fin g) ℤ) i j) ∧
        ((U.map (Int.cast : ℤ → ℚ)).transpose * T * U.map (Int.cast : ℤ → ℚ)).trace < c := by
  intro g N hg hN T _ hv c
  obtain ⟨v, hv⟩ := hv
  set D : ℕ := ∏ i, (v i).den with hD
  have hDpos : 0 < D := Finset.prod_pos fun i _ => (v i).den_pos
  have hden : ∀ i, (v i).den ∣ D := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  set xz : Fin g → ℤ := fun i => ((D / (v i).den : ℕ) : ℤ) * (v i).num with hxz
  have hx : ∀ i, ((xz i : ℤ) : ℚ) = (D : ℚ) * v i := by
    intro i
    have hne : ((v i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (v i).den_nz
    simp only [hxz]
    rw [Int.cast_mul, Int.cast_natCast, Nat.cast_div (hden i) hne, ← Rat.mul_den_eq_num (v i)]
    field_simp
  set x : Fin g → ℚ := fun i => (xz i : ℚ) with hxdef
  have hxv : x = (D : ℚ) • v := funext fun i => by simp [hxdef, hx]
  have hxT : x ⬝ᵥ T *ᵥ x < 0 := by
    rw [hxv, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc]
    have : (0 : ℚ) < D := by exact_mod_cast hDpos
    exact mul_neg_of_pos_of_neg (by positivity) hv
  obtain ⟨i0, hi0⟩ : ∃ i0, xz i0 ≠ 0 := by
    by_contra h
    push Not at h
    have : x = 0 := funext fun i => by simp [hxdef, h i]
    rw [this] at hxT
    simp at hxT
  obtain ⟨i1, hi1⟩ := Fintype.exists_ne_of_one_lt_card (by simp; omega) i0
  set yz : Fin g → ℤ := Pi.single i0 (xz i1) - Pi.single i1 (xz i0) with hyz
  have hyx : yz ⬝ᵥ xz = 0 := by
    rw [hyz, sub_dotProduct, single_dotProduct, single_dotProduct]; ring
  set y : Fin g → ℚ := fun j => (yz j : ℚ) with hydef
  have hy1 : y i1 = -(xz i0 : ℚ) := by
    simp [hydef, hyz, Pi.single_apply, hi1]
  have hyy : 0 < y ⬝ᵥ y := by
    have hle : y i1 * y i1 ≤ y ⬝ᵥ y :=
      Finset.single_le_sum (f := fun j => y j * y j) (fun j _ => mul_self_nonneg _) (Finset.mem_univ i1)
    have hpos : 0 < y i1 * y i1 := by
      rw [hy1]
      have : (xz i0 : ℚ) ≠ 0 := by exact_mod_cast hi0
      exact mul_self_pos.mpr (neg_ne_zero.mpr this)
    linarith
  have hq : (y ⬝ᵥ y) * (x ⬝ᵥ T *ᵥ x) < 0 := mul_neg_of_pos_of_neg hyy hxT
  obtain ⟨k, hk⟩ := exists_nat_mul_quadratic_lt N hN T.trace (x ⬝ᵥ T.mulVec y + y ⬝ᵥ T.mulVec x)
    ((y ⬝ᵥ y) * (x ⬝ᵥ T.mulVec x)) c hq
  refine ⟨1 + ((N : ℤ) * k) • vecMulVec xz yz, ?_, ?_, ?_⟩
  · rw [← smul_vecMulVec, vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, dotProduct_smul,
      hyx, smul_zero, add_zero]
  · intro i j
    refine ⟨k * (xz i * yz j), ?_⟩
    simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    ring
  · have hmap : (1 + ((N : ℤ) * k) • vecMulVec xz yz).map (Int.cast : ℤ → ℚ) =
        1 + ((N : ℚ) * k) • vecMulVec x y := by
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
        Matrix.one_apply, hxdef, hydef]
      split_ifs <;> push_cast <;> ring
    rw [hmap, trace_transvection_conj]
    exact hk
end GlobalTheory
