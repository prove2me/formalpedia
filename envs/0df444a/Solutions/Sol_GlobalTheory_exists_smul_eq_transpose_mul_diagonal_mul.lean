-- Prove2me | solution 1 for GlobalTheory.exists_smul_eq_transpose_mul_diagonal_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:20.370838+00:00
-- url     : https://prove2.me/submissions/61559f08-aa72-456a-ab5d-aaa3949864dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsSmulEqTransposeMulDiagonalMul
import Theorems.Thm_GlobalTheory_exists_rat_eq_transpose_mul_diagonal_mul
import Theorems.Thm_GlobalTheory_exists_pos_nat_mul_eq_intCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open scoped BigOperators
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℤ), (A.map (fun x : ℤ => (x : ℝ))).PosDef → ∃ (N : ℕ) (c : Fin n → ℕ) (l : Matrix (Fin n) (Fin n) ℤ), 0 < N ∧ (∀ i, 0 < c i) ∧ l.det ≠ 0 ∧ (N : ℤ) • A = lᵀ * Matrix.diagonal (fun i => (c i : ℤ)) * l) := by
  intro n A hA
  have hs : (A.map (fun x : ℤ => (x : ℚ))).IsSymm := by
    ext i j
    have := hA.isHermitian.apply j i
    simp only [Matrix.map_apply, star_trivial, Int.cast_inj] at this
    simp [this]
  have hp : ∀ x : Fin n → ℚ, x ≠ 0 → 0 < x ⬝ᵥ (A.map (fun x : ℤ => (x : ℚ))) *ᵥ x := by
    intro x hx
    have hx' : (fun i => (x i : ℝ)) ≠ 0 := by
      intro h
      apply hx
      ext i
      have := congrFun h i
      simpa using this
    have h := hA.dotProduct_mulVec_pos hx'
    have h2 : star (fun i => (x i : ℝ)) ⬝ᵥ (A.map (fun x : ℤ => (x : ℝ))) *ᵥ (fun i => (x i : ℝ))
        = ((x ⬝ᵥ (A.map (fun x : ℤ => (x : ℚ))) *ᵥ x : ℚ) : ℝ) := by
      simp [dotProduct, Matrix.mulVec]
    rw [h2] at h
    exact_mod_cast h
  obtain ⟨d, Q, hd, hQ, hAQ⟩ := exists_rat_eq_transpose_mul_diagonal_mul _ hs hp
  obtain ⟨a, g, ha, hg⟩ := exists_pos_nat_mul_eq_intCast (fun p : Fin n × Fin n => Q p.1 p.2)
  obtain ⟨b, k, hb, hk⟩ := exists_pos_nat_mul_eq_intCast d
  have hkpos : ∀ i, 0 < k i := by
    intro i
    have : (0 : ℚ) < k i := by
      rw [hk i]
      exact mul_pos (by exact_mod_cast hb) (hd i)
    exact_mod_cast this
  let l : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j => g (i, j)
  have hl : l.map (Int.castRingHom ℚ) = (a : ℚ) • Q := by
    ext i j
    simp [l, hg]
  have hc : (Matrix.diagonal fun i => (((k i).toNat : ℕ) : ℤ)).map (Int.castRingHom ℚ)
      = (b : ℚ) • Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
      rw [Int.toNat_of_nonneg (hkpos i).le]
      exact hk i
    · simp [Matrix.diagonal_apply_ne _ hij]
  refine ⟨a * b * a, fun i => (k i).toNat, l, by positivity, fun i => ?_, ?_, ?_⟩
  · have := hkpos i
    show 0 < (k i).toNat
    omega
  · intro h0
    have h1 : (l.map (Int.castRingHom ℚ)).det = 0 := by
      have := (Int.castRingHom ℚ).map_det l
      rw [RingHom.mapMatrix_apply, h0] at this
      simpa using this.symm
    rw [hl, Matrix.det_smul] at h1
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    exact (mul_ne_zero (pow_ne_zero _ ha') hQ) h1
  · apply Matrix.map_injective (f := Int.castRingHom ℚ) (Int.cast_injective (α := ℚ))
    simp only
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hl, hc]
    have : (((a * b * a : ℕ) : ℤ) • A).map (Int.castRingHom ℚ)
        = ((a : ℚ) * b * a) • A.map (fun x : ℤ => (x : ℚ)) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, eq_intCast]
      push_cast
      ring
    rw [this, hAQ]
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    ring
end GlobalTheory
