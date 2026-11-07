-- Prove2me | solution 1 for ModernConvex.Relaxations.quadform_eq_schurForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:37:51.029118+00:00
-- url     : https://prove2.me/submissions/54c9b30a-d654-4ca0-b8dd-fc153f8d0d7a

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_ModernConvex_SchurForm

/-!
# Schur elimination at a positive pivot

For a symmetric matrix `M` and an index `i` with `M i i > 0`, the quadratic form splits by
completing the square:

  `v ⬝ᵥ (M *ᵥ v) = a * (v i + (1/a) * Σ_{j≠i} M i j v j)^2 + Q v`,

where `a = M i i` and `Q` is the **Schur form** on the remaining coordinates,

  `Q v = Σ_{j,k≠i} v j v k M j k - (1/a) * (Σ_{j≠i} M i j v j)^2`.

Two consequences, which are the two arms of the PSD oracle's elimination step:

* if `Q` is nonnegative then `M` is positive semidefinite (the square term is nonnegative);
* if some `Q` is negative, then `M` is not positive semidefinite — indeed its value is unchanged
  when `v i` is adjusted, and choosing `v i = -(1/a) Σ_{j≠i} M i j v j` kills the square.

This is the elimination step of the rational PSD oracle, stated on quadratic forms so that no
matrix inverse of a block is needed.
-/

open Matrix
open scoped BigOperators MatrixOrder

namespace ModernConvex.Relaxations

/-- The Schur form does not depend on the `i`-th coordinate of `v`. -/
theorem schurForm_update_proof {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (v : Fin n → ℝ) (s : ℝ) :
    schurForm M i (Function.update v i s) = schurForm M i v := by
  have h : ∀ j ∈ Finset.univ.erase i, Function.update v i s j = v j := by
    intro j hj
    exact Function.update_of_ne (Finset.ne_of_mem_erase hj) s v
  have hinner : ∀ j ∈ Finset.univ.erase i,
      (∑ k ∈ Finset.univ.erase i, Function.update v i s j * (M j k * Function.update v i s k))
        = ∑ k ∈ Finset.univ.erase i, v j * (M j k * v k) := by
    intro j hj
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [h j hj, h k hk]
  have houter : ∀ j ∈ Finset.univ.erase i, M i j * Function.update v i s j = M i j * v j := by
    intro j hj
    rw [h j hj]
  simp only [schurForm]
  rw [Finset.sum_congr rfl hinner, Finset.sum_congr rfl houter]

/-- **Completing the square.** -/
theorem quadform_eq_schurForm_proof {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (i : Fin n) (ha : M i i ≠ 0) (v : Fin n → ℝ) :
    v ⬝ᵥ (M *ᵥ v)
      = M i i * (v i + (M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i, M i j * v j)) ^ 2
        + schurForm M i v := by
  have hsymm : ∀ j : Fin n, M j i = M i j := by
    intro j
    simpa using (hM.apply j i).symm
  -- expand the left-hand side as a double sum
  have hL : v ⬝ᵥ (M *ᵥ v) = ∑ p, ∑ q, v p * (M p q * v q) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  rw [hL, schurForm]
  -- split the outer sum at `i`
  have houter : ∑ p, ∑ q, v p * (M p q * v q)
      = (∑ q, v i * (M i q * v q))
        + ∑ p ∈ Finset.univ.erase i, ∑ q, v p * (M p q * v q) := by
    rw [← Finset.add_sum_erase Finset.univ (fun p => ∑ q, v p * (M p q * v q))
      (Finset.mem_univ i)]
  -- split the `i`-th inner sum
  have hinner_i : ∑ q, v i * (M i q * v q)
      = v i * (M i i * v i) + ∑ q ∈ Finset.univ.erase i, v i * (M i q * v q) := by
    rw [← Finset.add_sum_erase Finset.univ (fun q => v i * (M i q * v q))
      (Finset.mem_univ i)]
  -- split each remaining inner sum
  have hinner_rest : ∀ p : Fin n, ∑ q, v p * (M p q * v q)
      = v p * (M p i * v i) + ∑ q ∈ Finset.univ.erase i, v p * (M p q * v q) := by
    intro p
    rw [← Finset.add_sum_erase Finset.univ (fun q => v p * (M p q * v q))
      (Finset.mem_univ i)]
  rw [houter, hinner_i]
  rw [Finset.sum_congr rfl (fun p (_ : p ∈ Finset.univ.erase i) => hinner_rest p)]
  rw [Finset.sum_add_distrib]
  -- identify the two cross terms with `v i * P`
  have hA : ∑ q ∈ Finset.univ.erase i, v i * (M i q * v q)
      = v i * ∑ j ∈ Finset.univ.erase i, M i j * v j := by
    rw [Finset.mul_sum]
  have hB : ∑ p ∈ Finset.univ.erase i, v p * (M p i * v i)
      = v i * ∑ j ∈ Finset.univ.erase i, M i j * v j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hsymm p]
    ring
  -- expand the right-hand side
  have hR : M i i * (v i + (M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i, M i j * v j)) ^ 2
      + ((∑ p ∈ Finset.univ.erase i, ∑ q ∈ Finset.univ.erase i, v p * (M p q * v q))
          - (M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i, M i j * v j) ^ 2)
      = M i i * v i ^ 2 + 2 * v i * (∑ j ∈ Finset.univ.erase i, M i j * v j)
        + ∑ p ∈ Finset.univ.erase i, ∑ q ∈ Finset.univ.erase i, v p * (M p q * v q) := by
    field_simp
    ring
  rw [hA, hB, hR]
  ring

/-- **PSD from a nonnegative Schur form.** At a positive pivot, if the Schur form is nonnegative
then the whole quadratic form is. -/
theorem posSemidef_of_schurForm_proof {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (i : Fin n) (ha : 0 < M i i) (h : ∀ w : Fin n → ℝ, 0 ≤ schurForm M i w) :
    M.PosSemidef := by
  refine posSemidef_iff_dotProduct_mulVec.mpr ⟨hM, fun v => ?_⟩
  rw [star_trivial, quadform_eq_schurForm_proof hM i ha.ne' v]
  have hsq : (0:ℝ) ≤ (v i + (M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i, M i j * v j)) ^ 2 :=
    sq_nonneg _
  have hnn : 0 ≤ M i i * (v i + (M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i, M i j * v j)) ^ 2 :=
    mul_nonneg (le_of_lt ha) hsq
  have h2 := h v
  linarith

/-- **A negative Schur form gives a certificate.** At a positive pivot, a negative value of the
Schur form extends to a direction of negative quadratic form for `M`, by choosing the `i`-th
coordinate to cancel the square. -/
theorem exists_neg_of_schurForm_proof {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (i : Fin n) (ha : 0 < M i i) (w : Fin n → ℝ) (hw : schurForm M i w < 0) :
    ∃ v : Fin n → ℝ, v ⬝ᵥ (M *ᵥ v) < 0 := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = -(M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i, M i j * w j) := ⟨_, rfl⟩
  refine ⟨Function.update w i c, ?_⟩
  have hfix : ∀ j ∈ Finset.univ.erase i, Function.update w i c j = w j := by
    intro j hj
    exact Function.update_of_ne (Finset.ne_of_mem_erase hj) c w
  have hcancel : c + (M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i, M i j * Function.update w i c j) = 0 := by
    have hsum : (∑ j ∈ Finset.univ.erase i, M i j * Function.update w i c j)
        = ∑ j ∈ Finset.univ.erase i, M i j * w j :=
      Finset.sum_congr rfl fun j hj => by rw [hfix j hj]
    rw [hsum, hc]
    ring
  rw [quadform_eq_schurForm_proof hM i ha.ne', Function.update_self, hcancel,
    zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero, zero_add, schurForm_update_proof]
  exact hw

end ModernConvex.Relaxations

open ModernConvex.Relaxations in
theorem solution {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian)
    (i : Fin n) (ha : M i i ≠ 0) (v : Fin n → ℝ) :
    v ⬝ᵥ (M *ᵥ v)
      = M i i * (v i + (M i i)⁻¹ * (∑ j ∈ Finset.univ.erase i, M i j * v j)) ^ 2
        + schurForm M i v :=
  ModernConvex.Relaxations.quadform_eq_schurForm_proof hM i ha v
