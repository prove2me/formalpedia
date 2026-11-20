-- Prove2me | solution 1 for HarlowTASI.factorizedCode_entropy
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-26T20:50:14.147001+00:00
-- url     : https://prove2.me/submissions/8b580d3c-b4d5-49e8-b915-88a782f0bca0

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras
import Theorems.Thm_HarlowTASI_factorizedCode_reducedStates
import Theorems.Thm_HarlowTASI_vonNeumannEntropy_isometry_conj
import Theorems.Thm_HarlowTASI_vonNeumannEntropy_blockDiagonal_sigma
import Theorems.Thm_HarlowTASI_vonNeumannEntropy_kronecker
import Theorems.Thm_HarlowTASI_vonNeumannEntropy_transpose
import Theorems.Thm_HarlowTASI_diagBlock_state_facts
import Theorems.Thm_HarlowTASI_trace_mul_blockScalarOp

open Matrix
open scoped Kronecker ComplexOrder
open HarlowTASI

lemma fce_trace_traceRight {A B : Type} [Fintype A] [Fintype B] (X : Matrix (A × B) (A × B) ℂ) :
    (traceRight X).trace = X.trace := by
  simp [traceRight, Matrix.trace, Fintype.sum_prod_type]

lemma fce_trace_traceLeft {A B : Type} [Fintype A] [Fintype B] (X : Matrix (A × B) (A × B) ℂ) :
    (traceLeft X).trace = X.trace := by
  simp [traceLeft, Matrix.trace, Fintype.sum_prod_type]
  exact Finset.sum_comm

lemma fce_herm_kron {p q : Type} [Fintype p] [Fintype q] {A : Matrix p p ℂ} {B : Matrix q q ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A ⊗ₖ B).IsHermitian := by
  unfold IsHermitian; rw [conjTranspose_kronecker, hA.eq, hB.eq]

/-- An empty block (`dr a = 0` or `drb a = 0`) has weight `0`. -/
lemma fce_weight_empty {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    (ρ : Matrix C C ℂ) (a : Fin N) (h : ¬ (0 < dr a ∧ 0 < drb a)) :
    blockWeight U ρ a = 0 := by
  have : IsEmpty (Fin (dr a) × Fin (drb a)) := by
    rcases Nat.eq_zero_or_pos (dr a) with h0 | h0
    · have : IsEmpty (Fin (dr a)) := by rw [h0]; infer_instance
      infer_instance
    · have h1 : drb a = 0 := by omega
      have : IsEmpty (Fin (drb a)) := by rw [h1]; infer_instance
      infer_instance
  simp [blockWeight, Matrix.trace]

theorem solution {R Rb C : Type} [Fintype R] [DecidableEq R]
    [Fintype Rb] [DecidableEq Rb] [Fintype C] [DecidableEq C]
    (V : Matrix (R × Rb) C ℂ)
    (N : ℕ) (dr drb : Fin N → ℕ) (U : Matrix (BlockIndex N dr drb) C ℂ)
    (hU : IsUnitaryMatrix U)
    (m mb : Fin N → ℕ) (χ : ∀ a, Matrix (Fin (m a)) (Fin (mb a)) ℂ)
    (WR : Matrix R (Σ a : Fin N, Fin (dr a) × Fin (m a)) ℂ)
    (WRb : Matrix Rb (Σ a : Fin N, Fin (mb a) × Fin (drb a)) ℂ)
    (hWR : IsIsometry WR) (hWRb : IsIsometry WRb)
    (hχ : ∀ a, 0 < dr a → 0 < drb a → (χ a * (χ a)ᴴ).trace = 1)
    (hVU : ∀ (x : R) (y : Rb) (a : Fin N) (i : Fin (dr a)) (j : Fin (drb a)),
        (V * Uᴴ) (x, y) ⟨a, (i, j)⟩ =
          ∑ k, ∑ l, χ a k l * WR x ⟨a, (i, k)⟩ * WRb y ⟨a, (l, j)⟩)
    (ρ : Matrix C C ℂ) (hρ : IsDensityMatrix ρ) :
    ((vonNeumannEntropy (traceRight (V * ρ * Vᴴ)) : ℝ) : ℂ) =
        (ρ * (Uᴴ * blockScalarOp (dr := dr) (drb := drb)
          (fun a => ((vonNeumannEntropy (χ a * (χ a)ᴴ) : ℝ) : ℂ)) * U)).trace +
        ((algebraicEntropyLeft U ρ : ℝ) : ℂ) ∧
    ((vonNeumannEntropy (traceLeft (V * ρ * Vᴴ)) : ℝ) : ℂ) =
        (ρ * (Uᴴ * blockScalarOp (dr := dr) (drb := drb)
          (fun a => ((vonNeumannEntropy ((χ a)ᴴ * χ a) : ℝ) : ℂ)) * U)).trace +
        ((algebraicEntropyRight U ρ : ℝ) : ℂ) := by
  obtain ⟨hL, hRt⟩ :=
    factorizedCode_reducedStates V N dr drb U hU m mb χ WR WRb hWR hWRb hVU ρ
  have hb := fun a => diagBlock_state_facts U ρ hρ.1 a
  set p := blockWeight U ρ with hp
  -- the factor `Tr χ χ†` (resp. `Tr χ† χ`) only matters on nonempty blocks, where it is `1`
  have hnorm : ∀ a, ∀ s : ℝ, ((χ a * (χ a)ᴴ).trace.re) * (Real.negMulLog (p a) + p a * s)
      = Real.negMulLog (p a) + p a * s := by
    intro a s
    by_cases h : 0 < dr a ∧ 0 < drb a
    · rw [hχ a h.1 h.2]; simp
    · rw [hp, fce_weight_empty U ρ a h]; simp
  have hnorm' : ∀ a, ∀ s : ℝ, ((((χ a)ᴴ * χ a)ᵀ).trace.re) * (Real.negMulLog (p a) + p a * s)
      = Real.negMulLog (p a) + p a * s := by
    intro a s
    rw [trace_transpose, trace_mul_comm]; exact hnorm a s
  have keyL : ∀ a, vonNeumannEntropy (traceRight (diagBlock U ρ a) ⊗ₖ (χ a * (χ a)ᴴ)) =
      Real.negMulLog (p a) + p a * vonNeumannEntropy (blockStateLeft U ρ a) +
        p a * vonNeumannEntropy (χ a * (χ a)ᴴ) := by
    intro a
    rw [vonNeumannEntropy_kronecker _ _ (hb a).2.1 (isHermitian_mul_conjTranspose_self _),
      (hb a).2.2.2.1, hnorm, fce_trace_traceRight, (hb a).1, Complex.ofReal_re]
  have keyR : ∀ a, vonNeumannEntropy (((χ a)ᴴ * χ a)ᵀ ⊗ₖ traceLeft (diagBlock U ρ a)) =
      Real.negMulLog (p a) + p a * vonNeumannEntropy (blockStateRight U ρ a) +
        p a * vonNeumannEntropy ((χ a)ᴴ * χ a) := by
    intro a
    rw [vonNeumannEntropy_kronecker _ _ (isHermitian_conjTranspose_mul_self _).transpose
      (hb a).2.2.1, (hb a).2.2.2.2, hnorm', fce_trace_traceLeft, (hb a).1, Complex.ofReal_re,
      vonNeumannEntropy_transpose]
    ring
  refine ⟨?_, ?_⟩
  · rw [hL, vonNeumannEntropy_isometry_conj _ hWR,
      vonNeumannEntropy_blockDiagonal_sigma _
        (fun a => fce_herm_kron (hb a).2.1 (isHermitian_mul_conjTranspose_self _)),
      trace_mul_blockScalarOp]
    simp only [keyL, (hb _).1, algebraicEntropyLeft, ← hp]
    push_cast
    simp only [Finset.sum_add_distrib]
    ring_nf
    simp only [mul_comm]
  · rw [hRt, vonNeumannEntropy_isometry_conj _ hWRb,
      vonNeumannEntropy_blockDiagonal_sigma _
        (fun a => fce_herm_kron (isHermitian_conjTranspose_mul_self _).transpose (hb a).2.2.1),
      trace_mul_blockScalarOp]
    simp only [keyR, (hb _).1, algebraicEntropyRight, ← hp]
    push_cast
    simp only [Finset.sum_add_distrib]
    ring_nf
    simp only [mul_comm]
