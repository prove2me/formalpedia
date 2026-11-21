-- Prove2me | solution 1 for MiLAC.HybridCouplersPhaseShifters.implementable_dft
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:54.144172+00:00
-- url     : https://prove2.me/submissions/fae0c813-331c-470c-9d12-44c8a2c75a22

module
public import Definitions.Def_LeanPool_MicrowaveNetworks_Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Definitions.Def_LeanPool_MicrowaveNetworks_HybridCouplersPhaseShifters
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_implementableOn_iff
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_ImplementableOn_mul
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_ImplementableOn_submatrix_symm
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_implementable_if_block
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_IsLayered_mul
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_butterfly_eq_block
public import Theorems.Thm_MiLAC_HybridCouplersPhaseShifters_dft_exp
public import Theorems.Thm_MiLAC_castAdd_ne_natAdd
public import Theorems.Thm_MiLAC_natAdd_ne_castAdd
public import Theorems.Thm_MiLAC_parallel_castAdd_castAdd
public import Theorems.Thm_MiLAC_parallel_castAdd_natAdd
public import Theorems.Thm_MiLAC_parallel_natAdd_castAdd
public import Theorems.Thm_MiLAC_parallel_natAdd_natAdd
attribute [local simp] MiLAC.castAdd_ne_natAdd
attribute [local simp] MiLAC.natAdd_ne_castAdd
attribute [local simp] MiLAC.parallel_castAdd_castAdd
attribute [local simp] MiLAC.parallel_castAdd_natAdd
attribute [local simp] MiLAC.parallel_natAdd_castAdd
attribute [local simp] MiLAC.parallel_natAdd_natAdd



set_option autoImplicit true
@[expose] public section
public section
open MiLAC MiLAC.HybridCouplersPhaseShifters
namespace MiLAC.HybridCouplersPhaseShifters
theorem _root_.solution (L : ℕ) : Implementable (dft (2 ^ L)) := by
  induction L with
  | zero =>
      have h : dft (2 ^ 0) = interconnection := by
        ext i j
        fin_cases i
        fin_cases j
        simp [dft, interconnection]
      rw [h]
      exact Implementable.ic
  | succ L ih =>
      -- rows are indexed by (a, i) ↦ i + 2^L a, columns by (b, k) ↦ b + 2 k
      let out : Fin 2 × Fin (2 ^ L) ≃ Fin (2 ^ (L + 1)) :=
        finProdFinEquiv.trans (finCongr (by ring))
      let inp : Fin 2 × Fin (2 ^ L) ≃ Fin (2 ^ (L + 1)) :=
        (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (finCongr (by ring)))
      -- butterflies, and two DFTs of half size in parallel
      let B : Matrix (Fin 2 × Fin (2 ^ L)) (Fin 2 × Fin (2 ^ L)) ℂ :=
        Matrix.blockDiagonal (butterfly L)
      let K : Matrix (Fin 2 × Fin (2 ^ L)) (Fin 2 × Fin (2 ^ L)) ℂ :=
        Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _)
          (Matrix.blockDiagonal (fun _ : Fin 2 => dft (2 ^ L)))
      have hB : ImplementableOn B := by
        refine ImplementableOn.blockDiagonal _ _ fun i => ?_
        rw [implementableOn_iff, butterfly_eq_block]
        exact implementable_if_block _ _ _
      have hK : ImplementableOn K :=
        (ImplementableOn.blockDiagonal _ _
          fun _ => (implementableOn_iff _).2 ih).reindex _
      have hBK : ∀ a b : Fin 2, ∀ i k : Fin (2 ^ L),
          (B * K) (a, i) (b, k) = butterfly L i a b * dft (2 ^ L) i k := by
        intro a b i k
        rw [Matrix.mul_apply, Fintype.sum_prod_type]
        simp [B, K, Matrix.blockDiagonal_apply, Matrix.reindex_apply]
      have hdft : dft (2 ^ (L + 1)) = (B * K).submatrix out.symm inp.symm := by
        ext x y
        obtain ⟨⟨a, i⟩, rfl⟩ := out.surjective x
        obtain ⟨⟨b, k⟩, rfl⟩ := inp.surjective y
        rw [Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, hBK]
        have hx : ((out (a, i) : ℕ) : ℂ) = (i : ℂ) + 2 ^ L * (a : ℕ) := by
          simp [out, finProdFinEquiv]
        have hy : ((inp (b, k) : ℕ) : ℂ) = ((b : ℕ) : ℂ) + 2 * (k : ℕ) := by
          simp [inp, finProdFinEquiv]
        have hs : ((Real.sqrt ((2 ^ (L + 1) : ℕ) : ℝ)) : ℂ) =
            (Real.sqrt 2 : ℂ) * (Real.sqrt ((2 ^ L : ℕ) : ℝ) : ℂ) := by
          rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num)]
          push_cast
          ring_nf
        simp only [dft, butterfly]
        rw [hx, hy, hs]
        push_cast
        rw [dft_exp]
        ring
      rw [hdft]
      exact (hB.mul hK).submatrix_symm out inp
end MiLAC.HybridCouplersPhaseShifters
