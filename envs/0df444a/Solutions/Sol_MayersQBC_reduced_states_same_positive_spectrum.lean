-- Prove2me | solution 1 for MayersQBC.reduced_states_same_positive_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T20:56:21.954364+00:00
-- url     : https://prove2.me/submissions/79150946-7d5d-4c47-91f4-5b99b73f0f05

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement
open QAlgorithms

open scoped Matrix ComplexConjugate

/-- `finrank` of the `μ`-eigenspace of `X` is `card - rank (X - μ I)` (rank–nullity). -/
private lemma finrank_eigenspace_add_rank {n : Type} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (μ : ℂ) :
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' X) μ) + (X - μ • 1).rank =
      Fintype.card n := by
  have hker : Module.End.eigenspace (Matrix.toLin' X) μ =
      LinearMap.ker (Matrix.toLin' (X - μ • 1)) := by
    rw [Module.End.eigenspace_def, map_sub, map_smul, Matrix.toLin'_one]
    rfl
  rw [hker, Matrix.rank, ← Matrix.toLin'_apply', add_comm,
    LinearMap.finrank_range_add_finrank_ker, Module.finrank_fintype_fun_eq_card]

/-- Transposition does not change the dimension of an eigenspace. -/
private lemma finrank_eigenspace_transpose {n : Type} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) (μ : ℂ) :
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' Xᵀ) μ) =
      Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' X) μ) := by
  have h1 := finrank_eigenspace_add_rank Xᵀ μ
  have h2 := finrank_eigenspace_add_rank X μ
  have hr : (Xᵀ - μ • 1).rank = (X - μ • 1).rank := by
    rw [← Matrix.rank_transpose (X - μ • 1), Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one]
  omega

/-- For `μ ≠ 0`, `Nᴴ` maps the `μ`-eigenspace of `N Nᴴ` injectively into that of `Nᴴ N`. -/
private lemma finrank_eigenspace_mul_le {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (N : Matrix m n ℂ) (μ : ℂ) (hμ : μ ≠ 0) :
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' (N * Nᴴ)) μ) ≤
      Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' (Nᴴ * N)) μ) := by
  have hmap : ∀ v ∈ Module.End.eigenspace (Matrix.toLin' (N * Nᴴ)) μ,
      Matrix.toLin' Nᴴ v ∈ Module.End.eigenspace (Matrix.toLin' (Nᴴ * N)) μ := by
    intro v hv
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hv ⊢
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
      hv, Matrix.mulVec_smul]
  let f := (Matrix.toLin' Nᴴ).restrict hmap
  refine LinearMap.finrank_le_finrank_of_injective (f := f) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hv0 : Nᴴ *ᵥ (v : m → ℂ) = 0 := by
    have := congrArg Subtype.val hv
    simpa [f, LinearMap.restrict_apply, Matrix.toLin'_apply] using this
  have hv1 := v.2
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hv0,
    Matrix.mulVec_zero] at hv1
  have : (v : m → ℂ) = 0 := by
    have h := hv1.symm
    rcases smul_eq_zero.mp h with h' | h'
    · exact absurd h' hμ
    · exact h'
  exact Subtype.ext this

theorem solution {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (ψ : EuclideanSpace ℂ (A × B)) (μ : ℝ) (hμ : 0 < μ) :
    Module.finrank ℂ
        (Module.End.eigenspace (Matrix.toLin' (traceRight (pureDensity ψ))) (μ : ℂ)) =
      Module.finrank ℂ
        (Module.End.eigenspace (Matrix.toLin' (traceLeft (pureDensity ψ))) (μ : ℂ)) := by
  -- the coefficient matrix of `ψ`
  let M : Matrix A B ℂ := Matrix.of fun a b => ψ (a, b)
  have hA : traceRight (pureDensity ψ) = M * Mᴴ := by
    ext a a'
    simp [traceRight, pureDensity, M, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hB : traceLeft (pureDensity ψ) = (Mᴴ * M)ᵀ := by
    ext b b'
    simp [traceLeft, pureDensity, M, Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm]
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ.ne'
  rw [hA, hB, finrank_eigenspace_transpose]
  refine le_antisymm (finrank_eigenspace_mul_le M _ hμ') ?_
  have h := finrank_eigenspace_mul_le Mᴴ (μ : ℂ) hμ'
  rwa [Matrix.conjTranspose_conjTranspose] at h
