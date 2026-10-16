-- Prove2me | solution 1 for OAI.Paper256.BlockPencil.scaled_posSemidef_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:18:20.46392+00:00
-- url     : https://prove2.me/submissions/da9dfdd4-b127-48e0-81e4-42919809efdd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/BlockScaling.lean:L24-L46
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.BlockPencil.scaled_posSemidef_iff. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Theorems.Thm_OAI_Paper256_BlockPencil_G_eq_zero

-- ---- from OAI.Analysis.HyperbolicCones.MatrixBasic ----
namespace OAI

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

universe u

namespace Paper256

theorem qMatrix_smul {R : Type u} [CommRing R] (y : Fin 3 → R) (s : R) :
    qMatrix (s • y) = s ^ 2 • qMatrix y := by
  ext i j
  by_cases h : i = j <;> simp [qMatrix, h, mul_pow] <;> ring

theorem phi_scaling_general {R : Type u} [CommRing R]
    (y : Fin 3 → R) (s : R) (X : Mat 4 R) :
    phi (s • y) X = s ^ 2 • phi y X := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [phi, qMatrix_smul, Matrix.trace, Matrix.mul_apply, Matrix.submatrix,
      ← Finset.mul_sum, mul_left_comm, mul_assoc]

theorem phi_scaling (y : Fin 3 → ℝ) (s : ℝ) (X : Mat 4 ℝ) :
    phi (s • y) X = s ^ 2 • phi y X :=
  phi_scaling_general y s X

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.ScalingAlgebra ----
namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

theorem blockScalar_transpose (a c : ℕ) (s : ℝ) :
    (blockScalar a c s)ᵀ = blockScalar a c s := by
  simp [blockScalar, Matrix.fromBlocks_transpose]

theorem blockScalar_isUnit (a c : ℕ) (s : ℝ) (hs : s ≠ 0) :
    IsUnit (blockScalar a c s) := by
  refine ⟨⟨blockScalar a c s, blockScalar a c s⁻¹, ?_, ?_⟩, rfl⟩ <;>
    simp [blockScalar, Matrix.fromBlocks_multiply, smul_smul, hs]

theorem block_scaling_identity {a c : ℕ} (D A F : Mat a ℝ)
    (B C : Matrix (Fin a) (Fin c) ℝ) (E : Mat c ℝ) (s : ℝ) (hs : s ≠ 0) :
    blockScalar a c s⁻¹ *
        Matrix.fromBlocks (D + s ^ 2 • F + s • A) (s ^ 2 • C + s • B)
          (s ^ 2 • C + s • B)ᵀ (s ^ 2 • E) * blockScalar a c s⁻¹ =
      Matrix.fromBlocks (D + s • A + s ^ 2 • F) (B + s • C) (B + s • C)ᵀ E := by
  simp only [blockScalar, Matrix.fromBlocks_multiply]
  ext (i | i) (j | j) <;>
    simp [Matrix.fromBlocks, Matrix.transpose_add, Matrix.transpose_smul,
      mul_add, smul_smul] <;>
    field_simp <;> ring

theorem posSemidef_smul_iff {ι : Type u} [Fintype ι] {H : Matrix ι ι ℝ} {s : ℝ}
    (hs : 0 < s) : (s • H).PosSemidef ↔ H.PosSemidef := by
  constructor
  · intro h
    have hh := h.smul (inv_pos.mpr hs).le
    simpa only [smul_smul, inv_mul_cancel₀ hs.ne', one_smul] using hh
  · exact fun h => h.smul hs.le

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.BlockScaling ----
namespace OAI

noncomputable section

open Matrix Set
open scoped Matrix.Norms.L2Operator

namespace Paper256.BlockPencil

theorem scaled_congruence {K : Set Ambient} (P : BlockPencil K)
    (hSlice : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), (X : Mat 4 ℝ).PosDef →
      (((X, Z), y) ∈ K ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef))
    (X Z : Sym 4) (y : Fin 3 → ℝ) (s : ℝ) (hs : s ≠ 0) :
    blockScalar P.a P.c s⁻¹ * P.matrix X (s ^ 2 • Z) (s • y) * blockScalar P.a P.c s⁻¹ =
      P.scaled X Z y s := by
  have hG := P.G_eq_zero hSlice y
  simpa [matrix, scaled, hG] using
    block_scaling_identity (P.D X : Mat P.a ℝ) (P.A y : Mat P.a ℝ)
      (P.F Z : Mat P.a ℝ) (P.B y) (P.C Z) (P.E Z : Mat P.c ℝ) s hs

theorem scaled_posSemidef_iff {K : Set Ambient} (P : BlockPencil K)
    (hSlice : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), (X : Mat 4 ℝ).PosDef →
      (((X, Z), y) ∈ K ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef))
    (X Z : Sym 4) (y : Fin 3 → ℝ) (hX : (X : Mat 4 ℝ).PosDef) (s : ℝ) (hs : s ≠ 0) :
    (P.scaled X Z y s).PosSemidef ↔
      ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef := by
  let R := blockScalar P.a P.c s⁻¹
  have hR : IsUnit R := blockScalar_isUnit P.a P.c s⁻¹ (inv_ne_zero hs)
  have hRt : Rᴴ = R := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      blockScalar_transpose P.a P.c s⁻¹
  calc
    (P.scaled X Z y s).PosSemidef ↔ (P.matrix X (s ^ 2 • Z) (s • y)).PosSemidef := by
      rw [← P.scaled_congruence hSlice X Z y s hs]
      simpa only [Matrix.star_eq_conjTranspose, hRt] using
        hR.posSemidef_star_right_conjugate_iff (x := P.matrix X (s ^ 2 • Z) (s • y))
    _ ↔ (((X, s ^ 2 • Z), s • y) : Ambient) ∈ K :=
      (P.represents X (s ^ 2 • Z) (s • y)).symm
    _ ↔ (s ^ 2 • ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹)).PosSemidef := by
      rw [hSlice X (s ^ 2 • Z) (s • y) hX]
      simp only [selfAdjoint.val_smul, phi_scaling, smul_sub]
    _ ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef := by
      exact posSemidef_smul_iff (sq_pos_of_ne_zero hs)

end Paper256.BlockPencil

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256 OAI.Paper256.BlockPencil
open Matrix Set
open scoped Matrix.Norms.L2Operator


theorem solution : type_of% @_root_.OAI.Paper256.BlockPencil.scaled_posSemidef_iff := @_root_.OAI.Paper256.BlockPencil.scaled_posSemidef_iff
