-- Prove2me | solution 1 for OAI.Paper256.BlockPencil.G_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:16:26.276565+00:00
-- url     : https://prove2.me/submissions/f83380c8-2f7c-41d5-a37d-667edae0e2a6

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/BlockReduction.lean:L13-L28
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.BlockPencil.G_eq_zero. The node keeps its source
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
import Theorems.Thm_OAI_Paper256_linear_term_zero_of_quadratic_posSemidef

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

-- ---- from OAI.Analysis.HyperbolicCones.BlockReduction ----
namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256.BlockPencil

theorem G_eq_zero {K : Set Ambient} (P : BlockPencil K)
    (hSlice : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), (X : Mat 4 ℝ).PosDef →
      (((X, Z), y) ∈ K ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef))
    (y : Fin 3 → ℝ) : P.G y = 0 := by
  let Z0 : Sym 4 := ⟨phi y (1 : Mat 4 ℝ), phi_isHermitian y 1 Matrix.isHermitian_one⟩
  apply linear_term_zero_of_quadratic_posSemidef (P.E Z0) (P.G y)
  intro s
  have hm : (((1, s ^ 2 • Z0), s • y) : Ambient) ∈ K := by
    apply (hSlice 1 (s ^ 2 • Z0) (s • y) Matrix.PosDef.one).mpr
    simp [Z0, phi_scaling]
    exact Matrix.PosSemidef.zero
  have hp := (P.represents 1 (s ^ 2 • Z0) (s • y)).mp hm
  have hb := hp.submatrix Sum.inr
  convert hb using 1
  ext i j
  simp [Matrix.submatrix, Matrix.fromBlocks]

end Paper256.BlockPencil

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256 OAI.Paper256.BlockPencil
open Set Matrix
open scoped Matrix.Norms.L2Operator


theorem solution : type_of% @_root_.OAI.Paper256.BlockPencil.G_eq_zero := @_root_.OAI.Paper256.BlockPencil.G_eq_zero
