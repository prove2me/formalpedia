-- Prove2me | solution 1 for OAI.TriangularHilbert.MatrixEnergy.rowStar_mul_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:24:24.660989+00:00
-- url     : https://prove2.me/submissions/eb9379b8-e229-4741-8d72-6d66096c96d6

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
universe uι
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]
theorem h44_blocks_mul {κ : Type*} [Fintype κ] (M N : Matrix Three Three (Matrix κ κ ℂ)) :
    blocks M * blocks N = blocks (M * N) :=
  (map_mul (Matrix.compRingEquiv Three κ ℂ) M N).symm

theorem h44_blocks_ct {κ : Type*} (M : Matrix Three Three (Matrix κ κ ℂ)) :
    (blocks M)ᴴ = blocks Mᴴ := by
  ext ⟨a, i⟩ ⟨b, j⟩; simp [blocks, Matrix.conjTranspose_apply, Matrix.comp_apply]

theorem h44_vP {κ : Type*} [DecidableEq κ] (v : Three) :
    (vertexProj v : Matrix (BlockSpace κ) (BlockSpace κ) ℂ) =
      blocks (Matrix.diagonal (fun w => if w = v then (1 : Matrix κ κ ℂ) else 0)) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp only [vertexProj, blocks, Matrix.comp_apply, Matrix.diagonal_apply, Prod.mk.injEq]
  by_cases hab : a = b <;> by_cases hij : i = j <;> by_cases hv : a = v <;> simp_all [Matrix.one_apply]

theorem solution (A : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar A v * (rowStar A v)ᴴ =
      blockD (fun w => if w = v then centerGram A v else 0) := by
  rw [rowStar, triangle, h44_vP, h44_blocks_mul, h44_blocks_ct, h44_blocks_mul, blockD]
  congr 1
  funext w w'
  fin_cases v <;> fin_cases w <;> fin_cases w' <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose, centerGram, triangleBlocks]

