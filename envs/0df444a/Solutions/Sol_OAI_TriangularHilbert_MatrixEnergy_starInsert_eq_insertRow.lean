-- Prove2me | solution 1 for OAI.TriangularHilbert.MatrixEnergy.starInsert_eq_insertRow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:15:14.550986+00:00
-- url     : https://prove2.me/submissions/375dd48a-54c8-411d-ba08-b779503256ef

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/MatrixSupport.lean:L1741-L1756
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.MatrixEnergy.starInsert_eq_insertRow. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport

-- ---- from OAI.Analysis.TriangularHilbert.MatrixSupport ----
namespace OAI

universe uι uκ uX uμ

section
open scoped BigOperators
noncomputable section
namespace TriangularHilbert.MatrixEnergy

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace InnerProductSpace

end TriangularHilbert.MatrixEnergy

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary
namespace TriangularHilbert.MatrixEnergy

variable {ι : Type uι} [Fintype ι]

variable [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem blocks_mul (A B : Matrix Three Three (Matrix ι ι ℂ)) :
    blocks (A * B) = blocks A * blocks B := by
  exact (Matrix.compRingEquiv Three ι ℂ).map_mul A B

omit [Fintype ι] [DecidableEq ι] in
theorem blocks_star (A : Matrix Three Three (Matrix ι ι ℂ)) :
    blocks Aᴴ = (blocks A)ᴴ := rfl

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary MeasureTheory Filter
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma rowStar_blocks (W : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar W v = blocks (fun a b => if a = v then triangleBlocks W a b else 0) := by
  ext a b
  rcases a with ⟨a, i⟩
  rcases b with ⟨b, j⟩
  simp only [rowStar, vertexProj, Matrix.diagonal_mul, triangle, blocks, Matrix.comp_apply]
  change (if a = v then (1 : ℂ) else 0) * triangleBlocks W a b i j =
    (if a = v then triangleBlocks W a b else 0) i j
  split_ifs <;> simp

lemma starInsert_eq_insertRow (W D : Three → Matrix ι ι ℂ) (v : Three) :
    starInsert W D v = insertRow (triangleBlocks W v) (D v) := by
  unfold starInsert blockD
  rw [rowStar_blocks]
  let A : Matrix Three Three (Matrix ι ι ℂ) := fun a b => if a = v then triangleBlocks W a b else 0
  change (blocks A)ᴴ * blocks (Matrix.diagonal D) * blocks A = _
  rw [← blocks_star, ← blocks_mul, ← blocks_mul]
  unfold insertRow
  congr 1
  apply Matrix.ext
  intro a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  change (∑ c, star (A c a) * D c * A c b) =
    (triangleBlocks W v a)ᴴ * D v * triangleBlocks W v b
  simp [A, apply_ite, Matrix.star_eq_conjTranspose]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace TriangularHilbert.MatrixEnergy
variable {ι : Type uι} {κ : Type uκ} {μ : Type uμ} [Fintype ι] [Fintype κ] [Fintype μ]

variable [DecidableEq κ]

end TriangularHilbert.MatrixEnergy
end
end
end
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
open scoped BigOperators
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.MatrixEnergy.starInsert_eq_insertRow.{uι} := @_root_.OAI.TriangularHilbert.MatrixEnergy.starInsert_eq_insertRow.{uι}
