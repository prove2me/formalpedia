-- Prove2me | solution 1 for OAI.TriangularHilbert.MatrixEnergy.sylv_solvable_inserted_gram
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:09:37.706487+00:00
-- url     : https://prove2.me/submissions/c6f0b247-730d-4aa0-b8b9-cbcd84521bfb

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/MatrixSupport.lean:L830-L863
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.MatrixEnergy.sylv_solvable_inserted_gram. The node keeps its source
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

omit [Fintype ι] [DecidableEq ι] in

theorem gram_diag_eq_zero_iff {κ : Type uκ} [Fintype κ]
    (R : Matrix κ ι ℂ) (j : ι) :
    (Rᴴ * R) j j = 0 ↔ ∀ i, R i j = 0 := by
  change star (fun i => R i j) ⬝ᵥ (fun i => R i j) = 0 ↔ _
  rw [dotProduct_star_self_eq_zero]
  exact funext_iff

theorem sylv_solvable_inserted_gram {κ : Type uκ} [Fintype κ]
    (R : Matrix κ ι ℂ) (D : Matrix κ κ ℂ) :
    ∃ Y, sylv (CFC.sqrt (Rᴴ * R)) Y = Rᴴ * D * R := by
  let P := Rᴴ * R
  let A := CFC.sqrt P
  have hP : P.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self R
  have hA : A.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)
  let U := hA.isHermitian.eigenvectorUnitary
  let f := conjStarAlgAut ℂ (Matrix ι ι ℂ) (star U)
  let R' := R * (U : Matrix ι ι ℂ)
  let q := hA.isHermitian.eigenvalues
  have hAd : f A = Matrix.diagonal (fun i => (q i : ℂ)) :=
    hA.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hAp : A * A = P := CFC.sqrt_mul_sqrt_self P hP.nonneg
  have hGram : R'ᴴ * R' = f P := by
    simp only [R', f, P, conjStarAlgAut_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hIns : f (Rᴴ * D * R) = R'ᴴ * D * R' := by
    simp only [R', f, conjStarAlgAut_apply, Unitary.coe_star,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  apply exists_sylv_solution hA.isHermitian
  intro i j hij
  have hj : q j = 0 :=
    ((add_eq_zero_iff_of_nonneg (hA.eigenvalues_nonneg i)
      (hA.eigenvalues_nonneg j)).mp hij).2
  have hdiag : (R'ᴴ * R') j j = 0 := by
    rw [hGram, ← hAp, map_mul, hAd, Matrix.diagonal_mul_diagonal]
    simp [hj]
  have hcol := (gram_diag_eq_zero_iff R' j).mp hdiag
  change f (Rᴴ * D * R) i j = 0
  rw [hIns]
  simp only [Matrix.mul_apply, hcol, mul_zero, Finset.sum_const_zero]

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


theorem solution.{uι,uκ} : type_of% @_root_.OAI.TriangularHilbert.MatrixEnergy.sylv_solvable_inserted_gram.{uι,uκ} := @_root_.OAI.TriangularHilbert.MatrixEnergy.sylv_solvable_inserted_gram.{uι,uκ}
