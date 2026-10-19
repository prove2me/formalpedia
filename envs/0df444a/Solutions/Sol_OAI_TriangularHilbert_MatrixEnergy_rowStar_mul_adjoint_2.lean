-- Prove2me | solution 2 for OAI.TriangularHilbert.MatrixEnergy.rowStar_mul_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:24:56.295452+00:00
-- url     : https://prove2.me/submissions/ab2c001a-d61d-4054-8a5c-e7ef557ec9f1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/WeightedStar.lean:L118-L142
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.MatrixEnergy.rowStar_mul_adjoint. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Analysis.TriangularHilbert.WeightedStar ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma rowStar_eq_blocks (A : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar A v = blocks (fun a b => if a = v then triangleBlocks A a b else 0) := by
  exact rowStar_blocks A v

lemma rowStar_mul_adjoint (A : Three → Matrix ι ι ℂ) (v : Three) :
    rowStar A v * (rowStar A v)ᴴ =
      blockD (fun w => if w = v then centerGram A v else 0) := by
  rw [rowStar_eq_blocks]
  let R : Matrix Three Three (Matrix ι ι ℂ) := fun a b => if a = v then triangleBlocks A a b else 0
  change blocks R * (blocks R)ᴴ = _
  rw [← blocks_star, ← blocks_mul]
  unfold blockD
  congr 1
  apply Matrix.ext
  intro a b
  change (∑ c, R a c * (R b c)ᴴ) = Matrix.diagonal (fun w => if w = v then centerGram A v else 0) a b
  dsimp only [R]
  by_cases ha : a = v <;> by_cases hb : b = v
  · subst a
    subst b
    simp only [ite_true, Matrix.diagonal_apply_eq]
    rfl
  · simp [ha, hb, Ne.symm hb]
  · simp [ha, hb]
  · simp only [ite_eq_right ha, zero_mul, Finset.sum_const_zero]
    by_cases hab : a = b
    · subst b
      rw [Matrix.diagonal_apply_eq, ite_eq_right ha]
    · rw [Matrix.diagonal_apply_ne _ hab]

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.MatrixEnergy.rowStar_mul_adjoint.{uι} := @_root_.OAI.TriangularHilbert.MatrixEnergy.rowStar_mul_adjoint.{uι}
