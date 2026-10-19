-- Prove2me | solution 2 for OAI.TriangularHilbert.MatrixEnergy.vertexRoot_insert
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:29:55.332088+00:00
-- url     : https://prove2.me/submissions/dddf5d2a-f6a4-40b2-848b-145695fa2e00

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/StarInsertion.lean:L86-L99
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.MatrixEnergy.vertexRoot_insert. The node keeps its source
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar

-- ---- from OAI.Analysis.TriangularHilbert.StarInsertion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma vertexRoot_insert (g d : Three → ι → ℝ) (hg : ∀ v i, 0 ≤ g v i) :
    vertexRoot g * blockD (fun v => Matrix.diagonal (fun i => (d v i : ℂ))) * vertexRoot g =
      Matrix.diagonal (fun a => (g a.1 a.2 * d a.1 a.2 : ℂ)) := by
  have hb : blockD (fun v => Matrix.diagonal (fun i => (d v i : ℂ))) =
      Matrix.diagonal (fun a => (d a.1 a.2 : ℂ)) := by
    ext ⟨v,i⟩ ⟨w,j⟩
    by_cases hv : v = w <;> by_cases hi : i = j <;> simp [blockD, blocks, Matrix.diagonal, hv, hi, Prod.mk.injEq]
  rw [hb, vertexRoot, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext ⟨v,i⟩
  rw [mul_comm (Real.sqrt _ : ℂ) (d v i), mul_assoc, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (hg v i)]
  push_cast
  ring

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.MatrixEnergy.vertexRoot_insert.{uι} := @_root_.OAI.TriangularHilbert.MatrixEnergy.vertexRoot_insert.{uι}
