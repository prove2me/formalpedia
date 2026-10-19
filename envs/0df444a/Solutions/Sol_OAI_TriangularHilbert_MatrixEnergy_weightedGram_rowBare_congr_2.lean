-- Prove2me | solution 2 for OAI.TriangularHilbert.MatrixEnergy.weightedGram_rowBare_congr
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:26:36.867318+00:00
-- url     : https://prove2.me/submissions/1ab5276c-32bf-4ba1-bc6f-63ab62c297ce

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/WeightedCompare.lean:L31-L47
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.MatrixEnergy.weightedGram_rowBare_congr. The node keeps its source
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

-- ---- from OAI.Analysis.TriangularHilbert.WeightedStar ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma rowStar_apply (A : Three → Matrix ι ι ℂ) (v : Three) (a b : BlockSpace ι) :
    rowStar A v a b = if a.1 = v then triangleBlocks A a.1 b.1 a.2 b.2 else 0 := by
  simp [rowStar, vertexProj, triangle, blocks, Matrix.diagonal_mul, ite_mul]

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- from OAI.Analysis.TriangularHilbert.WeightedCompare ----
namespace OAI

universe uι

section
namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma rowBare_apply_zero (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ) (v : Three)
    (a b : BlockSpace ι) (ha : a.1 ≠ v) : rowBare A g v a b = 0 := by
  simp [rowBare,vertexRoot,Matrix.mul_diagonal,rowStar_apply,ha]

lemma weightedGram_rowBare_congr (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (v : Three) (f f' : BlockSpace ι → ℝ) (he : ∀ i, f (v,i)=f' (v,i)) :
    weightedGram (rowBare A g v) f = weightedGram (rowBare A g v) f' := by
  ext a b
  unfold weightedGram
  conv_lhs => rw [Matrix.mul_apply]
  conv_rhs => rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.1 = v
  · obtain ⟨w,i⟩ := k
    change w = v at hk
    subst w
    rw [he i]
  · rw [rowBare_apply_zero A g v k b hk]
    simp

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.MatrixEnergy.weightedGram_rowBare_congr.{uι} := @_root_.OAI.TriangularHilbert.MatrixEnergy.weightedGram_rowBare_congr.{uι}
