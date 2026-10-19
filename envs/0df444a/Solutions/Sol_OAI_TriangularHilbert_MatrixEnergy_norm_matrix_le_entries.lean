-- Prove2me | solution 1 for OAI.TriangularHilbert.MatrixEnergy.norm_matrix_le_entries
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:33:26.085061+00:00
-- url     : https://prove2.me/submissions/c4b75b0b-937d-4e12-bab8-6b17c2f4702b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/NormBounds.lean:L89-L103
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.MatrixEnergy.norm_matrix_le_entries. The node keeps its source
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
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds

-- ---- from OAI.Analysis.TriangularHilbert.NormBounds ----
namespace OAI

universe uι

section

namespace TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma norm_matrix_le_entries (R : Matrix ι ι ℂ) {M : ℝ} (hM : ∀ i j, ‖R i j‖ ≤ M) :
    ‖R‖ ≤ entryNormConstant ι * M := by
  calc
    _ = ‖∑ i, ∑ j, Matrix.single i j (R i j)‖ := congrArg norm (Matrix.matrix_eq_sum_single R)
    _ ≤ ∑ i, ‖∑ j, Matrix.single i j (R i j)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖Matrix.single i j (R i j)‖ := Finset.sum_le_sum (fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ i : ι, ∑ j : ι, ‖Matrix.single i j (1 : ℂ)‖ * M := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [show Matrix.single i j (R i j) = (R i j) • Matrix.single i j (1 : ℂ) by
        rw [Matrix.smul_single]; simp, norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_left (hM i j) (norm_nonneg _)
    _ = _ := by simp [entryNormConstant, Finset.sum_mul]

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.MatrixEnergy.norm_matrix_le_entries.{uι} := @_root_.OAI.TriangularHilbert.MatrixEnergy.norm_matrix_le_entries.{uι}
