-- Prove2me | solution 1 for OAI.TriangularHilbert.MatrixEnergy.norm_energyGradient_inserted_gram_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:31:56.906959+00:00
-- url     : https://prove2.me/submissions/244ae697-bf76-431d-94a6-93089073cdff

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/NormBounds.lean:L42-L62
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularHilbert.MatrixEnergy.norm_energyGradient_inserted_gram_le. The node keeps its source
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

lemma norm_sqrt_gram (R : Matrix ι ι ℂ) : ‖CFC.sqrt (Rᴴ * R)‖ = ‖R‖ := by
  rw [CFC.norm_sqrt _ (Matrix.posSemidef_conjTranspose_mul_self R).nonneg]
  rw [show ‖Rᴴ * R‖ = ‖R‖ * ‖R‖ from CStarRing.norm_star_mul_self,
    Real.sqrt_mul_self (norm_nonneg R)]

lemma norm_traceReal_le (X : Matrix ι ι ℂ) :
    ‖traceReal X‖ ≤ ‖traceRealCLM (ι := ι)‖ * ‖X‖ := by
  exact (traceRealCLM (ι := ι)).le_opNorm X

lemma norm_energyGradient_inserted_gram_le (R L : Matrix ι ι ℂ) :
    ‖energyGradient (Rᴴ * R) (Rᴴ * L * R)‖ ≤
      (3/2 : ℝ) * ‖traceRealCLM (ι := ι)‖ * ‖L‖ * ‖R‖^3 := by
  rw [energyGradient_apply, norm_mul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3/2)]
  have hh : ‖traceReal (CFC.sqrt (Rᴴ * R) * (Rᴴ * L * R))‖ ≤
      ‖traceRealCLM (ι := ι)‖ * (‖R‖ * ((‖R‖ * ‖L‖) * ‖R‖)) := by
    calc
      _ ≤ ‖traceRealCLM (ι := ι)‖ * ‖CFC.sqrt (Rᴴ * R) * (Rᴴ * L * R)‖ :=
        norm_traceReal_le _
      _ ≤ ‖traceRealCLM (ι := ι)‖ * (‖CFC.sqrt (Rᴴ * R)‖ * ‖Rᴴ * L * R‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ ‖traceRealCLM (ι := ι)‖ * (‖R‖ * ((‖R‖ * ‖L‖) * ‖R‖)) := by
        rw [norm_sqrt_gram]
        gcongr
        calc
          _ ≤ ‖Rᴴ * L‖ * ‖R‖ := norm_mul_le _ _
          _ ≤ (‖Rᴴ‖ * ‖L‖) * ‖R‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
          _ = _ := by rw [show ‖Rᴴ‖ = ‖R‖ from norm_star R]
  calc
    _ ≤ (3/2 : ℝ) * (‖traceRealCLM (ι := ι)‖ * (‖R‖ * ((‖R‖ * ‖L‖) * ‖R‖))) := by gcongr
    _ = _ := by ring

end
end TriangularHilbert.MatrixEnergy
end

end OAI

-- ---- platform node ----
open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators


theorem solution.{uι} : type_of% @_root_.OAI.TriangularHilbert.MatrixEnergy.norm_energyGradient_inserted_gram_le.{uι} := @_root_.OAI.TriangularHilbert.MatrixEnergy.norm_energyGradient_inserted_gram_le.{uι}
