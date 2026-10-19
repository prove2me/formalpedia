-- Prove2me | solution 1 for OAI.SubsphereCurrent.Fixed.parameters
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:29:13.385593+00:00
-- url     : https://prove2.me/submissions/e82578a9-84ec-43af-9de3-f579acc70d1c

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Estimates/FixedPrecision.lean:L19-L36
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.Fixed.parameters. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection
import Definitions.Def_OAI_Probability_Subsphere_Regression_Model
import Definitions.Def_OAI_Probability_Subsphere_Regression_Spheres
import Definitions.Def_OAI_Probability_Subsphere_Regression_Blocks
import Definitions.Def_OAI_Probability_Subsphere_Regression_Streaming
import Definitions.Def_OAI_Probability_Subsphere_Kernels_Precision
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Integration
import Definitions.Def_OAI_Probability_Subsphere_Geometry_MassBounds
import Definitions.Def_OAI_Probability_Subsphere_Geometry_Affine
import Definitions.Def_OAI_Probability_Subsphere_Estimates_FixedPrecision

-- ---- from OAI.Probability.Subsphere.Estimates.FixedPrecision ----
namespace OAI

noncomputable section

namespace SubsphereCurrent.Fixed
section
open scoped ENNReal NNReal

lemma parameters {d j m : ℕ} (hd : 64 ≤ d) (hm : (d : ℝ)/2 + 2*j ≤ m) :
    let q := (m-1)/4
    2 ≤ q ∧ d ≤ 16*q ∧ d/32 ≤ q ∧ (d : ℝ)/32 ≤ 2*q ∧
      j*(d/32)/q+1 ≤ j+1 := by
  have hdm : d ≤ 2*m := by
    have : (d : ℝ) ≤ 2*m := by nlinarith [Nat.cast_nonneg j (α := ℝ)]
    exact_mod_cast this
  dsimp
  have hq : 2 ≤ (m-1)/4 := by omega
  have hq32 : d/32 ≤ (m-1)/4 := by omega
  refine ⟨hq, by omega, hq32, ?_, ?_⟩
  · have hn : d ≤ 64*((m-1)/4) := by omega
    have hr : (d : ℝ) ≤ 64*((m-1)/4 : ℕ) := by exact_mod_cast hn
    linarith
  · have hmul : j*(d/32) ≤ j*((m-1)/4) := Nat.mul_le_mul_left j hq32
    have hdiv : j*(d/32)/((m-1)/4) ≤ j := by
      exact Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hmul)
    omega

end
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
universe u

end SubsphereCurrent.Fixed

end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereCurrent OAI.SubsphereCurrent.Fixed
open scoped ENNReal NNReal


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.Fixed.parameters := @_root_.OAI.SubsphereCurrent.Fixed.parameters
