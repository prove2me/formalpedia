-- Prove2me | solution 1 for OAI.SubsphereCurrent.rpow_decrease_shift
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:55:30.043479+00:00
-- url     : https://prove2.me/submissions/015312e7-b684-47ac-ab14-2a73521b97de

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Mixture/Domination.lean:L124-L143
-- (upload_full_project.md Phase 4): solution for node OAI.SubsphereCurrent.rpow_decrease_shift. The node keeps its source
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
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Haar
import Definitions.Def_OAI_Probability_Subsphere_Mixture_BetaTheory
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Latitude
import Definitions.Def_OAI_Probability_Subsphere_Mixture_Domination

-- ---- from OAI.Probability.Subsphere.Mixture.Domination ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace SubsphereCurrent

private lemma rpow_decrease_shift {x a A D : ℝ} (hx : (1 / 2 : ℝ) ≤ x)
    (ha : a ≤ A) (hD : A - a ≤ D) :
    x ^ (a - 1) ≤ (2 : ℝ) ^ D * x ^ (A - 1) := by
  have hx0 : 0 < x := by linarith
  have hfactor : x ^ (a - A) ≤ (2 : ℝ) ^ D := by
    calc
      x ^ (a - A) ≤ (1 / 2 : ℝ) ^ (a - A) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hx (by linarith)
      _ = (2 : ℝ) ^ (A - a) := by
        rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]
        congr 1
        ring
      _ ≤ (2 : ℝ) ^ D := Real.rpow_le_rpow_of_exponent_le (by norm_num) hD
  calc
    x ^ (a - 1) = x ^ (a - A) * x ^ (A - 1) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    _ ≤ (2 : ℝ) ^ D * x ^ (A - 1) :=
      mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hx0.le _)

end SubsphereCurrent
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory Set
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end SubsphereCurrent.Mixture
end
end
section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace SubsphereCurrent.Mixture

end SubsphereCurrent.Mixture
end
end

end OAI

-- ---- platform node ----
open OAI OAI.SubsphereCurrent
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal


theorem solution : type_of% @_root_.OAI.SubsphereCurrent.rpow_decrease_shift := @_root_.OAI.SubsphereCurrent.rpow_decrease_shift
