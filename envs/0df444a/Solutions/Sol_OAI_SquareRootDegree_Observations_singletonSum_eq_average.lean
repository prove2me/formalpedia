-- Prove2me | solution 1 for OAI.SquareRootDegree.Observations.singletonSum_eq_average
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:44:58.923851+00:00
-- url     : https://prove2.me/submissions/595b428b-025f-47bb-a519-6c77771bacc2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BooleanFunctions/Readout.lean:L16-L29
-- (upload_full_project.md Phase 4): solution for node OAI.SquareRootDegree.Observations.singletonSum_eq_average. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SquareRootDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Walsh
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Conditioning
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Blocks
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Projection
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_FiniteCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Observations
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothGaussian
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SmoothSelector
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_GaussianGain
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_MomentTransfer
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_SoftEvent
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Switching
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Rounding
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_CellDegree
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Grouping
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Amplification
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_ReadoutCLT
import Definitions.Def_OAI_Combinatorics_BooleanFunctions_Readout

-- ---- from OAI.Combinatorics.BooleanFunctions.Walsh ----
namespace OAI

/-!
Bool encodes a sign: false is +1 and true is -1. The average is uniform,
and degree is ordinary real Fourier degree, not F₂ degree or threshold degree.
-/

open scoped BigOperators

noncomputable section

namespace SquareRootDegree

/-! ## Finite Walsh calculus -/

theorem average_sum {α κ : Type*} [Fintype α] (s : Finset κ) (f : κ → α → ℝ) :
    average (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, average (f j) := by
  simp only [average, Finset.mul_sum]
  rw [Finset.sum_comm]

/-! ### Degree calculus for finite observations -/

end SquareRootDegree

end

end OAI

-- ---- from OAI.Combinatorics.BooleanFunctions.Readout ----
namespace OAI

open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real

noncomputable section

namespace SquareRootDegree
namespace Observations
attribute [local instance] Classical.propDecidable
variable {γ β : Type*} [Fintype γ] [Fintype β] [DecidableEq γ]

omit [Fintype β] in
theorem singletonSum_eq_average (f : Cube γ → ℝ) :
    singletonSum f = average (fun x => f x*cubeSum x) := by
  have hi (i : γ) : fourierCoeff f {i} = average (fun x => f x*sign (x i)) := by
    unfold fourierCoeff
    simp only [character_singleton]
    congr 1
    exact Subsingleton.elim _ _
  unfold singletonSum
  simp only [hi]
  rw [← average_sum]
  congr 1
  funext x
  exact (Finset.mul_sum _ _ _).symm

end Observations
end SquareRootDegree

namespace SquareRootDegree
namespace Observations
attribute [local instance] Classical.propDecidable
variable {γ δ : Type*} [Fintype γ] [Fintype δ] [DecidableEq γ] [DecidableEq δ]

end Observations
end SquareRootDegree

namespace SquareRootDegree
namespace Observations
attribute [local instance] Classical.propDecidable

variable {γ β : Type*} [Fintype γ] [Fintype β] [DecidableEq γ]

end Observations
end SquareRootDegree

end

end OAI

-- ---- platform node ----
open OAI OAI.SquareRootDegree OAI.SquareRootDegree.Observations
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Real
attribute [local instance] Classical.propDecidable
variable {γ β : Type*} [Fintype γ] [Fintype β] [DecidableEq γ]

omit [Fintype β] in
theorem solution (f : Cube γ → ℝ) :
    singletonSum f = average (fun x => f x*cubeSum x) := by
  first
    | exact OAI.SquareRootDegree.Observations.singletonSum_eq_average f
    | exact OAI.SquareRootDegree.Observations.singletonSum_eq_average
    | (apply OAI.SquareRootDegree.Observations.singletonSum_eq_average <;> assumption)
    | (intros; apply OAI.SquareRootDegree.Observations.singletonSum_eq_average <;> assumption)
