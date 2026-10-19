-- Prove2me | solution 1 for OAI.EuclideanRamsey.linear_moment_contract
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:13:03.967573+00:00
-- url     : https://prove2.me/submissions/9cdce9ee-c486-4231-aaa7-5d749d146b56

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Discretization.lean:L66-L80
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.linear_moment_contract. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization

-- ---- from OAI.Combinatorics.EuclideanRamsey.Discretization ----
namespace OAI

universe uDomain uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct

open MeasureTheory
open scoped BigOperators
namespace EuclideanRamsey

end EuclideanRamsey

open scoped BigOperators
namespace EuclideanRamsey

lemma linear_moment_contract {ι : Type uIndex} {k : ℕ}
    (S : Finset ι) (q : ι → ℝ) (v : ι → (Fin k → ℝ))
    (L : (Fin k → ℝ) →L[ℝ] ℝ) :
    ∑ γ ∈ S,q γ*L (v γ) = ∑ j,(∑ γ ∈ S,q γ*v γ j)*L (Pi.single j 1) := by
  have hv (γ : ι) : v γ = ∑ j, v γ j • Pi.single j (1:ℝ) := by
    ext l
    simp [Pi.single_apply]
  conv_lhs => arg 2; intro γ; rw [hv γ]
  simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro γ hγ
  ring

end EuclideanRamsey

open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
namespace EuclideanRamsey

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open MeasureTheory
open scoped BigOperators
open scoped BigOperators


theorem solution.{uIndex} : type_of% @_root_.OAI.EuclideanRamsey.linear_moment_contract.{uIndex} := @_root_.OAI.EuclideanRamsey.linear_moment_contract.{uIndex}
