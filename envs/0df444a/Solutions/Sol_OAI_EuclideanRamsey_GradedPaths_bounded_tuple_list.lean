-- Prove2me | solution 1 for OAI.EuclideanRamsey.GradedPaths.bounded_tuple_list
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:41:01.614874+00:00
-- url     : https://prove2.me/submissions/0cd7472a-0211-45e4-9c26-e934eff8cc4f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/PathFractions.lean:L222-L241
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.GradedPaths.bounded_tuple_list. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions

-- ---- from OAI.Combinatorics.EuclideanRamsey.PathFractions ----
namespace OAI

universe uGroup uIndex

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
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace

open scoped BigOperators
namespace EuclideanRamsey
section Fractions
variable {G : Type uGroup} {ι : Type uIndex} [Group G] [DecidableEq ι]

end Fractions
end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
variable {G : Type uGroup} {ι : Type uIndex} [Group G] [DecidableEq ι]

namespace GradedPaths
variable (P : GradedPaths ι G)
lemma bounded_tuple_list (l : List ι) (z : ι → G) (c : ι → ℕ)
    (h : ∀ i∈l,P.BoundedFraction (Pi.mulSingle i (z i)) (c i)) :
    P.BoundedFraction ((l.map (fun i => Pi.mulSingle i (z i))).prod) ((l.map c).sum) := by
  induction l with
  | nil => simpa using P.bounded_one
  | cons i l ih =>
    have ht := (P.bounded_mul_single (ih (by intro j hj; exact h j (by simp [hj]))) i (h i (by simp)))
    have he : (l.map (fun j => Pi.mulSingle j (z j))).prod*Pi.mulSingle i (z i)=
        Pi.mulSingle i (z i)*(l.map (fun j => Pi.mulSingle j (z j))).prod := by
      apply Commute.symm
      apply Commute.list_prod_right
      intro y hy
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hy
      by_cases hji : j=i
      · subst j; exact Commute.refl _
      · ext k
        by_cases hki : k=i
        · subst k; simp [Pi.mulSingle_eq_of_ne (Ne.symm hji)]
        · simp [Pi.mulSingle_eq_of_ne hki]
    simpa [he,Nat.add_comm] using ht
end GradedPaths
end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.GradedPaths
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
open scoped BigOperators


theorem solution.{uGroup,uIndex} : type_of% @_root_.OAI.EuclideanRamsey.GradedPaths.bounded_tuple_list.{uGroup,uIndex} := @_root_.OAI.EuclideanRamsey.GradedPaths.bounded_tuple_list.{uGroup,uIndex}
