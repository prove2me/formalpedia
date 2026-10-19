-- Prove2me | solution 1 for OAI.EuclideanRamsey.NormalCost.product_difference
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:07:18.570995+00:00
-- url     : https://prove2.me/submissions/34f3dbd4-eff3-45dd-8406-4d0d1ac7d369

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/NormalCost.lean:L74-L91
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.NormalCost.product_difference. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost

-- ---- from OAI.Combinatorics.EuclideanRamsey.NormalCost ----
namespace OAI

universe uGroup uAction uPoint uAlpha

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
open Filter
open Set

namespace EuclideanRamsey
open scoped BigOperators commutatorElement
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X]

namespace NormalCost
variable {L : Subgroup G} [L.Normal] (c : NormalCost L)
lemma product_difference {α : Type uAlpha} (l : List α) (a b : α → G)
    (h : ∀ j∈l,a j*(b j)⁻¹∈L) :
    (l.map a).prod*((l.map b).prod)⁻¹∈L ∧
    c.cost ((l.map a).prod*((l.map b).prod)⁻¹) ≤
      (l.map (fun j => c.cost (a j*(b j)⁻¹))).sum := by
  induction l with
  | nil => simp [c.one,L.one_mem]
  | cons j l ih =>
    obtain ⟨hm,hc⟩ := ih (fun k hk => h k (by simp [hk]))
    have hj := h j (by simp)
    let z := (l.map a).prod*((l.map b).prod)⁻¹
    have he : (a j*(l.map a).prod)*(b j*(l.map b).prod)⁻¹ =
        (a j*z*(a j)⁻¹)*(a j*(b j)⁻¹) := by dsimp [z]; group
    have hz : a j*z*(a j)⁻¹∈L := (inferInstance : L.Normal).conj_mem _ hm _
    simp only [List.map_cons,List.prod_cons,List.sum_cons]
    rw [he]
    refine ⟨L.mul_mem hz hj,?_⟩
    exact (c.mul _ hz _ hj).trans (by rw [c.conj z hm]; linarith)
end NormalCost

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.NormalCost
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
open Filter
open Set
open scoped BigOperators commutatorElement


theorem solution.{uGroup,uAlpha} : type_of% @_root_.OAI.EuclideanRamsey.NormalCost.product_difference.{uGroup,uAlpha} := @_root_.OAI.EuclideanRamsey.NormalCost.product_difference.{uGroup,uAlpha}
