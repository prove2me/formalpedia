-- Prove2me | solution 1 for OAI.EuclideanRamsey.RightFraction.mul_pair
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:38:25.329353+00:00
-- url     : https://prove2.me/submissions/4f7811a4-ec12-4526-9af1-f43fe49097b1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/PathFractions.lean:L97-L117
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.RightFraction.mul_pair. The node keeps its source
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

lemma RightFraction.mul_pair {M : Submonoid (ι → G)} (hM : PairInverse M)
    {z t : ι → G} (hz : RightFraction M z) (ht : RightFraction M t)
    (i j : ι) (hij : i≠j) (hs : ∀ l,l≠i → l≠j → t l=1) :
    RightFraction M (z*t) := by
  obtain ⟨u,hu,v,hv,rfl⟩ := hz
  obtain ⟨c,hc,d,hd,rfl⟩ := ht
  obtain ⟨b,hb,hi,hj⟩ := hM i j hij v hv
  have hcomm : Commute (v*b) (c*d⁻¹) := by
    ext l
    by_cases hli : l=i
    · subst l; simp only [Pi.mul_apply,Pi.inv_apply] at *; rw [hi]; simp
    by_cases hlj : l=j
    · subst l; simp only [Pi.mul_apply,Pi.inv_apply] at *; rw [hj]; simp
    · have hh := hs l hli hlj
      change v l*b l*(c l*(d l)⁻¹) = (c l*(d l)⁻¹)*(v l*b l)
      change c l*(d l)⁻¹=1 at hh
      rw [hh]; simp
  refine ⟨u*b*c,M.mul_mem (M.mul_mem hu hb) hc,(v*b)*d,M.mul_mem (M.mul_mem hv hb) hd,?_⟩
  have he : u*v⁻¹ = (u*b)*(v*b)⁻¹ := by group
  rw [he,mul_assoc,hcomm.inv_left.eq]
  group
end Fractions
end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
variable {G : Type uGroup} {ι : Type uIndex} [Group G] [DecidableEq ι]

namespace GradedPaths
variable (P : GradedPaths ι G)
end GradedPaths
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
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators


theorem solution.{uGroup,uIndex} : type_of% @_root_.OAI.EuclideanRamsey.RightFraction.mul_pair.{uGroup,uIndex} := @_root_.OAI.EuclideanRamsey.RightFraction.mul_pair.{uGroup,uIndex}
