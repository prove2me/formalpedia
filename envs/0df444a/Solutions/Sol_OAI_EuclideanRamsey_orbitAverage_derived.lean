-- Prove2me | solution 1 for OAI.EuclideanRamsey.orbitAverage_derived
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T04:10:00.87498+00:00
-- url     : https://prove2.me/submissions/2d4e37cd-a441-4f1d-8f43-6869508751b5

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/NormalCost.lean:L135-L156
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.orbitAverage_derived. The node keeps its source
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
end NormalCost

lemma groupList_mul_perm [Fintype H] (h : H) :
    ((groupList H).map (·*h)).Perm (groupList H) := by
  classical
  apply (List.perm_ext_iff_of_nodup ((Finset.nodup_toList _).map (mul_left_injective h))
    (Finset.nodup_toList _)).mpr
  intro g
  simp only [List.mem_map,Finset.mem_toList,Finset.mem_univ,true_and,iff_true]
  exact ⟨g*h⁻¹,by group⟩

lemma orbitAverage_derived [Fintype H] (N : Subgroup G) [N.Normal]
    (w : X → G) (x y : X) (horbit : SameOrbit (H:=H) x y)
    (hw : ∀ g : H,w (g•x)∈N) :
    orbitAverage (H:=H) w x*(orbitAverage (H:=H) w y)⁻¹∈⁅N,N⁆ := by
  obtain ⟨h,rfl⟩ := horbit
  let q := QuotientGroup.mk' ⁅N,N⁆
  rw [← div_eq_mul_inv]
  apply QuotientGroup.eq_iff_div_mem.mp
  change q (orbitAverage (H:=H) w x)=q (orbitAverage (H:=H) w (h•x))
  simp only [orbitAverage,map_list_prod,List.map_map]
  have hp := (groupList_mul_perm h).map (fun g => q (w (g•x)))
  simp only [List.map_map,Function.comp_def,mul_smul] at hp
  symm
  apply hp.prod_eq'
  apply List.pairwise_map.mpr
  apply List.pairwise_of_forall
  intro g k
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.commutator_mem_commutator (by simpa only [mul_smul] using hw (g*h))
      (by simpa only [mul_smul] using hw (k*h)))
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
open Filter
open Set
open scoped BigOperators commutatorElement


theorem solution.{uGroup,uAction,uPoint} : type_of% @_root_.OAI.EuclideanRamsey.orbitAverage_derived.{uGroup,uAction,uPoint} := @_root_.OAI.EuclideanRamsey.orbitAverage_derived.{uGroup,uAction,uPoint}
