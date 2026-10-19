-- Prove2me | solution 1 for OAI.EuclideanRamsey.full_affine_representative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T04:56:03.864756+00:00
-- url     : https://prove2.me/submissions/b30560e8-2923-4ec1-a1e3-e195106a9cd0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Main.lean:L78-L123
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.full_affine_representative. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CorrectionPaths__EuclideanRamseyTransitive

-- ---- from OAI.Combinatorics.EuclideanRamsey.Main ----
namespace OAI

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

end EuclideanRamsey

namespace EuclideanRamsey

theorem full_affine_representative {s D : ℕ} (a : Fin s → Space D)
    (hs : 2 ≤ s) (ha : Function.Injective a) :
    ∃ d : ℕ,1 ≤ d ∧ ∃ b : Fin s → Space d,Function.Injective b ∧
      Congruent a b ∧ affineSpan ℝ (Set.range b)=⊤ := by
  classical
  let i₀ : Fin s := ⟨0,by omega⟩
  let i₁ : Fin s := ⟨1,by omega⟩
  let V : Submodule ℝ (Space D) := Submodule.span ℝ (Set.range (fun i => a i-a i₀))
  have hx (i : Fin s) : a i-a i₀∈V := Submodule.subset_span (Set.mem_range_self i)
  let x (i : Fin s) : V := ⟨a i-a i₀,hx i⟩
  have hxspan : Submodule.span ℝ (Set.range x)=⊤ :=
    (Submodule.span_range_subtype_eq_top_iff V hx).mpr rfl
  have hpos : 0<Module.finrank ℝ V := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨x i₁,?_⟩
    intro he
    have hv := congrArg (fun z : V => (z : Space D)) he
    change a i₁-a i₀=0 at hv
    have hi := ha (sub_eq_zero.mp hv)
    have hi' := congrArg Fin.val hi
    norm_num [i₀,i₁] at hi'
  let E := (stdOrthonormalBasis ℝ V).repr
  let b : Fin s → Space (Module.finrank ℝ V) := fun i => E (x i)
  have hbspan : Submodule.span ℝ (Set.range b)=⊤ := by
    change Submodule.span ℝ (Set.range (E.toLinearEquiv.toLinearMap ∘ x))=⊤
    rw [Set.range_comp,Submodule.span_image,hxspan,Submodule.map_top]
    exact LinearMap.range_eq_top.mpr E.surjective
  have hb0 : b i₀=0 := by
    change E (x i₀)=0
    have hx0 : x i₀=0 := by apply Subtype.ext; exact sub_self _
    rw [hx0,map_zero]
  refine ⟨Module.finrank ℝ V,hpos, b,?_,?_,?_⟩
  · intro i j he
    have hx' := E.injective he
    have hv := congrArg (fun z : V => (z : Space D)) hx'
    change a i-a i₀=a j-a i₀ at hv
    exact ha (sub_left_injective hv)
  · intro i j
    change dist (E (x i)) (E (x j))=dist (a i) (a j)
    rw [dist_eq_norm,dist_eq_norm,← map_sub,LinearIsometryEquiv.norm_map]
    change ‖(a i-a i₀)-(a j-a i₀)‖=‖a i-a j‖
    rw [sub_sub_sub_cancel_right]
  · apply (AffineSubspace.direction_eq_top_iff_of_nonempty
      ⟨b i₀,subset_affineSpan ℝ (Set.range b) (Set.mem_range_self i₀)⟩).mp
    rw [direction_affineSpan,vectorSpan_range_eq_span_range_vsub_right ℝ b i₀]
    simpa only [vsub_eq_sub,hb0,sub_zero] using hbspan
end EuclideanRamsey

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
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.full_affine_representative := @_root_.OAI.EuclideanRamsey.full_affine_representative
