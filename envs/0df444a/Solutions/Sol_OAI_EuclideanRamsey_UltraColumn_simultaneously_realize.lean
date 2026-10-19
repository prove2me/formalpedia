-- Prove2me | solution 1 for OAI.EuclideanRamsey.UltraColumn.simultaneously_realize
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:49:07.585208+00:00
-- url     : https://prove2.me/submissions/aa3badbf-b830-4fa6-b099-68bcb513ec10

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/UltrafilterStrings.lean:L85-L109
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.UltraColumn.simultaneously_realize. The node keeps its source
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

-- ---- from OAI.Combinatorics.EuclideanRamsey.UltrafilterStrings ----
namespace OAI

universe uModule uIndex uAlpha

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
namespace EuclideanRamsey
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup

section Ultrafilters
variable {M : Type uModule} [Monoid M]
end Ultrafilters

namespace UltraColumn
variable {ι : Type uIndex} {M : Type uModule}
lemma choose [Finite ι] (q : UltraColumn ι M) (p : ι → M → Prop)
    (h : ∀ i,∀ᶠ x in (q.value i : Filter M),p i x) :
    ∃ x : ι → M,q.Realizes x ∧ ∀ i,p i (x i) := by
  cases q with
  | common U =>
    have hh : ∀ᶠ x in (U : Filter M),∀ i,p i x := Filter.eventually_all.mpr h
    obtain ⟨x,hx⟩ := hh.exists
    exact ⟨fun _ => x,⟨x,fun _ => rfl⟩,hx⟩
  | principal x =>
    refine ⟨x,rfl,?_⟩
    intro i
    simpa [value] using h i

theorem simultaneously_realize [Finite ι] [Monoid M] (qs : List (UltraColumn ι M))
    (B : ι → Set M)
    (h : letI := ultrafilterMonoid (M:=M)
      ∀ i,B i ∈ ((qs.map (fun q => q.value i)).prod : Ultrafilter M)) :
    ∃ xs : List (ι → M), List.Forall₂ Realizes qs xs ∧
      ∀ i, (xs.map (fun x => x i)).prod ∈ B i := by
  let := ultrafilterMonoid (M:=M)
  induction qs generalizing B with
  | nil =>
    refine ⟨[],.nil,?_⟩
    intro i
    have hi := h i
    change B i ∈ (pure (1:M) : Ultrafilter M) at hi
    simpa using hi
  | cons q qs ih =>
    have hh (i : ι) : ∀ᶠ x in (q.value i : Filter M),
        {y | x*y∈B i} ∈ ((qs.map (fun q => q.value i)).prod : Ultrafilter M) := by
      have hi := h i
      change ∀ᶠ z in ((q.value i)*(qs.map (fun q => q.value i)).prod : Ultrafilter M), z∈B i at hi
      exact (Ultrafilter.eventually_mul _ _ _).mp hi
    obtain ⟨x,hx,hxB⟩ := q.choose _ hh
    obtain ⟨xs,hxs,hB⟩ := ih (fun i => {y | x i*y∈B i}) hxB
    refine ⟨x::xs,.cons hx hxs,?_⟩
    intro i
    simpa using hB i
end UltraColumn
end EuclideanRamsey
namespace EuclideanRamsey
open Filter
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup
variable {ι : Type uIndex}

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.UltraColumn
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
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup


theorem solution.{uModule,uIndex} : type_of% @_root_.OAI.EuclideanRamsey.UltraColumn.simultaneously_realize.{uModule,uIndex} := @_root_.OAI.EuclideanRamsey.UltraColumn.simultaneously_realize.{uModule,uIndex}
