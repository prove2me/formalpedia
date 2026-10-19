-- Prove2me | solution 1 for OAI.EuclideanRamsey.Path.expand
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:53:13.38796+00:00
-- url     : https://prove2.me/submissions/153a76b7-26c9-40a1-b4c5-2910f871980c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/UltrafilterStrings.lean:L159-L178
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.Path.expand. The node keeps its source
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
end UltraColumn
end EuclideanRamsey
namespace EuclideanRamsey
open Filter
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup
variable {ι : Type uIndex}

lemma Path.expand {a : ι → FiniteEuclidean} {w u} (h : Path a w u)
    (Ψ : LetterGroup →ₙ* Ultrafilter Strings) (p : Ultrafilter Strings)
    (hgen : ∀ z,Ψ (FreeGroup.of z)=p*(pure (FreeMonoid.of z))*p) :
    ∃ qs : List (UltraColumn ι Strings),ColumnPath a qs u ∧
      (letI := ultrafilterMonoid (M:=Strings); ∀ i,(qs.map (fun q => q.value i)).prod=Ψ (w i)) := by
  let := ultrafilterMonoid (M:=Strings)
  induction h with
  | diag g => exact ⟨[.common (Ψ g)],.common _,by intro i; simp [UltraColumn.value]⟩
  | @copy u b hb =>
    refine ⟨[.common p,.principal (fun i => FreeMonoid.of (b i)),.common p],?_,?_⟩
    · simpa using (ColumnPath.common p).append ((ColumnPath.copy b hb).append (.common p))
    · intro i
      simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,UltraColumn.value,mul_one,hgen,mul_assoc]
  | @mul w v u t hu hv ihu ihv =>
    obtain ⟨qs,hqs,hqe⟩ := ihu
    obtain ⟨rs,hrs,hre⟩ := ihv
    refine ⟨qs++rs,hqs.append hrs,?_⟩
    intro i
    simp only [List.map_append,List.prod_append,hqe,hre,Pi.mul_apply]
    exact (Ψ.map_mul _ _).symm

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
open Filter
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup


theorem solution.{uIndex} : type_of% @_root_.OAI.EuclideanRamsey.Path.expand.{uIndex} := @_root_.OAI.EuclideanRamsey.Path.expand.{uIndex}
