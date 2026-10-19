-- Prove2me | solution 1 for OAI.EuclideanRamsey.ColumnPath.realizes
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:50:45.921167+00:00
-- url     : https://prove2.me/submissions/09d44eb9-11dc-46a4-beab-ffddeb1ee8c4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/UltrafilterStrings.lean:L124-L157
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.ColumnPath.realizes. The node keeps its source
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

-- ---- from OAI.Combinatorics.EuclideanRamsey.PathWords ----
namespace OAI

universe uIndex

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

namespace EuclideanRamsey
open scoped BigOperators
variable {ι : Type uIndex}

end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
lemma stringEnergy_append (l k l' k' : List FiniteEuclidean) (h : l.length=k.length) :
    stringEnergy (l++l') (k++k')=stringEnergy l k+stringEnergy l' k' := by
  induction l generalizing k with
  | nil => have hk : k=[] := List.length_eq_zero_iff.mp h.symm; subst k; simp [stringEnergy]
  | cons x l ih =>
    cases k with
    | nil => simp at h
    | cons y k =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at h
      simp only [List.cons_append,stringEnergy,ih k h,add_assoc]

variable {ι : Type uIndex}
lemma StringFamily.common (a : ι → FiniteEuclidean) (x : Strings) :
    StringFamily a 0 (fun _ => x) := by constructor <;> intros <;> simp [stringEnergy_self]
lemma StringFamily.single {a : ι → FiniteEuclidean} {u : ℝ} {b : ι → FiniteEuclidean}
    (h : CopyPath a u b) : StringFamily a u (fun i => FreeMonoid.of (b i)) := by
  refine ⟨fun _ _ => rfl,?_⟩
  intro i j
  change ‖b i-b j‖^2+0=u*‖a i-a j‖^2
  simpa only [add_zero] using h.2 i j
lemma StringFamily.mul {a : ι → FiniteEuclidean} {u v : ℝ} {x y : ι → Strings}
    (hx : StringFamily a u x) (hy : StringFamily a v y) : StringFamily a (u+v) (x*y) := by
  refine ⟨?_,?_⟩
  · intro i j
    change ((x i).toList++(y i).toList).length=((x j).toList++(y j).toList).length
    simp only [List.length_append,hx.1 i j,hy.1 i j]
  · intro i j
    change stringEnergy ((x i).toList++(y i).toList) ((x j).toList++(y j).toList)=_
    rw [stringEnergy_append _ _ _ _ (hx.1 i j),hx.2,hy.2,add_mul]
end EuclideanRamsey

end

end OAI

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

lemma ColumnPath.realizes {a : ι → FiniteEuclidean} {qs u} (h : ColumnPath a qs u)
    (xs : List (ι → Strings)) (hx : List.Forall₂ UltraColumn.Realizes qs xs) :
    StringFamily a u (fun i => (xs.map (fun x => x i)).prod) := by
  induction h generalizing xs with
  | nil =>
    cases hx
    simpa using StringFamily.common a 1
  | common U =>
    cases hx with
    | cons hx hn =>
      cases hn
      obtain ⟨x,hx⟩ := hx
      simpa [hx] using StringFamily.common a x
  | copy b hb =>
    cases hx with
    | cons hx hn =>
      cases hn
      change _ = _ at hx
      subst hx
      simpa using StringFamily.single hb
  | @append p q u v _ _ ihp ihq =>
    have hp : List.Forall₂ UltraColumn.Realizes p (xs.take p.length) := by
      have hh := List.forall₂_take p.length hx
      simpa only [List.take_left] using hh
    have hq : List.Forall₂ UltraColumn.Realizes q (xs.drop p.length) := by
      have hh := List.forall₂_drop p.length hx
      simpa only [List.drop_left] using hh
    have hmul := (ihp (xs.take p.length) hp).mul (ihq (xs.drop p.length) hq)
    have he : (fun i => ((xs.take p.length).map (fun x => x i)).prod) *
        (fun i => ((xs.drop p.length).map (fun x => x i)).prod) =
        (fun i => (xs.map (fun x => x i)).prod) := by
      funext i
      simp only [Pi.mul_apply,← List.prod_append,← List.map_append,List.take_append_drop]
    rwa [he] at hmul

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


theorem solution.{uIndex} : type_of% @_root_.OAI.EuclideanRamsey.ColumnPath.realizes.{uIndex} := @_root_.OAI.EuclideanRamsey.ColumnPath.realizes.{uIndex}
