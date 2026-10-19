-- Prove2me | solution 1 for OAI.EuclideanRamsey.latticeSample_finite_support
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:20:49.043313+00:00
-- url     : https://prove2.me/submissions/3cdebdfe-82cd-4e81-9d52-63d7b53ab27a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Discretization.lean:L190-L214
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.latticeSample_finite_support. The node keeps its source
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

end EuclideanRamsey

open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
namespace EuclideanRamsey

lemma latticeSample_finite_support {k n : ℕ} (hn : n ≠ 0)
    {f : (Fin k → ℝ) → ℝ} (hf : HasCompactSupport f) :
    Function.HasFiniteSupport (fun γ : Fin k → ℤ => f (latticeSample n γ)) := by
  let b := Pi.basisFun ℝ (Fin k)
  have hb : Bornology.IsBounded ((n:ℝ) • tsupport f) :=
    (hf.isCompact.image (show Continuous (fun x : Fin k → ℝ => (n:ℝ) • x) by fun_prop)).isBounded
  have hfinite := ZSpan.setFinite_inter b hb
  let cast : (Fin k → ℤ) → (Fin k → ℝ) := fun γ j => γ j
  have hinj : Function.Injective cast := by
    intro x y h
    ext j
    have he : (x j : ℝ) = (y j : ℝ) := congr_fun h j
    exact_mod_cast he
  apply ((hfinite.preimage hinj.injOn).subset ?_)
  intro γ hγ
  have hs : latticeSample n γ ∈ tsupport f := subset_closure hγ
  constructor
  · refine ⟨latticeSample n γ,hs,?_⟩
    ext j
    change (n:ℝ)*((γ j : ℝ)/n) = (γ j : ℝ)
    field_simp
  · change cast γ ∈ Submodule.span ℤ (Set.range b)
    rw [b.mem_span_iff_repr_mem ℤ]
    intro j
    exact ⟨γ j,by simp [b,cast]⟩

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
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.latticeSample_finite_support := @_root_.OAI.EuclideanRamsey.latticeSample_finite_support
