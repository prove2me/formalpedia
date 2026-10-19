-- Prove2me | solution 1 for OAI.EuclideanRamsey.quadraticStencil_moments
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:10:01.53812+00:00
-- url     : https://prove2.me/submissions/be41762e-0870-4a37-be7c-b025c2c15676

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/LatticeMoments.lean:L245-L262
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.quadraticStencil_moments. The node keeps its source
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

-- ---- from OAI.Combinatorics.EuclideanRamsey.LatticeMoments ----
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
namespace EuclideanRamsey

section Algebra
variable {k : ℕ}

lemma quadraticStencil_moments (C : Matrix (Fin k) (Fin k) ℚ) (hC : C.IsSymm)
    (l : Fin k → LatticeRing k) (hm : ∀ a, mass (l a) = 0)
    (hf : ∀ a b, firstMoment (l a) b = if a = b then 1 else 0) :
    mass (quadraticStencil C l) = 0 ∧ (∀ a, firstMoment (quadraticStencil C l) a = 0) ∧
      (∀ a b, secondMoment (quadraticStencil C l) a b = C a b) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simp [quadraticStencil, hm]
  · intro a
    simp [quadraticStencil, firstMoment_mul, hm]
  · intro a b
    simp only [quadraticStencil, secondMoment_smul, secondMoment_sum, secondMoment_mul, hm,
      hf, zero_mul, mul_zero, zero_add]
    simp only [mul_add, Finset.sum_add_distrib]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hs : C b a = C a b := congrFun (congrFun hC a) b
    rw [hs]
    ring

end Algebra
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


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.quadraticStencil_moments := @_root_.OAI.EuclideanRamsey.quadraticStencil_moments
