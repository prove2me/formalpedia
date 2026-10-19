-- Prove2me | solution 1 for OAI.EuclideanRamsey.bilinear_moment_contract
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:14:36.059543+00:00
-- url     : https://prove2.me/submissions/608ec843-0483-4225-89c5-e5e08bb22b1a

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Discretization.lean:L82-L108
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.bilinear_moment_contract. The node keeps its source
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

lemma bilinear_moment_contract {ι : Type uIndex} {k : ℕ}
    (S : Finset ι) (q : ι → ℝ) (v : ι → (Fin k → ℝ))
    (L : (Fin k → ℝ) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℝ) :
    ∑ γ ∈ S,q γ*L (v γ) (v γ) =
      ∑ j,∑ l,(∑ γ ∈ S,q γ*v γ j*v γ l)*L (Pi.single j 1) (Pi.single l 1) := by
  have hv (γ : ι) : v γ = ∑ j, v γ j • Pi.single j (1:ℝ) := by
    ext l
    simp [Pi.single_apply]
  have he (γ : ι) : q γ*L (v γ) (v γ) =
      ∑ j,∑ l,q γ*v γ j*v γ l*L (Pi.single j 1) (Pi.single l 1) := by
    have hfirst := congrArg (fun a => L a (v γ)) (hv γ)
    rw [hfirst]
    simp only [map_sum,map_smul,_root_.sum_apply,
      _root_.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hsecond := congrArg (fun a => L (Pi.single j 1) a) (hv γ)
    rw [hsecond]
    simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    ring
  simp only [he,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]

end EuclideanRamsey

open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
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
open MeasureTheory
open scoped BigOperators
open scoped BigOperators


theorem solution.{uIndex} : type_of% @_root_.OAI.EuclideanRamsey.bilinear_moment_contract.{uIndex} := @_root_.OAI.EuclideanRamsey.bilinear_moment_contract.{uIndex}
