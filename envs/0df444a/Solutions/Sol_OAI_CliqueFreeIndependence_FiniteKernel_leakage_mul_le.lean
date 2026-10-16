-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.FiniteKernel.leakage_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:22:22.907121+00:00
-- url     : https://prove2.me/submissions/0cebfc89-8daf-44af-9612-fd32f81a8141

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/FiniteKernel.lean:L370-L386
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.FiniteKernel.leakage_mul_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel

-- ---- from OAI.Combinatorics.CliqueFree.FiniteKernel ----
namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace FiniteKernel

open FiniteEntropy
variable {I : Type u} [Fintype I]

attribute [local instance] OAI.CliqueFreeIndependence.FiniteKernel.instDecidableEq_oAI
variable {J : Type v}

lemma rowMass_le_one {K : Kernel I} (hK : Stochastic K) (i : I) (A : Finset I) :
    rowMass K i A ≤ 1 := by
  rw [← (hK i).2]
  exact sum_le_univ_sum_of_nonneg (hK i).1

lemma rowMass_mul (P Q : Kernel I) (i : I) (A : Finset I) :
    rowMass (P * Q) i A = ∑ j, P i j * rowMass Q j A := by
  unfold rowMass
  simp only [Matrix.mul_apply, mul_sum]
  rw [sum_comm]

lemma leakage_mul_le {P Q : Kernel I} (hP : Stochastic P) (hQ : Stochastic Q)
    (i : I) (A B : Finset I) :
    rowMass (P * Q) i Bᶜ ≤ rowMass P i Aᶜ + ∑ y ∈ Bᶜ, ∑ z ∈ A, P i z * Q z y := by
  rw [rowMass_mul]
  have hsplit : (∑ j, P i j * rowMass Q j Bᶜ) =
      (∑ j ∈ A, P i j * rowMass Q j Bᶜ) + ∑ j ∈ Aᶜ, P i j * rowMass Q j Bᶜ :=
    (sum_add_sum_compl A _).symm
  rw [hsplit]
  have hle : (∑ j ∈ Aᶜ, P i j * rowMass Q j Bᶜ) ≤ rowMass P i Aᶜ := by
    exact sum_le_sum fun j _ ↦ by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (rowMass_le_one hQ j Bᶜ) ((hP i).1 j)
  have he : (∑ j ∈ A, P i j * rowMass Q j Bᶜ) = ∑ y ∈ Bᶜ, ∑ z ∈ A, P i z * Q z y := by
    simp only [rowMass, mul_sum]
    rw [sum_comm]
  rw [he]
  linarith

end FiniteKernel

end CliqueFreeIndependence

end

end OAI

-- ---- platform node ----
open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.FiniteKernel
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
open FiniteEntropy
attribute [local instance] OAI.CliqueFreeIndependence.FiniteKernel.instDecidableEq_oAI


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.FiniteKernel.leakage_mul_le.{u} := @_root_.OAI.CliqueFreeIndependence.FiniteKernel.leakage_mul_le.{u}
