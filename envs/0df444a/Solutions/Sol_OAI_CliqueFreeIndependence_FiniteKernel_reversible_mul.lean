-- Prove2me | solution 1 for OAI.CliqueFreeIndependence.FiniteKernel.reversible_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T00:18:09.189439+00:00
-- url     : https://prove2.me/submissions/d5779c1f-9a1d-44a1-b8a8-98582c5b94d0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/FiniteKernel.lean:L99-L115
-- (upload_full_project.md Phase 4): solution for node OAI.CliqueFreeIndependence.FiniteKernel.reversible_mul. The node keeps its source
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
lemma reversible_mul {π : I → ℝ} {P Q : Kernel I}
    (hP : Reversible π P) (hQ : Reversible π Q) (hc : Commute P Q) :
    Reversible π (P * Q) := by
  intro i j
  rw [Matrix.mul_apply, mul_sum]
  calc
    _ = ∑ k, π j * (Q j k * P k i) := by
      apply sum_congr rfl
      intro k _
      calc
        _ = (π i * P i k) * Q k j := by ring
        _ = (π k * P k i) * Q k j := by rw [hP]
        _ = (π k * Q k j) * P k i := by ring
        _ = (π j * Q j k) * P k i := by rw [hQ]
        _ = _ := by ring
    _ = π j * (Q * P) j i := by rw [Matrix.mul_apply, mul_sum]
    _ = _ := by rw [hc.eq]

variable {J : Type v}

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


theorem solution.{u} : type_of% @_root_.OAI.CliqueFreeIndependence.FiniteKernel.reversible_mul.{u} := @_root_.OAI.CliqueFreeIndependence.FiniteKernel.reversible_mul.{u}
