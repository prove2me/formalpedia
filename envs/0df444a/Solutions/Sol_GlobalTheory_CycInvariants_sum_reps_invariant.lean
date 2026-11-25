-- Prove2me | solution 1 for GlobalTheory.CycInvariants.sum_reps_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:13:46.256822+00:00
-- url     : https://prove2.me/submissions/c2d04e7a-6cf7-4bd4-89a1-fd0c4351adb2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerTraceAlmostSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumMulLeftTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegers
import Theorems.Thm_GlobalTheory_LeftTransversalSum_sum_mul_left_transversal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycInvariants
namespace GlobalTheory.CycInvariants
theorem _root_.solution {G M : Type} [Group G] [AddCommMonoid M] (H N : Subgroup G)
    (S : Finset G) (hS : ∀ s ∈ S, s ∈ H) (hu : ∀ h ∈ H, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N)
    (f : G → M) (hf : ∀ g, ∀ n ∈ N, f (g * n) = f g) (h : G) (hh : h ∈ H) :
    ∑ s ∈ S, f (h * s) = ∑ s ∈ S, f s := by
  first
  | exact @_root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal
  | exact _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal
  | (apply _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal <;> assumption)
  | (intros; apply _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LeftTransversalSum.sum_mul_left_transversal ..)
end GlobalTheory.CycInvariants
