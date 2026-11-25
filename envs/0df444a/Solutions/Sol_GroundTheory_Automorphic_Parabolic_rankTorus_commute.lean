-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.rankTorus_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:12.719551+00:00
-- url     : https://prove2.me/submissions/f5e1c92e-32c9-4b03-9161-5605b7e1e81a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Induction
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_coe_torusPow
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_blockRank_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure
open scoped NNReal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) F) V)
variable {π} {V' : Type*} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ (GL (Fin n) F) V'}
  {V'' : Type*} [AddCommGroup V''] [Module ℂ V''] {π'' : Representation ℂ (GL (Fin n) F) V''}
variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (e : ℕ) {y : GL (Fin n) F}
    (hy : y ∈ levi F n β) : rankTorus F n β e * y = y * rankTorus F n β e := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Units.val_mul, Units.val_mul, rankTorus, coe_torusPow, diagonal_mul, mul_diagonal]
  by_cases h : β i = β j
  · rw [blockRank_eq h, mul_comm]
  · rw [mem_levi.1 hy i j h, mul_zero, zero_mul]
end GroundTheory.Automorphic.Parabolic
