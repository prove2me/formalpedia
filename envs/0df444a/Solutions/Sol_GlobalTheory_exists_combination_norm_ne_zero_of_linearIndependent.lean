-- Prove2me | solution 1 for GlobalTheory.exists_combination_norm_ne_zero_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:39:06.102891+00:00
-- url     : https://prove2.me/submissions/2aeceaae-b7c6-4ab8-827d-49435f88067e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsCombinationNormNeZeroOfLinearIndependentAl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    {B A : Type} [CommRing B] [IsDomain B] [CommRing A] [Algebra B A]
    [Module.Free B A] [Module.Finite B A] {d : ℕ} (hd : Module.finrank B A = d)
    (y : Fin d → A) (hy : LinearIndependent B y) :
    ∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0 := by
  classical
  let e := Module.finBasisOfFinrankEq B A hd
  let Y : Matrix (Fin d) (Fin d) B := fun i j => e.equivFun (y j) i
  have key : ∀ v : Fin d → B, e.equivFun (∑ j, v j • y j) = Y *ᵥ v := by
    intro v
    ext i
    simp [Y, Matrix.mulVec, dotProduct, mul_comm]
  have hdet : Y.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have h1 : ∑ j, v j • y j = 0 := by
      apply e.equivFun.injective
      rw [key, hv, map_zero]
    exact hv0 (funext fun j => Fintype.linearIndependent_iff.mp hy v h1 j)
  refine ⟨Y.adjugate *ᵥ e.equivFun 1, ?_⟩
  have hsum : ∑ j, (Y.adjugate *ᵥ e.equivFun 1) j • y j = algebraMap B A Y.det := by
    apply e.equivFun.injective
    rw [key, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, Algebra.algebraMap_eq_smul_one, map_smul]
  rw [hsum, Algebra.norm_algebraMap]
  exact pow_ne_zero _ hdet
end GlobalTheory
