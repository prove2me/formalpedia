-- Prove2me | solution 1 for GlobalTheory.posDef_gram_of_posDef_realExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:37:44.947828+00:00
-- url     : https://prove2.me/submissions/73137c5e-9e13-40eb-b3c2-0907d5146860

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Theorems.Thm_GlobalTheory_realExtBilin_tmul
import Theorems.Thm_GlobalTheory_realExt_tmul
import Theorems.Thm_GlobalTheory_realExt_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.realExtBilin_tmul
attribute [local simp] GlobalTheory.realExt_tmul

set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X : Type*} [AddCommGroup X]
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Fintype ι] (b : Basis ι ℤ X)
    {Q : QuadraticMap ℤ X ℝ} (hQ : (realExt Q).PosDef) :
    (Matrix.of fun i j => QuadraticMap.polar Q (b i) (b j)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun w hw => ?_
  · ext i j
    simp [QuadraticMap.polar_comm]
  · have h := hQ ((b.baseChange ℝ).equivFun.symm w)
      ((b.baseChange ℝ).equivFun.symm.map_ne_zero_iff.2 hw)
    rw [realExt_apply] at h
    have e : realExtBilin Q.polarBilin ((b.baseChange ℝ).equivFun.symm w)
        ((b.baseChange ℝ).equivFun.symm w) =
        star w ⬝ᵥ (Matrix.of fun i j => QuadraticMap.polar Q (b i) (b j)).mulVec w := by
      simp only [Basis.equivFun_symm_apply, Basis.baseChange_apply, map_sum, map_smul,
        LinearMap.sum_apply, LinearMap.smul_apply, realExtBilin_tmul, dotProduct, Matrix.mulVec,
        Finset.mul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm Q (b j) (b i),
        smul_eq_mul, Matrix.of_apply, Pi.star_apply, star_trivial]
      ring
    linarith
end GlobalTheory
