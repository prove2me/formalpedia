-- Prove2me | solution 1 for GlobalTheory.DualCokernel.extZero_of_isRegularLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:13:28.654071+00:00
-- url     : https://prove2.me/submissions/fabf1127-4d98-471b-8f56-6f67d205b6b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExactDualMapOfExactFibresOfIsRegularLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory
open GlobalTheory.DualCokernel
namespace GlobalTheory.DualCokernel
theorem _root_.solution (R : Type) [CommRing R] [IsRegularLocalRing R] (g : ℕ)
    (hg : ringKrullDim R = g) (j : ℕ) (hj : j < g) : ExtZero (R := R) R j := by
  obtain ⟨xs, h, hd⟩ := exists_ofList_eq_maximalIdeal_length_eq R
  have hreg := isRegular_of_ofList_eq_maximalIdeal h hd.le
  have hlen : xs.length = g := by
    rw [hg] at hd
    exact_mod_cast hd
  refine ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) _ ?_ _ ?_ _ ?_ hreg j
    (by simpa [hlen] using hj)
  · rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  · rw [smul_eq_mul, Ideal.mul_top]
    exact (maximalIdeal.isMaximal R).ne_top.lt_top
  · intro r hr
    exact h ▸ Ideal.subset_span hr
end GlobalTheory.DualCokernel
