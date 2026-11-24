-- Prove2me | solution 1 for GlobalTheory.DerivationPowerIdeal.derivation_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:19:24.539284+00:00
-- url     : https://prove2.me/submissions/f7084d85-3f80-44ab-aa75-6a21c2411636

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DerivationMemPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DerivationPowerIdeal
namespace GlobalTheory.DerivationPowerIdeal
theorem _root_.solution {A' : Type} [CommRing A'] {k : Type} [CommRing k] [Algebra k A']
    (I : Ideal A') (D : Derivation k A' A') (n : ℕ) {x : A'} (hx : x ∈ I ^ (n + 1)) :
    D x ∈ I ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' I (n + 1)] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ hb)
      rw [pow_succ' I n]
      exact Ideal.mul_mem_mul ha (ih hb)
    · intro a b ha hb
      rw [map_add]
      exact Ideal.add_mem _ ha hb
end GlobalTheory.DerivationPowerIdeal
