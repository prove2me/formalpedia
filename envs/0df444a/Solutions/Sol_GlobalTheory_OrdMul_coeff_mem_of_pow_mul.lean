-- Prove2me | solution 1 for GlobalTheory.OrdMul.coeff_mem_of_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:37:40.927005+00:00
-- url     : https://prove2.me/submissions/95323901-73b9-47bc-97a0-f5a0f5268681

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CoeffMemOfPowMul
import Theorems.Thm_GlobalTheory_OrdMul_coeff_mem_of_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrdMul
open MvPolynomial
namespace GlobalTheory.OrdMul
theorem _root_.solution : ∀ (O : Type) [CommRing O] (I : Ideal O) (ι : Type) (K : Set ι) (q : ι), q ∉ K → ∀ (a F : MvPolynomial ι O) (N k : ℕ), a.coeff 0 = 0 → IsUnit (a.coeff (Finsupp.single q 1)) → (∀ m : ι →₀ ℕ, m.degree < N + k → (∀ j ∈ K, m j = 0) → (a ^ k * F).coeff m ∈ I) → ∀ m : ι →₀ ℕ, m.degree < N → (∀ j ∈ K, m j = 0) → F.coeff m ∈ I := by
  intro O _ I ι K q hq a F N k h0 hu H
  induction k generalizing F N with
  | zero =>
    intro m hm hK
    simpa using H m (by simpa using hm) hK
  | succ k ih =>
    refine coeff_mem_of_mul I K q hq a F N h0 hu ?_
    refine ih (a * F) (N + 1) ?_
    intro m hm hK
    have := H m (by omega) hK
    rwa [pow_succ, mul_assoc] at this
end GlobalTheory.OrdMul
