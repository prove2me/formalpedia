-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_sub_one_pow_eq_norm_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:37:18.413608+00:00
-- url     : https://prove2.me/submissions/689321d6-ad4c-40b4-9cad-50840678acda

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_KerFontaineThetaCompFrobeniusEquivSymmPow
import Definitions.Def_GroundTheory_PAdicHodge_AInfXi
import Theorems.Thm_GroundTheory_PAdicHodge_norm_sub_one_eq_of_isPrimitiveRoot_of_isUltrametricDist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open WittVector
open GroundTheory GroundTheory.PAdicHodge
variable {F : Type*} [NormedField F] [IsUltrametricDist F]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {p : ℕ} [hp : Fact p.Prime] {ζ : F} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) : ‖ζ - 1‖ ^ (p ^ k * (p - 1)) = ‖(p : F)‖ := by
  have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have h1 := Polynomial.eval_one_cyclotomic_prime_pow (R := F) (p := p) k
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h1
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1
  rw [← h1, norm_prod, Finset.prod_congr rfl fun μ hμ => (norm_sub_rev 1 μ).trans
    (norm_sub_one_eq_of_isPrimitiveRoot_of_isUltrametricDist hζ
      ((mem_primitiveRoots (Nat.pos_of_ne_zero (NeZero.ne _))).1 hμ)),
    Finset.prod_const, hζ.card_primitiveRoots, Nat.totient_prime_pow hp.out (Nat.succ_pos k),
    Nat.succ_sub_one]
end GroundTheory.PAdicHodge
