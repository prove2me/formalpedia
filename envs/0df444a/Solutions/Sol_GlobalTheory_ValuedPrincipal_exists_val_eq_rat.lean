-- Prove2me | solution 1 for GlobalTheory.ValuedPrincipal.exists_val_eq_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:22:13.016802+00:00
-- url     : https://prove2.me/submissions/9f7e1ece-d82e-4258-91aa-bee0a1e459a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsLeastOfDiscrete
import Theorems.Thm_GlobalTheory_ValuedPrincipal_exists_val_eq
import Theorems.Thm_GlobalTheory_ValuedPrincipal_exists_val_eq_int
import Theorems.Thm_GlobalTheory_ValuedPrincipal_val_pow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ValuedPrincipal
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))
namespace GlobalTheory.ValuedPrincipal
theorem _root_.solution [IsAlgClosed F] {π : F} (hπ : v π = ((1 : ℚ) : WithTop ℚ)) (q : ℚ) :
    ∃ t : F, t ≠ 0 ∧ v t = (q : WithTop ℚ) := by
  obtain ⟨y, hy, hyv⟩ := exists_val_eq_int v hπ q.num
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq y q.den_pos
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_pow q.den_ne_zero] at ht
    exact hy ht.symm
  obtain ⟨s, hs, -⟩ := exists_val_eq v ht0
  refine ⟨t, ht0, ?_⟩
  have hp := val_pow_eq v hs q.den
  rw [ht, hyv] at hp
  have hq : (q.num : ℚ) = q.den * s := by exact_mod_cast hp
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  rw [hs]
  congr 1
  rw [← Rat.num_div_den q, eq_div_iff hd, hq]
  ring
end GlobalTheory.ValuedPrincipal
