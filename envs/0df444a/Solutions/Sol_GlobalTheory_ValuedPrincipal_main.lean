-- Prove2me | solution 1 for GlobalTheory.ValuedPrincipal.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:32:52.934003+00:00
-- url     : https://prove2.me/submissions/741d56b3-91dc-4bcd-a47a-2e515efd8e9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExistsLeastOfDiscrete
import Theorems.Thm_GlobalTheory_ValuedPrincipal_exists_val_eq_rat
import Theorems.Thm_GlobalTheory_ValuedPrincipal_exists_least_of_discrete
import Theorems.Thm_GlobalTheory_ValuedPrincipal_exists_eq_mul_of_le

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
theorem _root_.solution : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (π : F), v π = ((1 : ℚ) : WithTop ℚ) → (IsAlgClosed F ∨ ∃ d : ℕ, 1 ≤ d ∧ ∀ x : F, x ≠ 0 → ∃ n : ℤ, v x = (((n : ℚ) / d : ℚ) : WithTop ℚ)) → ∀ q : ℚ, ∃ t : F, t ≠ 0 ∧ ((q : ℚ) : WithTop ℚ) ≤ v t ∧ ∀ a : F, ((q : ℚ) : WithTop ℚ) ≤ v a → ∃ c : F, (0 : WithTop ℚ) ≤ v c ∧ a = c * t := by
  intro F _ v π hπ hcase q
  have key : ∃ t : F, t ≠ 0 ∧ (q : WithTop ℚ) ≤ v t ∧
      ∀ a : F, (q : WithTop ℚ) ≤ v a → v t ≤ v a := by
    rcases hcase with hac | ⟨d, hd, hdisc⟩
    · haveI := hac
      obtain ⟨t, ht, htv⟩ := exists_val_eq_rat v hπ q
      refine ⟨t, ht, htv.ge, fun a ha => ?_⟩
      rw [htv]
      exact ha
    · exact exists_least_of_discrete v hπ hd hdisc q
  obtain ⟨t, ht, hqt, hmin⟩ := key
  exact ⟨t, ht, hqt, fun a ha => exists_eq_mul_of_le v ht (hmin a ha)⟩
end GlobalTheory.ValuedPrincipal
