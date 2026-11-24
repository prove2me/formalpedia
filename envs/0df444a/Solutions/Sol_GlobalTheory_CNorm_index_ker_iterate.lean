-- Prove2me | solution 1 for GlobalTheory.CNorm.index_ker_iterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:38:15.585605+00:00
-- url     : https://prove2.me/submissions/b60cd926-0dba-49ad-ace1-ce7fde6ee993

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_MemPowSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexRangeKerIterateEndomorphism
import Theorems.Thm_GlobalTheory_CNorm_index_range_ker_pow_succ_endomorphism

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
open GlobalTheory GlobalTheory.CNorm
namespace GlobalTheory.CNorm
theorem _root_.solution :
    ∀ (M : Type) [CommGroup M] (f : Monoid.End M) (k : ℕ), (MonoidHom.range (f ^ (k + 1) : Monoid.End M)).index ≠ 0 → Nat.card (MonoidHom.ker (f ^ (k + 1) : Monoid.End M)) ≠ 0 → (MonoidHom.range f).index ≠ 0 ∧ Nat.card (MonoidHom.ker f) ≠ 0 ∧ (MonoidHom.range (f ^ (k + 1) : Monoid.End M)).index * Nat.card (MonoidHom.ker f) ^ (k + 1) = (MonoidHom.range f).index ^ (k + 1) * Nat.card (MonoidHom.ker (f ^ (k + 1) : Monoid.End M)) := by
  intro M _ f k hI hK
  have hr : MonoidHom.range (f ^ (k + 1) : Monoid.End M) ≤ MonoidHom.range f := by
    rintro _ ⟨x, rfl⟩
    exact ⟨(f ^ k : Monoid.End M) x, by rw [pow_succ']; rfl⟩
  have hk : MonoidHom.ker f ≤ MonoidHom.ker (f ^ (k + 1) : Monoid.End M) := by
    intro x hx
    have hx' : f x = 1 := hx
    rw [pow_succ]
    change (f ^ k : Monoid.End M) (f x) = 1
    rw [hx', map_one]
  have hK' : Nat.card (MonoidHom.ker f) ≠ 0 :=
    ne_zero_of_dvd_ne_zero hK (Subgroup.card_dvd_of_le hk)
  exact ⟨ne_zero_of_dvd_ne_zero hI (Subgroup.index_dvd_of_le hr), hK',
    (index_range_ker_pow_succ_endomorphism f hK' k).2⟩
end GlobalTheory.CNorm
