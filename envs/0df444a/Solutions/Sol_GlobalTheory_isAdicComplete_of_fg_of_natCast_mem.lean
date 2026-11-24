-- Prove2me | solution 1 for GlobalTheory.isAdicComplete_of_fg_of_natCast_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:10:16.112471+00:00
-- url     : https://prove2.me/submissions/ba256352-164d-43c1-8753-f56ff7d79f23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsAdicCompleteOfFgOfNatCastMem
import Theorems.Thm_GlobalTheory_isAdicComplete_of_pow_le_of_le
import Theorems.Thm_GlobalTheory_exists_pow_le_span_of_fg_of_integers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (p : ℕ), p ≠ 0 → IsAdicComplete (Ideal.span {(p : O)}) O → ∀ J : Ideal O, J.FG → J ≠ ⊤ → (p : O) ∈ J → IsAdicComplete J O := by
  intro C _ _ _ v O _ _ hv p hp hc J hJ hJ' hpJ
  have ha : v (algebraMap O C (p : O)) ≠ 0 := by
    rw [map_natCast, Ne, v.zero_iff]
    exact_mod_cast hp
  obtain ⟨n, hn⟩ := exists_pow_le_span_of_fg_of_integers hv hJ hJ' ha
  exact isAdicComplete_of_pow_le_of_le hc hn ((Ideal.span_singleton_le_iff_mem _).mpr hpJ)
end GlobalTheory
