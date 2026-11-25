-- Prove2me | solution 1 for GroundTheory.ProfCoh.Supernatural.ofNat_prime_dvd_iSup_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:32:37.686826+00:00
-- url     : https://prove2.me/submissions/7d7ed7de-eba5-42d2-96c0-2b9f2dca2438

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_exp_ofNat
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_ofNat_one
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_ofNat_prime_dvd_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.Supernatural.exp_ofNat
attribute [local simp] GroundTheory.ProfCoh.Supernatural.ofNat_one

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open GroundTheory.ProfCoh.Supernatural
namespace GroundTheory.ProfCoh.Supernatural
theorem _root_.solution (p : Nat.Primes) {ι : Sort*} (f : ι → Supernatural) :
    ofNat p ∣ ⨆ i, f i ↔ ∃ i, ofNat p ∣ f i := by
  simp only [ofNat_prime_dvd_iff p, Order.one_le_iff_ne_zero]
  rw [exp_iSup]
  constructor
  · intro h
    by_contra h'
    simp only [not_exists, ne_eq, not_not] at h'
    exact h (le_antisymm (iSup_le fun i => (h' i).le) zero_le)
  · rintro ⟨i, hi⟩ h
    exact hi (le_antisymm (h ▸ le_iSup (fun i => (f i).exp p) i) zero_le)
end GroundTheory.ProfCoh.Supernatural
