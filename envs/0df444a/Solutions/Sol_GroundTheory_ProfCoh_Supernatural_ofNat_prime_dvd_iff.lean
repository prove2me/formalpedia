-- Prove2me | solution 1 for GroundTheory.ProfCoh.Supernatural.ofNat_prime_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:23:20.028133+00:00
-- url     : https://prove2.me/submissions/f150b1c4-aab4-46d3-902e-aaeeedb22f0c

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_Supernatural
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_le_def
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_dvd_iff_le
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_exp_ofNat
import Theorems.Thm_GroundTheory_ProfCoh_Supernatural_ofNat_one
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
theorem _root_.solution (p : Nat.Primes) (a : Supernatural) :
    ofNat p ∣ a ↔ 1 ≤ a.exp p := by
  have h1 : (ofNat p).exp p = 1 := by
    rw [exp_ofNat]
    simp [p.prop.factorization_self]
  rw [dvd_iff_le, le_def]
  constructor
  · intro h
    exact h1 ▸ h p
  · intro h q
    by_cases hq : q = p
    · subst hq
      exact h1 ▸ h
    · have hq' : (p : ℕ) ≠ q := fun e => hq (Subtype.ext e.symm)
      simp [p.prop.factorization, hq']
end GroundTheory.ProfCoh.Supernatural
