-- Prove2me | solution 1 for GlobalTheory.length_localizedModule_quotient_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:43.526676+00:00
-- url     : https://prove2.me/submissions/f4793a4c-eced-420b-99a2-0fa5e936fbcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable {S : Type*} [CommRing S]
namespace GlobalTheory
theorem _root_.solution (m n : Ideal S) [hm : m.IsMaximal] [hn : n.IsPrime]
    (h : n ≠ m) :
    Module.length (Localization.AtPrime n) (LocalizedModule n.primeCompl (S ⧸ m)) = 0 := by
  rw [Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
  have : ¬ m ≤ n := fun hle => h (hm.eq_of_le hn.ne_top hle).symm
  obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.mp this
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective m x
  refine ⟨s, hs', ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact m.mul_mem_right _ hs
end GlobalTheory
