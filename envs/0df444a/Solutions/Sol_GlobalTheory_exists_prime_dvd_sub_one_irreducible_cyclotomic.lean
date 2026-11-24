-- Prove2me | solution 1 for GlobalTheory.exists_prime_dvd_sub_one_irreducible_cyclotomic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:11:20.313637+00:00
-- url     : https://prove2.me/submissions/17e12e23-e098-4a74-bbcf-5162b200eb98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeDvdSubOneCyclotomicIrreducibleOver
import Theorems.Thm_GlobalTheory_irreducible_cyclotomic_of_not_dvd_discr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), n ≠ 0 →
      ∃ m : ℕ, m.Prime ∧ n ∣ m - 1 ∧ Irreducible (cyclotomic m K) := by
  intro K _ _ n hn
  obtain ⟨m, hmp, hgt, hmod⟩ := Nat.exists_prime_gt_modEq_one (NumberField.discr K).natAbs hn
  refine ⟨m, hmp, (Nat.modEq_iff_dvd' hmp.one_le).mp hmod.symm, ?_⟩
  apply irreducible_cyclotomic_of_not_dvd_discr K m hmp
  intro h
  have hne : NumberField.discr K ≠ 0 := NumberField.discr_ne_zero K
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (Int.natCast_dvd.mp h)
  omega
end GlobalTheory
