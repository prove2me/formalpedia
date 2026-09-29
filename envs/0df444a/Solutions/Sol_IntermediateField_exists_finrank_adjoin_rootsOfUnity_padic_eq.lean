-- Prove2me | solution 1 for IntermediateField.exists_finrank_adjoin_rootsOfUnity_padic_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d6738cb8-b155-5cf9-bc6f-775007964a14

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_ExtCitation_LocalLevel_exists_ramification_inertia_Rw
import Theorems.Thm_IntermediateField_finrank_adjoin_rootsOfUnity_padic_eq_orderOf
import Theorems.Thm_orderOf_unitOfCoprime_pow_sub_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_exists_finrank_adjoin_rootsOfUnity_padic_eq

set_option autoImplicit false
set_option maxHeartbeats 1600000
open IntermediateField
open ExtCitation.LocalLevel

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (n : ℕ) (hn : 0 < n) :
    ∃ N : ℕ, 0 < N ∧
      Module.finrank K (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) = n := by
  classical
  have hq : q.Prime := Fact.out
  obtain ⟨e, f, he, hf, -, hcardκ, -⟩ := ExtCitation.LocalLevel.exists_ramification_inertia_Rw q K
  have hN : 0 < f * n := Nat.mul_pos hf hn
  refine ⟨f * n, hN, ?_⟩
  rw [IntermediateField.finrank_adjoin_rootsOfUnity_padic_eq_orderOf q K (f * n) hN, hcardκ]
  have hQ1 : 1 < q ^ f := Nat.one_lt_pow hf.ne' hq.one_lt
  have hndvd : ¬ q ∣ q ^ (f * n) - 1 := by
    intro h
    have h1 : q ∣ q ^ (f * n) := dvd_pow_self q hN.ne'
    have h2 : 1 < q ^ (f * n) := Nat.one_lt_pow hN.ne' hq.one_lt
    have : q ∣ q ^ (f * n) - (q ^ (f * n) - 1) := Nat.dvd_sub h1 h
    rw [Nat.sub_sub_self h2.le] at this
    exact hq.one_lt.ne' (Nat.dvd_one.1 this)
  have hcop : (q ^ f).Coprime ((q ^ f) ^ n - 1) := by
    rw [← pow_mul]
    exact Nat.Coprime.pow_left f ((Nat.Prime.coprime_iff_not_dvd hq).2 hndvd)
  have hm : q ^ (f * n) - 1 = (q ^ f) ^ n - 1 := by rw [pow_mul]
  suffices H : ∀ M : ℕ, M = (q ^ f) ^ n - 1 → orderOf ((q ^ f : ℕ) : ZMod M) = n from H _ hm
  rintro M rfl
  have key := orderOf_unitOfCoprime_pow_sub_one (q ^ f) n hQ1 hn hcop
  rwa [← orderOf_units, ZMod.coe_unitOfCoprime] at key

end S_IntermediateField_exists_finrank_adjoin_rootsOfUnity_padic_eq
end P2MW
export P2MW.S_IntermediateField_exists_finrank_adjoin_rootsOfUnity_padic_eq (solution)
