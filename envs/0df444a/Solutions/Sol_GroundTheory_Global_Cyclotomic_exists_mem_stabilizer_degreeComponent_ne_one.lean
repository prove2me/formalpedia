-- Prove2me | solution 1 for GroundTheory.Global.Cyclotomic.exists_mem_stabilizer_degreeComponent_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:56:03.346096+00:00
-- url     : https://prove2.me/submissions/b0231d52-d29c-4196-a1b2-90fc86258d39

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_Degree
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_DegreeDecomposition
import Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_mem_stabilizer_modCharacter_eq_prime
import Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_mem_stabilizer_modCharacter_eq_of_prime_pow
import Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_degreeComponent_ne_one
import Theorems.Thm_GroundTheory_Global_Cyclotomic_genLog_ne_zero
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_padicEquiv_symm_apply
import Theorems.Thm_GroundTheory_Global_Cyclotomic_val_unitsPadicEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.padicEquiv_symm_apply
attribute [local simp] GroundTheory.Global.Cyclotomic.val_unitsPadicEquiv_apply



set_option autoImplicit false
open NumberField IntermediateField Filter Topology
open scoped GroundTheory.LocalField.Abstract Pointwise
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract
local notation "ℚ̄" => AlgebraicClosure ℚ
namespace GroundTheory.Global.Cyclotomic
theorem _root_.solution {p : ℕ} [hp : Fact p.Prime]
    (P : Ideal (𝓞 ℚ̄)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] (q : Nat.Primes) :
    ∃ σ ∈ MulAction.stabilizer Gal(ℚ̄/ℚ) P, degreeComponent q σ ≠ 1 := by
  have : NeZero (q : ℕ) := ⟨q.2.ne_zero⟩
  by_cases hpq : p = q
  · have hw : padicUnitsLog q (genPadicUnit q) ≠ 1 := by
      intro h
      have := padicUnitsLog_genPadicUnit (q : ℕ)
      rw [h, toAdd_one] at this
      exact genLog_ne_zero q (Nat.cast_eq_zero.1 this.symm)
    obtain ⟨N, hN, hσ⟩ := exists_degreeComponent_ne_one q _ hw
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
    subst hpq
    obtain ⟨σ, hσP, hσa⟩ := exists_mem_stabilizer_modCharacter_eq_of_prime_pow P k
      (redUnits q (k + 1) (genPadicUnit q))
    exact ⟨σ, hσP, hσ σ (by rw [hσa, coe_redUnits])⟩
  · have hcop : Nat.Coprime q p := (Nat.coprime_primes q.2 hp.out).2 (Ne.symm hpq)
    have hw : padicUnitsLog q (isUnit_natCast_of_coprime (q : ℕ) hcop).unit ≠ 1 := by
      intro h
      rw [padicUnitsLog_eq_one_iff] at h
      have h2 := congrArg (fun u : ℤ_[q]ˣ => (u : ℤ_[q])) h
      simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at h2
      rw [← Nat.cast_pow, ← Nat.cast_one, Nat.cast_inj, Nat.pow_eq_one] at h2
      rcases h2 with h2 | h2
      · exact hp.out.one_lt.ne' h2
      · exact (torsionExponent_pos q).ne' h2
    obtain ⟨N, -, hσ⟩ := exists_degreeComponent_ne_one q _ hw
    have hM : ¬ p ∣ (q : ℕ) ^ N := fun h =>
      hpq ((Nat.prime_dvd_prime_iff_eq hp.out q.2).1 (hp.out.dvd_of_dvd_pow h))
    obtain ⟨σ, hσP, hσp⟩ := exists_mem_stabilizer_modCharacter_eq_prime P hM
    exact ⟨σ, hσP, hσ σ (by rw [hσp, IsUnit.unit_spec, map_natCast])⟩
end GroundTheory.Global.Cyclotomic
