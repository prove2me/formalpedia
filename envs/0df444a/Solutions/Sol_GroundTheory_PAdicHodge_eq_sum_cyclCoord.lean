-- Prove2me | solution 1 for GroundTheory.PAdicHodge.eq_sum_cyclCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:45:12.450411+00:00
-- url     : https://prove2.me/submissions/ccbcc037-d27c-4fae-807e-2a7c5028c757

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_cycl_isPrimitiveRoot
import Theorems.Thm_GroundTheory_PAdicHodge_exists_eq_sum_pow_of_adjoin_eq
import Theorems.Thm_GroundTheory_PAdicHodge_cycl_eq_adjoin
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_mul_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_of_mem
import Theorems.Thm_GroundTheory_PAdicHodge_normTrace_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {η : PadicAlgCl p}
    (hη : IsPrimitiveRoot η (p ^ (k + 1))) {y : PadicAlgCl p} (hy : y ∈ cycl p (k + 1)) :
    y = ∑ i ∈ Finset.range p, cyclCoord k η y i * η ^ i := by
  have hpr := (Fact.out : p.Prime)
  obtain ⟨b, hb, hyb⟩ := exists_eq_sum_pow_of_adjoin_eq hk (cycl_eq_adjoin hη).symm hy
  have hcoord : ∀ i ∈ Finset.range p, cyclCoord k η y i = b i := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    have hle : i ≤ p ^ (k + 1) := le_trans hi'.le (Nat.le_self_pow (by omega) p)
    rw [cyclCoord, hyb, Finset.sum_mul, normTrace_sum, Finset.sum_eq_single i]
    · rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hle, hη.pow_eq_one, mul_one,
        normTrace_of_mem _ (hb i)]
    · intro j hj hji
      have hj' := Finset.mem_range.1 hj
      rw [mul_assoc, ← pow_add, normTrace_mul_of_mem _ (hb j)]
      have hcop : (j + (p ^ (k + 1) - i)).Coprime (p ^ (k + 1)) := by
        refine Nat.Coprime.pow_right _ (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hpr).2
          fun h => hji ?_))
        have h' : (p : ℤ) ∣ ((j : ℤ) - i) := by
          have e : ((j + (p ^ (k + 1) - i) : ℕ) : ℤ) = (p : ℤ) * (p : ℤ) ^ k + ((j : ℤ) - i) := by
            push_cast [Nat.cast_sub hle]; ring
          have h2 : (p : ℤ) ∣ ((j + (p ^ (k + 1) - i) : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 h
          rw [e] at h2
          exact (dvd_add_right (dvd_mul_right _ _)).1 h2
        have habs : |(j : ℤ) - i| < p := by rw [abs_lt]; constructor <;> omega
        have := Int.eq_zero_of_abs_lt_dvd h' habs
        omega
      rw [normTrace_cycl_isPrimitiveRoot hk (hη.pow_of_coprime _ hcop), mul_zero]
    · intro h; exact absurd hi h
  calc y = ∑ i ∈ Finset.range p, b i * η ^ i := hyb
    _ = _ := Finset.sum_congr rfl fun i hi => by rw [hcoord i hi]
end GroundTheory.PAdicHodge
