-- Prove2me | solution 1 for GlobalTheory.Hk.RayConv.sum_lamIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:49:22.258451+00:00
-- url     : https://prove2.me/submissions/c9e34aa5-c4b9-4ac4-8afc-dd084daa24fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiniteIdealsIn
import Theorems.Thm_GlobalTheory_Hk_RayConv_lamIdeal_pow
import Theorems.Thm_GlobalTheory_Hk_RayConv_finite_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayConv
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Hk.RayConv
theorem _root_.solution (I : Ideal (𝓞 K)) : I ≠ 0 → ∀ T : Finset (Ideal (𝓞 K)), (∀ J, J ∈ T ↔ J ∣ I) →
    ∑ J ∈ T, lamIdeal J = Real.log (Ideal.absNorm I) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact (h rfl).elim
  | h₂ I hu =>
    intro _ T hT
    have h1 : I = 1 := isUnit_iff_eq_one.1 hu
    subst h1
    rw [map_one, Nat.cast_one, Real.log_one]
    refine Finset.sum_eq_zero fun J hJ => ?_
    unfold lamIdeal
    rw [if_neg]
    rintro ⟨P, k, hP, hP0, hk, rfl⟩
    have := isUnit_of_dvd_one ((hT _).1 hJ)
    rw [isUnit_pow_iff (by omega), Ideal.isUnit_iff] at this
    exact hP.ne_top this
  | h₃ I P hI hP ih =>
    intro _ T hT
    set S := (finite_dvd hI).toFinset with hS
    have hSm : ∀ J, J ∈ S ↔ J ∣ I := fun J => by simp [hS]
    have hsub : S ⊆ T := fun J hJ => (hT J).2 (((hSm J).1 hJ).mul_left P)
    have hfin : FiniteMultiplicity P I := FiniteMultiplicity.of_prime_left hP hI
    have hN : ∀ J : Ideal (𝓞 K), J ≠ 0 → ((Ideal.absNorm J : ℕ) : ℝ) ≠ 0 := fun J hJ =>
      Nat.cast_ne_zero.2 fun h => hJ (Ideal.absNorm_eq_zero_iff.1 h)
    rw [← Finset.sum_sdiff hsub, ih hI S hSm, map_mul, Nat.cast_mul, Real.log_mul (hN _ hP.ne_zero) (hN _ hI)]
    congr 1
    rw [Finset.sum_eq_single_of_mem (P ^ (multiplicity P I + 1)), lamIdeal_pow hP]
    · rw [Finset.mem_sdiff, hT, hSm]
      refine ⟨?_, hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)⟩
      rw [pow_succ']
      exact mul_dvd_mul_left _ (pow_multiplicity_dvd _ _)
    · intro J hJ hne
      rw [Finset.mem_sdiff, hT, hSm] at hJ
      unfold lamIdeal
      rw [if_neg]
      rintro ⟨Q, k, hQ, hQ0, hk, rfl⟩
      have hQp : Prime Q := Ideal.prime_of_isPrime hQ0 hQ
      by_cases hQP : Q = P
      · subst hQP
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have h1 : Q ^ j ∣ I := by
          have := hJ.1
          rw [pow_succ'] at this
          exact (mul_dvd_mul_iff_left hP.ne_zero).1 this
        have h2 : j ≤ multiplicity Q I := hfin.le_multiplicity_of_pow_dvd h1
        have h3 : ¬ j + 1 ≤ multiplicity Q I := fun h => hJ.2 (pow_dvd_of_le_multiplicity h)
        exact hne (by rw [show j = multiplicity Q I by omega])
      · refine hJ.2 (hQp.pow_dvd_of_dvd_mul_left k ?_ hJ.1)
        intro hd
        exact hQP (associated_iff_eq.1 ((hQp.dvd_prime_iff_associated hP).1 hd))
end GlobalTheory.Hk.RayConv
