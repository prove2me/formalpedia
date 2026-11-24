-- Prove2me | solution 1 for GlobalTheory.traceDual_integral_of_not_dvd_discr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:37:49.766864+00:00
-- url     : https://prove2.me/submissions/7c684964-9cf1-48b0-8d44-6f2910020134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftOfTraceDualElement
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ), l.Prime → ¬ (l : ℤ) ∣ discr E → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → ∀ (σ : E →+* K) (y : E), (∀ x : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E (y * x) = n) → ∃ z : O, algebraMap O K z = σ y := by
  intro E _ _ _ l hl hd O _ _ _ _ K _ _ _ hlm σ y hy

  have hmem : y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨x, rfl⟩ := Submodule.mem_one.mp ha
    obtain ⟨k, hk⟩ := hy x
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply, hk]
    simp
  have hb : ∀ i, IsIntegral ℤ (integralBasis E i) := fun i => by
    rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
  have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hint0 := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) hb h1 hmem
  rw [← coe_discr, Algebra.smul_def, mul_one] at hint0
  have hint : IsIntegral ℤ ((NumberField.discr E : E) * y) := by simpa using hint0

  have hσ : IsIntegral ℤ (σ ((NumberField.discr E : E) * y)) := hint.map σ.toIntAlgHom
  have hO : IsIntegral O (σ ((NumberField.discr E : E) * y)) := hσ.tower_top
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hO

  have hcop : IsCoprime (l : ℤ) (NumberField.discr E) :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hl).irreducible).mpr hd
  obtain ⟨a, b, hab⟩ := hcop
  have hu : IsUnit ((NumberField.discr E : ℤ) : O) := by
    by_contra hn
    have hdm : ((NumberField.discr E : ℤ) : O) ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr hn
    have hlm' : ((l : ℤ) : O) ∈ IsLocalRing.maximalIdeal O := by simpa using hlm
    have h1m : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have : ((a : O) * ((l : ℤ) : O) + (b : O) * ((NumberField.discr E : ℤ) : O)) = 1 := by
        exact_mod_cast congrArg (Int.cast (R := O)) hab
      rw [← this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hlm') (Ideal.mul_mem_left _ _ hdm)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1m)
  obtain ⟨u, hu'⟩ := hu
  refine ⟨(u⁻¹ : Oˣ) * z, ?_⟩
  rw [map_mul, hz, map_mul, map_intCast, ← map_intCast (algebraMap O K), ← hu', ← mul_assoc,
    ← map_mul, Units.inv_mul, map_one, one_mul]
end GlobalTheory
