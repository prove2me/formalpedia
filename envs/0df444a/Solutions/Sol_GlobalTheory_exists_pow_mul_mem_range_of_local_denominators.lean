-- Prove2me | solution 1 for GlobalTheory.exists_pow_mul_mem_range_of_local_denominators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:26:29.893662+00:00
-- url     : https://prove2.me/submissions/b283642d-22be-45b5-a32e-6739f82d437e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__DimEqZero_40b4adf5f58b53e3
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsPowMulMemRangeOfLocalDenominators
import Theorems.Thm_GlobalTheory_exists_dvd_pow_of_forall_prime_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A B : Type} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] [CommRing B] [IsDomain B] (φ : A →+* B)
    (hφ : Function.Injective φ) (W : Set (PrimeSpectrum A)) (hW : W.Nonempty) (a : A)
    (ha : ∀ (q : A) (p : PrimeSpectrum A), Prime q → p.asIdeal = Ideal.span {q} → p ∉ W → q ∣ a)
    (v : B) (hv : ∀ p ∈ W, ∃ s, s ∉ p.asIdeal ∧ ∃ x, φ x = φ s * v) :
    ∃ (n : ℕ) (x : A), φ x = φ a ^ n * v := by
  obtain ⟨p₀, hp₀⟩ := hW
  obtain ⟨s, hs, x, e⟩ := hv p₀ hp₀
  have hs0 : s ≠ 0 := fun h => hs (h ▸ p₀.asIdeal.zero_mem)
  obtain ⟨y, x', c, hrel, rfl, rfl⟩ := UniqueFactorizationMonoid.exists_reduced_factors s hs0 x
  have hc : c ≠ 0 := left_ne_zero_of_mul hs0
  have hy : y ≠ 0 := right_ne_zero_of_mul hs0
  have e' : φ x' = φ y * v := by
    rw [map_mul, map_mul, _root_.mul_assoc] at e
    exact mul_left_cancel₀ ((map_ne_zero_iff _ hφ).mpr hc) e
  obtain ⟨n, z, hz⟩ := exists_dvd_pow_of_forall_prime_dvd a y hy fun q hq hqy => by
    refine ha q ⟨Ideal.span {q}, (Ideal.span_singleton_prime hq.ne_zero).2 hq⟩ hq rfl fun hm => ?_
    obtain ⟨t, ht, w, ew⟩ := hv _ hm
    refine ht (Ideal.mem_span_singleton.2 (hqy.trans (hrel.dvd_of_dvd_mul_right ⟨w, hφ ?_⟩)))
    rw [map_mul, map_mul, e', ew, mul_left_comm]
  refine ⟨n, z * x', ?_⟩
  rw [← map_pow, hz, map_mul, map_mul, e']
  ring
end GlobalTheory
