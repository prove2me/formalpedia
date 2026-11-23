-- Prove2me | solution 1 for GlobalTheory.PrimeToNormalVanishing.sum_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:27.123547+00:00
-- url     : https://prove2.me/submissions/addaf9e3-950b-4d00-bcd9-cb6b611fa0f3

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_ContinuousConstSMulQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousCohomologyVanishesOfPrimeToLNormalNoIn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.PrimeToNormalVanishing
variable {G Q R M : Type} [Group G] [Group Q] [CommRing R] [AddCommGroup M] [Module R M]
  (ρ : Representation R G M) (π : G →* Q) (J : Subgroup G) (K : Subgroup Q) [Fintype K]
namespace GlobalTheory.PrimeToNormalVanishing
theorem _root_.solution [hK : K.Normal] (φ : Q → M) (a k : Q) (hk : k ∈ K) :
    ∑ i : K, φ (k * (a * i)) = ∑ i : K, φ (a * i) := by
  have h : a⁻¹ * k * a ∈ K := by simpa using hK.conj_mem k hk a⁻¹
  refine Fintype.sum_equiv (Equiv.mulLeft (⟨_, h⟩ : K)) _ _ fun i => ?_
  simp [mul_assoc]
end GlobalTheory.PrimeToNormalVanishing
