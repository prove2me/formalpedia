-- Prove2me | solution 1 for GlobalTheory.RegularNormal.StableDvd.of_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:14:57.911924+00:00
-- url     : https://prove2.me/submissions/7f4a272e-500b-4eab-9f5b-9b21db2f70ce

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSaturated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RegularLocalRingNormalDomain
import Theorems.Thm_GlobalTheory_RegularNormal_dvd_of_not_dvd
import Theorems.Thm_GlobalTheory_RegularNormal_prime_dvd_of_stable

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
open GlobalTheory.RegularNormal
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] {x : A}
namespace GlobalTheory.RegularNormal
namespace StableDvd
theorem _root_.solution (hx : Prime x) (h : StableDvd (A ⧸ Ideal.span {x})) :
    StableDvd A := by
  intro a b I hb hI hst
  obtain ⟨n, c, hc, rfl⟩ := WfDvdMonoid.max_power_factor' hb hx.not_unit
  clear hb
  induction n generalizing a with
  | zero =>
    rw [pow_zero, one_mul] at hst ⊢
    exact dvd_of_not_dvd hx h hc hI hst
  | succ n ih =>
    obtain ⟨a, rfl⟩ := prime_dvd_of_stable hx (a := a) (b := x ^ n * c) hI (fun r hr => by
      obtain ⟨s, hs, e⟩ := hst r hr
      exact ⟨s, hs, by linear_combination e⟩)
    obtain ⟨v, hv⟩ := ih a (fun r hr => by
      obtain ⟨s, hs, e⟩ := hst r hr
      exact ⟨s, hs, mul_left_cancel₀ hx.ne_zero (by linear_combination e)⟩)
    exact ⟨v, by rw [hv]; ring⟩
end StableDvd
end GlobalTheory.RegularNormal
