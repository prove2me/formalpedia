-- Prove2me | solution 1 for GlobalTheory.injective_of_finite_of_ringKrullDim_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:29:27.049479+00:00
-- url     : https://prove2.me/submissions/f15a22ed-5d5b-4d18-9516-19b8a484ec8f

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Theorems.Thm_ReciprocityTheory_CA_ringKrullDim_quotient_eq_quotient_comap_of_isIntegral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory
theorem _root_.solution {k S : Type*} [Field k] [CommRing S] {δ : ℕ}
    (φ : MvPolynomial (Fin δ) k →+* S) (hφ : φ.Finite) (hdim : ringKrullDim S = δ) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hne
  letI := φ.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin δ) k) S := hφ
  have h1 := ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral
    (A := MvPolynomial (Fin δ) k) (⊥ : Ideal S)
  rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot S), hdim] at h1
  have h2 := ringKrullDim_succ_le_of_surjective
    (Ideal.Quotient.mk ((⊥ : Ideal S).comap (algebraMap (MvPolynomial (Fin δ) k) S)))
    Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_of_ne_zero hne)
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_comap.mpr (Ideal.mem_bot.mpr hr)))
  rw [← h1, MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    zero_add, Nat.card_eq_fintype_card, Fintype.card_fin] at h2
  have h3 : δ + 1 ≤ δ := by exact_mod_cast h2
  omega
end GlobalTheory
