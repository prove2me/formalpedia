-- Prove2me | solution 1 for GlobalTheory.height_add_ringKrullDim_quotient_of_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:34:55.066021+00:00
-- url     : https://prove2.me/submissions/55666478-400a-4f1b-89e9-3b5edce10525

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRingKrullDimQuotientMvPolynomialEqNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingCoeffNonnegOfEventuallyEvalNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Theorems.Thm_ReciprocityTheory_CA_height_add_ringKrullDim_quotient_mvPolynomial_field
import Theorems.Thm_ReciprocityTheory_CA_ringKrullDim_eq_of_isIntegral_of_injective
import Theorems.Thm_ReciprocityTheory_CA_ringKrullDim_quotient_eq_quotient_comap_of_isIntegral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Module
open GlobalTheory
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory
theorem _root_.solution (k : Type*) {A : Type*} [Field k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (q : Ideal A) [q.IsPrime] :
    (q.height : WithBot ℕ∞) + ringKrullDim (A ⧸ q) = ringKrullDim A := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  let : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨hint⟩
  have hinj' : Function.Injective (algebraMap (MvPolynomial (Fin s) k) A) := hinj
  have : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj'
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  set p := q.comap (algebraMap (MvPolynomial (Fin s) k) A) with hp
  have : q.LiesOver p := ⟨rfl⟩
  have h1 : p.height ≤ q.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q]
    exact le_self_add
  have h2 : q.height ≤ p.height := by
    have e1 := PrimeSpectrum.height_eq_orderHeight (⟨q, inferInstance⟩ : PrimeSpectrum A)
    have e2 := PrimeSpectrum.height_eq_orderHeight (⟨p, inferInstance⟩ : PrimeSpectrum _)
    simp only at e1 e2
    rw [e1, e2]
    exact Order.height_le_height_apply_of_strictMono
      (fun P : PrimeSpectrum A => (⟨P.asIdeal.comap (algebraMap (MvPolynomial (Fin s) k) A),
        inferInstance⟩ : PrimeSpectrum _))
      (fun P Q hPQ => Ideal.IsIntegral.comap_lt_comap (R := MvPolynomial (Fin s) k)
        (show P.asIdeal < Q.asIdeal from hPQ)) _
  rw [le_antisymm h2 h1,
    ReciprocityTheory.CA.ringKrullDim_quotient_eq_quotient_comap_of_isIntegral
      (A := MvPolynomial (Fin s) k) q,
    ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field,
    ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj',
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp
end GlobalTheory
