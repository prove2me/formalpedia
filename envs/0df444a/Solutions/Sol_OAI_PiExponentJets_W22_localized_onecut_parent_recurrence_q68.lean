-- Prove2me | solution 1 for OAI.PiExponentJets.W22.localized_onecut_parent_recurrence_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:01:49.229011+00:00
-- url     : https://prove2.me/submissions/6a98b99d-e70f-4e0f-b3ed-a4c7820eb4d9

import Mathlib
import Definitions.Def_OAIQ068A006
import Definitions.Def_OAIQ068A010
import Theorems.Thm_OAI_PiExponentJets_W28_LocalIntersection_regular_ring_onecut_length_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_QuotientLengthEquivalence
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

theorem length_eq_of_semilinear_bijective
    {R S M N : Type*} [Ring R] [Ring S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N]
    (σ : R →+* S) [RingHomSurjective σ]
    (f : M →ₛₗ[σ] N) (hf : Function.Bijective f) :
    Module.length R M = Module.length S N := by
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

theorem quotient_length_eq_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (J : Ideal S)
    (hIJ : J = I.map e.toRingHom) :
    Module.length R (R ⧸ I) = Module.length S (S ⧸ J) := by
  let eQ : R ⧸ I ≃+* S ⧸ J := Ideal.quotientEquiv I J e hIJ
  let f : (R ⧸ I) →ₛₗ[e.toRingHom] (S ⧸ J) :=
    { toFun := eQ
      map_add' := eQ.map_add
      map_smul' := by
        intro r x
        change eQ ((Ideal.Quotient.mk I r) * x) =
          Ideal.Quotient.mk J (e r) * eQ x
        rw [map_mul]
        change Ideal.quotientEquiv I J e hIJ (Ideal.Quotient.mk I r) * eQ x = _
        rfl }
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  exact length_eq_of_semilinear_bijective e.toRingHom f eQ.bijective

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_QuotientLocalizedLength
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSiegel.W23

theorem intrinsic_length_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : Module.length R R = Module.length S S := by
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  let f : R →ₛₗ[e.toRingHom] S :=
    { toFun := e
      map_add' := e.map_add'
      map_smul' := by
        intro r x
        exact e.map_mul' r x }
  exact PiExponentJets.W22.length_eq_of_semilinear_bijective
    e.toRingHom f e.bijective

theorem quotient_module_length_eq_intrinsic {R : Type*} [CommRing R] (I : Ideal R) :
    Module.length R (R ⧸ I) = Module.length (R ⧸ I) (R ⧸ I) := by
  have hq : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  exact Module.length_eq_of_surjective (M := R ⧸ I) hq

variable {A : Type*} [CommRing A] (I P : Ideal A) [P.IsPrime] (hI : I ≤ P)

theorem quotient_localized_length_eq :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ parameterLocalizedIdeal I P) =
    Module.length (Localization.AtPrime (quotientParameterPrime I P hI))
      (Localization.AtPrime (quotientParameterPrime I P hI)) := by
  calc
    Module.length (Localization.AtPrime P)
        (Localization.AtPrime P ⧸ parameterLocalizedIdeal I P) =
      Module.length (Localization.AtPrime P ⧸ parameterLocalizedIdeal I P)
        (Localization.AtPrime P ⧸ parameterLocalizedIdeal I P) :=
      quotient_module_length_eq_intrinsic (parameterLocalizedIdeal I P)
    _ = Module.length (Localization.AtPrime (quotientParameterPrime I P hI))
        (Localization.AtPrime (quotientParameterPrime I P hI)) :=
      intrinsic_length_eq_of_ringEquiv (localizationQuotientParametersEquiv I P hI)

theorem quotient_localized_length_eq_explicit :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I.map (algebraMap A (Localization.AtPrime P))) =
    Module.length (Localization.AtPrime (quotientParameterPrime I P hI))
      (Localization.AtPrime (quotientParameterPrime I P hI)) :=
  quotient_localized_length_eq I P hI

end PiExponentSiegel.W23

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalIntersectionQuotientTransport
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A : Type*} [CommRing A]

theorem quotient_cut_length (I J : Ideal A) :
    Module.length A (A ⧸ (I ⊔ J)) =
      Module.length (A ⧸ I) ((A ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) := by
  calc
    Module.length A (A ⧸ (I ⊔ J)) =
        Module.length (A ⧸ (I ⊔ J)) (A ⧸ (I ⊔ J)) :=
      PiExponentSiegel.W23.quotient_module_length_eq_intrinsic _
    _ = Module.length ((A ⧸ I) ⧸ J.map (Ideal.Quotient.mk I))
        ((A ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) :=
      (PiExponentSiegel.W23.intrinsic_length_eq_of_ringEquiv
        (DoubleQuot.quotQuotEquivQuotSup I J)).symm
    _ = Module.length (A ⧸ I) ((A ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) :=
      (PiExponentSiegel.W23.quotient_module_length_eq_intrinsic _).symm

theorem quotient_principal_cut_length (I : Ideal A) (x : A) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) =
      Module.length (A ⧸ I) ((A ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I x}) := by
  have hmap : (Ideal.span {x}).map (Ideal.Quotient.mk I) =
      Ideal.span {Ideal.Quotient.mk I x} := by
    simp only [Ideal.map_span, Set.image_singleton]
  exact (quotient_cut_length I (Ideal.span {x})).trans
    (Submodule.quotEquivOfEq _ _ hmap).length_eq

theorem quotient_prime_cut_length (I P : Ideal A) (hIP : I ≤ P) (x : A) :
    Module.length A (A ⧸ (P ⊔ Ideal.span {x})) =
      Module.length (A ⧸ I) ((A ⧸ I) ⧸
        (P.map (Ideal.Quotient.mk I) ⊔ Ideal.span {Ideal.Quotient.mk I x})) := by
  have hleft : I ⊔ (P ⊔ Ideal.span {x}) = P ⊔ Ideal.span {x} :=
    sup_eq_right.mpr (hIP.trans le_sup_left)
  have hright : (P ⊔ Ideal.span {x}).map (Ideal.Quotient.mk I) =
      P.map (Ideal.Quotient.mk I) ⊔ Ideal.span {Ideal.Quotient.mk I x} := by
    simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  calc
    Module.length A (A ⧸ (P ⊔ Ideal.span {x})) =
        Module.length A (A ⧸ (I ⊔ (P ⊔ Ideal.span {x}))) :=
      (Submodule.quotEquivOfEq _ _ hleft).length_eq.symm
    _ = Module.length (A ⧸ I) ((A ⧸ I) ⧸
        (P ⊔ Ideal.span {x}).map (Ideal.Quotient.mk I)) :=
      quotient_cut_length I (P ⊔ Ideal.span {x})
    _ = Module.length (A ⧸ I) ((A ⧸ I) ⧸
        (P.map (Ideal.Quotient.mk I) ⊔ Ideal.span {Ideal.Quotient.mk I x})) :=
      (Submodule.quotEquivOfEq _ _ hright).length_eq

theorem quotient_minimal_local_length (I : Ideal A)
    (Q : minimalPrimes (A ⧸ I)) :
    (letI : (quotientMinimalPrimesEquiv I Q).val.IsPrime :=
       (quotientMinimalPrimesEquiv I Q).property.1.1
     Module.length (Localization.AtPrime (quotientMinimalPrimesEquiv I Q).val)
       (Localization.AtPrime (quotientMinimalPrimesEquiv I Q).val ⧸
        I.map (algebraMap A (Localization.AtPrime (quotientMinimalPrimesEquiv I Q).val)))) =
    (letI : Q.val.IsPrime := Q.property.1.1
     Module.length (Localization.AtPrime Q.val)
       (Localization.AtPrime Q.val ⧸ (⊥ : Ideal (A ⧸ I)).map
        (algebraMap (A ⧸ I) (Localization.AtPrime Q.val)))) := by
  let P := (quotientMinimalPrimesEquiv I Q).val
  let : P.IsPrime := (quotientMinimalPrimesEquiv I Q).property.1.1
  let : Q.val.IsPrime := Q.property.1.1
  have hIP : I ≤ P := (quotientMinimalPrimesEquiv I Q).property.1.2
  have hmap : PiExponentSiegel.W23.quotientParameterPrime I P hIP = Q.val := by
    exact Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective Q.val
  have hlocal := PiExponentSiegel.W23.quotient_localized_length_eq_explicit I P hIP
  have hprime :
      (⟨PiExponentSiegel.W23.quotientParameterPrime I P hIP,
        PiExponentSiegel.W23.quotientParameterPrime_isPrime I P hIP⟩ : PrimeSpectrum (A ⧸ I)) =
      ⟨Q.val, Q.property.1.1⟩ := PrimeSpectrum.ext hmap
  have hlength := congrArg (fun p : PrimeSpectrum (A ⧸ I) =>
    Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) hprime
  refine (hlocal.trans hlength).trans ?_
  rw [Ideal.map_bot]
  exact ((⊥ : Submodule (Localization.AtPrime Q.val) (Localization.AtPrime Q.val)).quotEquivOfEqBot
    rfl).length_eq.symm

end PiExponentJets.W28.LocalIntersection

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalIntersectionFormula
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

open scoped BigOperators

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

theorem minimalPrimeCutSum_quotient (I : Ideal A) (x : A) :
    minimalPrimeCutSum I x =
      minimalPrimeCutSum (⊥ : Ideal (A ⧸ I)) (Ideal.Quotient.mk I x) := by
  classical
  let : Fintype I.minimalPrimes :=
    (I.finite_minimalPrimes_of_isNoetherianRing A).fintype
  let : Fintype (minimalPrimes (A ⧸ I)) :=
    ((⊥ : Ideal (A ⧸ I)).finite_minimalPrimes_of_isNoetherianRing (A ⧸ I)).fintype
  symm
  unfold minimalPrimeCutSum
  apply Fintype.sum_equiv (quotientMinimalPrimesEquiv I)
  intro Q
  let P := (quotientMinimalPrimesEquiv I Q).val
  let : P.IsPrime := (quotientMinimalPrimesEquiv I Q).property.1.1
  let : Q.val.IsPrime := Q.property.1.1
  have hIP : I ≤ P := (quotientMinimalPrimesEquiv I Q).property.1.2
  have hmap : P.map (Ideal.Quotient.mk I) = Q.val :=
    Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective Q.val
  have hc := quotient_prime_cut_length I P hIP x
  rw [hmap] at hc
  exact congrArg₂ HMul.hMul (quotient_minimal_local_length I Q).symm hc.symm

omit [IsNoetherianRing A] in
theorem quotient_parameter_mem_nonZeroDivisors (I : Ideal A) (x : A)
    (hregular : Function.Injective (quotientMul I x)) :
    Ideal.Quotient.mk I x ∈ nonZeroDivisors (A ⧸ I) := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro y hy
  apply hregular
  change x • y = x • (0 : A ⧸ I)
  rw [smul_zero, Algebra.smul_def]
  exact hy

theorem local_onecut_length [IsLocalRing A]
    (I : Ideal A) (x : A) (hdim : ringKrullDim (A ⧸ I) = 1)
    (hregular : Function.Injective (quotientMul I x)) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) = minimalPrimeCutSum I x := by
  have hnot : ¬ Subsingleton (A ⧸ I) := by
    intro hsub
    let := hsub
    have hbot : ringKrullDim (A ⧸ I) = ⊥ := ringKrullDim_eq_bot_of_subsingleton
    rw [hdim] at hbot
    exact WithBot.one_ne_bot hbot
  let : Nontrivial (A ⧸ I) := not_subsingleton_iff_nontrivial.mp hnot
  let : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : Ring.KrullDimLE 1 (A ⧸ I) := Ring.krullDimLE_iff.mpr hdim.le
  calc
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) =
        Module.length (A ⧸ I) ((A ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I x}) :=
      quotient_principal_cut_length I x
    _ = minimalPrimeCutSum (⊥ : Ideal (A ⧸ I)) (Ideal.Quotient.mk I x) :=
      regular_ring_onecut_length_q68 _ (quotient_parameter_mem_nonZeroDivisors I x hregular)
    _ = minimalPrimeCutSum I x := (minimalPrimeCutSum_quotient I x).symm

end PiExponentJets.W28.LocalIntersection

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalPrimeTower
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

variable {A : Type*} [CommRing A]

theorem localPrimeTower_map_ideal
    (Q : Ideal A) [Q.IsPrime] (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] (I : Ideal A) :
    (I.map (algebraMap A (Localization.AtPrime Q))).map
      (algebraMap (Localization.AtPrime Q) (Localization.AtPrime p)) =
    (I.map (algebraMap A
      (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q)))))).map
        (localPrimeTowerEquiv Q p).toRingEquiv.toRingHom := by
  have he : (localPrimeTowerEquiv Q p).toRingEquiv.toRingHom.comp
      (algebraMap A (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q))))) =
      algebraMap A (Localization.AtPrime p) := by
    ext a
    exact localPrimeTowerEquiv_algebraMap Q p a
  rw [Ideal.map_map, Ideal.map_map, he,
    ← IsScalarTower.algebraMap_eq A (Localization.AtPrime Q) (Localization.AtPrime p)]

theorem localPrimeTower_quotient_length
    (Q : Ideal A) [Q.IsPrime] (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] (I : Ideal A) :
    Module.length (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q))))
      (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q))) ⧸
        I.map (algebraMap A
          (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q)))))) =
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ (I.map (algebraMap A (Localization.AtPrime Q))).map
        (algebraMap (Localization.AtPrime Q) (Localization.AtPrime p))) :=
  quotient_length_eq_of_ringEquiv (localPrimeTowerEquiv Q p).toRingEquiv _ _
    (localPrimeTower_map_ideal Q p I)

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalizedOneCutPropagation
attribute [-instance] _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W28.LocalIntersection
open scoped BigOperators Classical

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

omit [IsNoetherianRing A] in
theorem localization_map_cut (I Q : Ideal A) [Q.IsPrime] (x : A) :
    (I ⊔ Ideal.span {x}).map (algebraMap A (Localization.AtPrime Q)) =
      I.map (algebraMap A (Localization.AtPrime Q)) ⊔
        Ideal.span {algebraMap A (Localization.AtPrime Q) x} := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]

theorem minimalPrimeCutSum_localization (I Q : Ideal A) [Q.IsPrime] (x : A) :
    minimalPrimeCutSum (I.map (algebraMap A (Localization.AtPrime Q)))
      (algebraMap A (Localization.AtPrime Q) x) = globalParentCutSum I Q x := by
  classical
  let : Fintype (I.map (algebraMap A (Localization.AtPrime Q))).minimalPrimes :=
    ((I.map (algebraMap A (Localization.AtPrime Q))).finite_minimalPrimes_of_isNoetherianRing
      (Localization.AtPrime Q)).fintype
  unfold minimalPrimeCutSum globalParentCutSum
  apply Fintype.sum_equiv (localizedMinimalPrimesEquiv I Q)
  intro p
  let : p.val.IsPrime := p.property.1.1
  have htower := localPrimeTower_quotient_length Q p.val I
  have hcut :
      ((p.val.comap (algebraMap A (Localization.AtPrime Q))) ⊔ Ideal.span {x}).map
        (algebraMap A (Localization.AtPrime Q)) =
      p.val ⊔ Ideal.span {algebraMap A (Localization.AtPrime Q) x} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton,
      IsLocalization.map_under Q.primeCompl (Localization.AtPrime Q) p.val]
  have hcutlen := congrArg
    (fun K : Ideal (Localization.AtPrime Q) =>
      Module.length (Localization.AtPrime Q) (Localization.AtPrime Q ⧸ K)) hcut
  exact congrArg₂ HMul.hMul htower.symm hcutlen.symm

theorem localized_onecut_parent_recurrence_q68_oai
    (I Q : Ideal A) [Q.IsPrime] (x : A)
    (hdim : ringKrullDim (Localization.AtPrime Q ⧸
      I.map (algebraMap A (Localization.AtPrime Q))) = 1)
    (hregular : Function.Injective
      (quotientMul (I.map (algebraMap A (Localization.AtPrime Q)))
        (algebraMap A (Localization.AtPrime Q) x))) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ (I ⊔ Ideal.span {x}).map
        (algebraMap A (Localization.AtPrime Q))) = globalParentCutSum I Q x := by
  rw [localization_map_cut]
  exact (local_onecut_length _ _ hdim hregular).trans
    (minimalPrimeCutSum_localization I Q x)

end PiExponentJets.W22

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PiExponentJets.W22.localized_onecut_parent_recurrence_q68_oai.{u_1} := @OAI.PiExponentJets.W22.localized_onecut_parent_recurrence_q68_oai.{u_1}
