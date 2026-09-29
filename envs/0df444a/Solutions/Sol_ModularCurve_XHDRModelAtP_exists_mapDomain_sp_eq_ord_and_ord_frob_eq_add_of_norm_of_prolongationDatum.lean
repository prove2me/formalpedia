-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/73fee5de-e2f2-536a-ae0d-e9b0118a8b4a

import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_Correspondence
import Theorems.Thm_Subalgebra_algebraMap_norm_eq_and_residue_norm_eq_mul
import Theorems.Thm_ModularCurve_qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finrankAlong_eq_add_one_of_coe_eq_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_residue_alpha_eq
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mapDomain_sp_eq_ord_residue_alpha_full
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_finset_isIntegral_span_residue_surjective
import Theorems.Thm_ModularCurve_ord_qExpFrobeniusPlaceModL_eq_ord_of_qExpFrobeniusModL_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open scoped MatrixGroups

noncomputable section

namespace Ws49
namespace NormRed

section Engine

variable {K F Fb k : Type*} [Field K] [Field F] [Field Fb] [Field k] [Algebra K F] [Algebra k Fb]
  (V : ValuationSubring K) [Algebra ↥V F] [IsScalarTower ↥V K F]
  (resV : ↥V →+* Fb) (hker : ∀ v : ↥V, v ∈ maximalIdeal ↥V → resV v = 0) (φ : Fb →ₐ[k] Fb)

abbrev B := ResidueField ↥V

def Lmap : B V →+* Fb := Ideal.Quotient.lift (maximalIdeal ↥V) resV hker

theorem Lmap_residue (v : ↥V) : Lmap V resV hker (residue _ v) = resV v := Ideal.Quotient.lift_mk _ _ _

theorem Lmap_surjective (hsurjN : Function.Surjective resV) : Function.Surjective (Lmap V resV hker) := fun a => by
  obtain ⟨v, hv⟩ := hsurjN a
  exact ⟨residue _ v, by rw [Lmap_residue, hv]⟩

def Emap (hsurjN : Function.Surjective resV) : B V ≃+* Fb :=
  RingEquiv.ofBijective (Lmap V resV hker) ⟨(Lmap V resV hker).injective, Lmap_surjective V resV hker hsurjN⟩

set_option linter.unusedVariables false in

def KOne {K : Type*} [Field K] (V : ValuationSubring K) (Fb : Type*) [Field Fb] {k : Type*} [Field k] [Algebra k Fb]
    (resV : ↥V →+* Fb) (hker : ∀ v : ↥V, v ∈ maximalIdeal ↥V → resV v = 0) (φ : Fb →ₐ[k] Fb) : Type _ := Fb

set_option linter.unusedVariables false in

def KTwo {K : Type*} [Field K] (V : ValuationSubring K) (Fb : Type*) [Field Fb] {k : Type*} [Field k] [Algebra k Fb]
    (resV : ↥V →+* Fb) (hker : ∀ v : ↥V, v ∈ maximalIdeal ↥V → resV v = 0) (φ : Fb →ₐ[k] Fb) : Type _ := Fb

scoped instance instFieldKOne : Field (KOne V Fb resV hker φ) := inferInstanceAs (Field Fb)
scoped instance instFieldKTwo : Field (KTwo V Fb resV hker φ) := inferInstanceAs (Field Fb)

scoped instance algebraFbKOne : Algebra Fb (KOne V Fb resV hker φ) := show Algebra Fb Fb from Algebra.id _

scoped instance algebraFbKTwo : Algebra Fb (KTwo V Fb resV hker φ) := show Algebra Fb Fb from algebraAlong φ

theorem finrank_KTwo_eq : Module.finrank Fb (KTwo V Fb resV hker φ) = finrankAlong k φ := rfl

scoped instance algebraBKOne : Algebra (B V) (KOne V Fb resV hker φ) := (show B V →+* KOne V Fb resV hker φ from Lmap V resV hker).toAlgebra

theorem algebraMap_BKOne (b : B V) : algebraMap (B V) (KOne V Fb resV hker φ) b = (Lmap V resV hker b : Fb) := rfl

scoped instance algebraBKTwo : Algebra (B V) (KTwo V Fb resV hker φ) := ((algebraMap Fb (KTwo V Fb resV hker φ)).comp (Lmap V resV hker)).toAlgebra

theorem algebraMap_BKTwo (b : B V) : algebraMap (B V) (KTwo V Fb resV hker φ) b = φ (Lmap V resV hker b) := rfl

scoped instance algebraVKOne : Algebra ↥V (KOne V Fb resV hker φ) := ((algebraMap (B V) (KOne V Fb resV hker φ)).comp (residue ↥V)).toAlgebra
scoped instance algebraVKTwo : Algebra ↥V (KTwo V Fb resV hker φ) := ((algebraMap (B V) (KTwo V Fb resV hker φ)).comp (residue ↥V)).toAlgebra

scoped instance towerVBKOne : IsScalarTower ↥V (B V) (KOne V Fb resV hker φ) := IsScalarTower.of_algebraMap_eq fun _ => rfl
scoped instance towerVBKTwo : IsScalarTower ↥V (B V) (KTwo V Fb resV hker φ) := IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem algebraMap_VKOne_apply (v : ↥V) : algebraMap ↥V (KOne V Fb resV hker φ) v = (Lmap V resV hker (residue _ v) : Fb) := rfl
theorem algebraMap_VKTwo_apply (v : ↥V) : algebraMap ↥V (KTwo V Fb resV hker φ) v = φ (Lmap V resV hker (residue _ v)) := rfl

theorem finrank_BKOne (hsurjN : Function.Surjective resV) : Module.finrank (B V) (KOne V Fb resV hker φ) = 1 :=
  (Algebra.finrank_eq_of_equiv_equiv (Emap V resV hker hsurjN) (RingEquiv.refl (KOne V Fb resV hker φ)) (RingHom.ext fun _ => rfl)).trans
    (Module.finrank_self Fb)

theorem finrank_BKTwo (hsurjN : Function.Surjective resV) {p : ℕ}
    (hφdeg : finrankAlong k φ = p) : Module.finrank (B V) (KTwo V Fb resV hker φ) = p :=
  (Algebra.finrank_eq_of_equiv_equiv (Emap V resV hker hsurjN) (RingEquiv.refl (KTwo V Fb resV hker φ)) (RingHom.ext fun _ => rfl)).trans
    ((finrank_KTwo_eq V resV hker φ).trans hφdeg)

theorem finite_BKOne (hsurjN : Function.Surjective resV) : FiniteDimensional (B V) (KOne V Fb resV hker φ) :=
  Module.finite_of_finrank_pos (by rw [finrank_BKOne V resV hker φ hsurjN]; exact Nat.one_pos)

theorem finite_BKTwo (hsurjN : Function.Surjective resV) {p : ℕ} [Fact p.Prime]
    (hφdeg : finrankAlong k φ = p) : FiniteDimensional (B V) (KTwo V Fb resV hker φ) :=
  Module.finite_of_finrank_pos (by rw [finrank_BKTwo V resV hker φ hsurjN hφdeg]; exact (Fact.out : p.Prime).pos)

theorem exists_algebraMap_BKTwo_eq_pow (hsurjN : Function.Surjective resV) {p : ℕ}
    (hφpow : ∀ y : Fb, ∃ c : Fb, φ c = y ^ p) (y : KTwo V Fb resV hker φ) :
    ∃ c : B V, algebraMap (B V) (KTwo V Fb resV hker φ) c = y ^ p := by
  obtain ⟨c', hc'⟩ := hφpow (show Fb from y)
  obtain ⟨c, hc⟩ := Lmap_surjective V resV hker hsurjN c'
  exact ⟨c, by rw [algebraMap_BKTwo, hc, hc']; rfl⟩

open Polynomial IntermediateField in
theorem algebraMap_norm_eq_pow_of_finrank_eq_prime {κ κ₂ : Type*} [Field κ] [Field κ₂] [Algebra κ κ₂]
    (p : ℕ) [Fact p.Prime] [CharP κ p] (hfin : Module.finrank κ κ₂ = p)
    (hpow : ∀ y : κ₂, ∃ c : κ, algebraMap κ κ₂ c = y ^ p) (x : κ₂) :
    algebraMap κ κ₂ (Algebra.norm κ x) = x ^ p := by
  have hp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hp.ne_zero
  obtain ⟨c, hc⟩ := hpow x
  by_cases hx : ∃ b : κ, algebraMap κ κ₂ b = x
  · obtain ⟨b, rfl⟩ := hx
    rw [Algebra.norm_algebraMap, hfin, map_pow]
  haveI : FiniteDimensional κ κ₂ := Module.finite_of_finrank_pos (by rw [hfin]; exact hp.pos)
  have hint : IsIntegral κ x := IsIntegral.of_finite κ x
  have hdvd : minpoly κ x ∣ X ^ p - C c := minpoly.dvd κ x (by simp [hc])
  have hdeg : (minpoly κ x).natDegree = p := by
    have h1 : Module.finrank κ κ⟮x⟯ ∣ p := by
      rw [← hfin]
      exact Dvd.intro _ (Module.finrank_mul_finrank κ κ⟮x⟯ κ₂)
    rcases (Nat.dvd_prime hp).mp h1 with h1 | h1
    · exfalso
      apply hx
      have hmem : x ∈ κ⟮x⟯ := mem_adjoin_simple_self κ x
      rw [finrank_eq_one_iff.mp h1, mem_bot] at hmem
      obtain ⟨b, hb⟩ := hmem
      exact ⟨b, hb⟩
    · rw [← adjoin.finrank hint]
      exact h1
  have hmin : X ^ p - C c = minpoly κ x :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (monic_X_pow_sub_C c hp0) hdvd
      (by rw [natDegree_X_pow_sub_C, hdeg])
  have htop : κ⟮x⟯ = ⊤ := by
    refine eq_of_le_of_finrank_eq le_top ?_
    rw [finrank_top', hfin, adjoin.finrank hint, hdeg]
  let pb : PowerBasis κ κ₂ := (adjoin.powerBasis hint).map ((equivOfEq htop).trans topEquiv)
  have hgen : pb.gen = x := rfl
  have hdim : pb.dim = p := hdeg
  have hcoeff : (X ^ p - C c).coeff 0 = -c := by simp [Ne.symm hp0]
  have hnorm : Algebra.norm κ x = c := by
    have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
    rw [hgen, hdim, ← hmin, hcoeff] at h
    rw [h]
    rcases hp.eq_two_or_odd' with h2 | hodd
    · subst h2
      rw [neg_one_sq, one_mul, CharTwo.neg_eq]
    · rw [hodd.neg_one_pow, neg_one_mul, neg_neg]
  rw [hnorm, hc]

scoped instance algebraOrder (S : Subalgebra ↥V F) : Algebra ↥V ↥S := Subalgebra.algebra S

variable {L : Type*} [Field L] [Algebra L F] {A : ValuationSubring L} [Algebra (ResidueField ↥A) Fb]
  (R₁ R₂ : RegularProlongation A F Fb)
  (S : Subalgebra ↥V F) (hS₁ : ∀ s ∈ S, s ∈ R₁.integers) (hS₂ : ∀ s ∈ S, s ∈ R₂.integers)
  (hV₁ : ∀ v : ↥V, algebraMap ↥V F v ∈ R₁.integers)
  (hρ₁ : ∀ v : ↥V, R₁.residue ⟨algebraMap ↥V F v, hV₁ v⟩ = resV v)
  (hV₂ : ∀ v : ↥V, algebraMap ↥V F v ∈ R₂.integers)
  (hρ₂ : ∀ v : ↥V, R₂.residue ⟨algebraMap ↥V F v, hV₂ v⟩ = φ (resV v))

include hV₁ hρ₁ in

def rho₁ : ↥S →ₐ[↥V] KOne V Fb resV hker φ where
  toFun s := (R₁.residue ⟨(s : F), hS₁ _ s.2⟩ : Fb)
  map_one' := by
    have : (⟨((1 : ↥S) : F), hS₁ _ (1 : ↥S).2⟩ : ↥R₁.integers) = 1 := Subtype.ext rfl
    simp only [this, map_one]; rfl
  map_mul' s t := by
    have : (⟨((s * t : ↥S) : F), hS₁ _ (s * t).2⟩ : ↥R₁.integers) = ⟨(s : F), hS₁ _ s.2⟩ * ⟨(t : F), hS₁ _ t.2⟩ := Subtype.ext rfl
    simp only [this, map_mul]; rfl
  map_zero' := by
    have : (⟨((0 : ↥S) : F), hS₁ _ (0 : ↥S).2⟩ : ↥R₁.integers) = 0 := Subtype.ext rfl
    simp only [this, map_zero]; rfl
  map_add' s t := by
    have : (⟨((s + t : ↥S) : F), hS₁ _ (s + t).2⟩ : ↥R₁.integers) = ⟨(s : F), hS₁ _ s.2⟩ + ⟨(t : F), hS₁ _ t.2⟩ := Subtype.ext rfl
    simp only [this, map_add]; rfl
  commutes' v := by
    show (R₁.residue ⟨((algebraMap ↥V ↥S v : ↥S) : F), _⟩ : Fb) = algebraMap ↥V (KOne V Fb resV hker φ) v
    rw [algebraMap_VKOne_apply, Lmap_residue, ← hρ₁ v]
    congr 1

theorem rho₁_apply (s : ↥S) : (rho₁ V resV hker φ R₁ S hS₁ hV₁ hρ₁ s : Fb) = R₁.residue ⟨(s : F), hS₁ _ s.2⟩ := rfl

include hV₂ hρ₂ in

def rho₂ : ↥S →ₐ[↥V] KTwo V Fb resV hker φ where
  toFun s := (R₂.residue ⟨(s : F), hS₂ _ s.2⟩ : Fb)
  map_one' := by
    have : (⟨((1 : ↥S) : F), hS₂ _ (1 : ↥S).2⟩ : ↥R₂.integers) = 1 := Subtype.ext rfl
    simp only [this, map_one]; rfl
  map_mul' s t := by
    have : (⟨((s * t : ↥S) : F), hS₂ _ (s * t).2⟩ : ↥R₂.integers) = ⟨(s : F), hS₂ _ s.2⟩ * ⟨(t : F), hS₂ _ t.2⟩ := Subtype.ext rfl
    simp only [this, map_mul]; rfl
  map_zero' := by
    have : (⟨((0 : ↥S) : F), hS₂ _ (0 : ↥S).2⟩ : ↥R₂.integers) = 0 := Subtype.ext rfl
    simp only [this, map_zero]; rfl
  map_add' s t := by
    have : (⟨((s + t : ↥S) : F), hS₂ _ (s + t).2⟩ : ↥R₂.integers) = ⟨(s : F), hS₂ _ s.2⟩ + ⟨(t : F), hS₂ _ t.2⟩ := Subtype.ext rfl
    simp only [this, map_add]; rfl
  commutes' v := by
    show (R₂.residue ⟨((algebraMap ↥V ↥S v : ↥S) : F), _⟩ : Fb) = algebraMap ↥V (KTwo V Fb resV hker φ) v
    rw [algebraMap_VKTwo_apply, Lmap_residue, ← hρ₂ v]
    congr 1

theorem rho₂_apply (s : ↥S) : (rho₂ V resV hker φ R₂ S hS₂ hV₂ hρ₂ s : Fb) = R₂.residue ⟨(s : F), hS₂ _ s.2⟩ := rfl

include hker hV₁ hρ₁ hV₂ hρ₂ in

theorem residue_norm_factorization {p : ℕ} [Fact p.Prime] [CharP Fb p] [Module.Finite ↥V ↥S]
    (hsurjN : Function.Surjective resV)
    (hφdeg : finrankAlong k φ = p)
    (hφpow : ∀ y : Fb, ∃ c : Fb, φ c = y ^ p)
    (hdeg : Module.finrank K F = p + 1)
    (hspan : Submodule.span K (S : Set F) = ⊤)
    (hsurjS : ∀ a b : Fb, ∃ (s : F) (hs : s ∈ S), R₁.residue ⟨s, hS₁ s hs⟩ = a ∧ R₂.residue ⟨s, hS₂ s hs⟩ = b)
    (f : F) (hfS : f ∈ S) :
    ∃ (hn : algebraMap K F (Algebra.norm K f) ∈ R₁.integers) (g₂ : Fb), φ g₂ = (R₂.residue ⟨f, hS₂ f hfS⟩) ^ p ∧
      R₁.residue ⟨algebraMap K F (Algebra.norm K f), hn⟩ = R₁.residue ⟨f, hS₁ f hfS⟩ * g₂ := by
  haveI := finite_BKOne V resV hker φ hsurjN
  haveI := finite_BKTwo V resV hker φ hsurjN hφdeg
  haveI : CharP (B V) p := by
    haveI : Algebra (B V) Fb := (Lmap V resV hker).toAlgebra
    exact (Algebra.charP_iff (B V) Fb p).mpr inferInstance
  have hsurj : Function.Surjective fun s : ↥S => (rho₁ V resV hker φ R₁ S hS₁ hV₁ hρ₁ s, rho₂ V resV hker φ R₂ S hS₂ hV₂ hρ₂ s) := by
    intro q
    obtain ⟨s, hs, ha, hb⟩ := hsurjS q.1 q.2
    exact ⟨⟨s, hs⟩, Prod.ext ha hb⟩
  have hdim : Module.finrank (B V) (KOne V Fb resV hker φ) + Module.finrank (B V) (KTwo V Fb resV hker φ) = Module.finrank K F := by
    rw [finrank_BKOne V resV hker φ hsurjN, finrank_BKTwo V resV hker φ hsurjN hφdeg, hdeg, add_comm]
  obtain ⟨hint, hfac⟩ := @Subalgebra.algebraMap_norm_eq_and_residue_norm_eq_mul ↥V K F
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance S inferInstance hspan (KOne V Fb resV hker φ) (KTwo V Fb resV hker φ) inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (rho₁ V resV hker φ R₁ S hS₁ hV₁ hρ₁) (rho₂ V resV hker φ R₂ S hS₂ hV₂ hρ₂) hsurj hdim ⟨f, hfS⟩

  have hint' : algebraMap K F (Algebra.norm K f) = algebraMap ↥V F (Algebra.norm ↥V (⟨f, hfS⟩ : ↥S)) := by
    rw [← hint, ← IsScalarTower.algebraMap_apply]
  have hn : algebraMap K F (Algebra.norm K f) ∈ R₁.integers := by rw [hint']; exact hV₁ _

  obtain ⟨b, hb⟩ := Lmap_surjective V resV hker hsurjN (R₁.residue ⟨f, hS₁ f hfS⟩)
  have hn₁ : Algebra.norm (B V) (rho₁ V resV hker φ R₁ S hS₁ hV₁ hρ₁ ⟨f, hfS⟩) = b := by
    rw [show rho₁ V resV hker φ R₁ S hS₁ hV₁ hρ₁ ⟨f, hfS⟩ = algebraMap (B V) (KOne V Fb resV hker φ) b by rw [algebraMap_BKOne, hb]; rfl,
      Algebra.norm_algebraMap, finrank_BKOne V resV hker φ hsurjN, pow_one]

  have hn₂ : φ (Lmap V resV hker (Algebra.norm (B V) (rho₂ V resV hker φ R₂ S hS₂ hV₂ hρ₂ ⟨f, hfS⟩))) = (R₂.residue ⟨f, hS₂ f hfS⟩) ^ p := by
    have h := algebraMap_norm_eq_pow_of_finrank_eq_prime (κ := B V) (κ₂ := KTwo V Fb resV hker φ) p
      (finrank_BKTwo V resV hker φ hsurjN hφdeg) (exists_algebraMap_BKTwo_eq_pow V resV hker φ hsurjN hφpow) (rho₂ V resV hker φ R₂ S hS₂ hV₂ hρ₂ ⟨f, hfS⟩)
    rw [algebraMap_BKTwo] at h
    exact h
  refine ⟨hn, Lmap V resV hker (Algebra.norm (B V) (rho₂ V resV hker φ R₂ S hS₂ hV₂ hρ₂ ⟨f, hfS⟩)), hn₂, ?_⟩
  have hres' := congrArg (Lmap V resV hker) hfac
  rw [map_mul, Lmap_residue, hn₁, hb, ← hρ₁] at hres'
  rw [← hres']
  congr 1
  exact Subtype.ext hint'

end Engine

end Ws49.NormRed
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum.Ws49 P2MW.S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum.Ws49.NormRed"
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum.Ws49"

namespace Ws49
namespace NormRed

section Common

variable {L K F Fb : Type*} [Field L] [Field K] [Field F] [Field Fb] [Algebra L K] [Algebra L F]
  {A : ValuationSubring L} [Algebra (ResidueField ↥A) Fb]

theorem mem₂_of_unit (R₁ R₂ : RegularProlongation A F Fb) (α : K →ₐ[L] F) (φ : Fb → Fb) (hφ0 : ∀ y, φ y = 0 → y = 0)
    (hres : ∀ (v : K) (h₁ : α v ∈ R₁.integers) (h₂ : α v ∈ R₂.integers), R₂.residue ⟨α v, h₂⟩ = φ (R₁.residue ⟨α v, h₁⟩))
    (v : K) (h₁ : α v ∈ R₁.integers) (hr₁ : R₁.residue ⟨α v, h₁⟩ ≠ 0) : ∃ h₂ : α v ∈ R₂.integers, R₂.residue ⟨α v, h₂⟩ ≠ 0 := by
  by_cases h₂ : α v ∈ R₂.integers
  · exact ⟨h₂, by rw [hres v h₁ h₂]; exact fun h => hr₁ (hφ0 _ h)⟩
  · exfalso
    have hv0 : α v ≠ 0 := by
      intro h
      apply hr₁
      have : (⟨α v, h₁⟩ : ↥R₁.integers) = 0 := Subtype.ext h
      rw [this, map_zero]
    have hinv₂ : (α v)⁻¹ ∈ R₂.integers := (R₂.integers.mem_or_inv_mem (α v)).resolve_left h₂
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp (R₁.isUnit_of_residue_ne_zero hr₁)
    have hb' : (b : F) = (α v)⁻¹ := eq_inv_of_mul_eq_one_right (by simpa using congrArg Subtype.val hb)
    have hinv₁ : (α v)⁻¹ ∈ R₁.integers := hb' ▸ b.2
    have k₁ : α v⁻¹ ∈ R₁.integers := by rw [map_inv₀]; exact hinv₁
    have k₂ : α v⁻¹ ∈ R₂.integers := by rw [map_inv₀]; exact hinv₂
    have hr₁' : R₁.residue ⟨α v⁻¹, k₁⟩ ≠ 0 := by
      apply R₁.residue_ne_zero_of_isUnit
      refine IsUnit.of_mul_eq_one ⟨α v, h₁⟩ (Subtype.ext ?_)
      simp [map_inv₀, inv_mul_cancel₀ hv0]
    have hr₂' : R₂.residue ⟨α v⁻¹, k₂⟩ ≠ 0 := by rw [hres v⁻¹ k₁ k₂]; exact fun h => hr₁' (hφ0 _ h)
    obtain ⟨b₂, hb₂⟩ := isUnit_iff_exists_inv.mp (R₂.isUnit_of_residue_ne_zero hr₂')
    have hb₂' : (b₂ : F) = (α v⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right (by simpa using congrArg Subtype.val hb₂)
    apply h₂
    have : (α v⁻¹)⁻¹ = α v := by rw [map_inv₀, inv_inv]
    rw [← this, ← hb₂']
    exact b₂.2

theorem mem₂_of_mem₁ (R₁ R₂ : RegularProlongation A F Fb) (α : K →ₐ[L] F) (φ : Fb → Fb) (hφ0 : ∀ y, φ y = 0 → y = 0)
    (hres : ∀ (v : K) (h₁ : α v ∈ R₁.integers) (h₂ : α v ∈ R₂.integers), R₂.residue ⟨α v, h₂⟩ = φ (R₁.residue ⟨α v, h₁⟩))
    (v : K) (h₁ : α v ∈ R₁.integers) : α v ∈ R₂.integers := by
  by_cases hr₁ : R₁.residue ⟨α v, h₁⟩ ≠ 0
  · exact (mem₂_of_unit R₁ R₂ α φ hφ0 hres v h₁ hr₁).1
  · push Not at hr₁
    have h₁' : α (1 + v) ∈ R₁.integers := by rw [map_add, map_one]; exact add_mem (one_mem _) h₁
    have hr : R₁.residue ⟨α (1 + v), h₁'⟩ ≠ 0 := by
      have : (⟨α (1 + v), h₁'⟩ : ↥R₁.integers) = 1 + ⟨α v, h₁⟩ := Subtype.ext (by simp)
      rw [this, map_add, map_one, hr₁, add_zero]
      exact one_ne_zero
    obtain ⟨h₂', -⟩ := mem₂_of_unit R₁ R₂ α φ hφ0 hres (1 + v) h₁' hr
    have : α v = α (1 + v) - 1 := by rw [map_add, map_one]; ring
    rw [this]
    exact sub_mem h₂' (one_mem _)

omit [Algebra L K] [Algebra L F] [Algebra (ResidueField ↥A) Fb] in

theorem mem_of_isIntegral_tower (O : ValuationSubring F) {V₀ : Type*} [CommRing V₀] [Algebra V₀ F]
    (toO : V₀ →+* ↥O) (htoO : ∀ v, ((toO v : ↥O) : F) = algebraMap V₀ F v) {x : F} (hx : IsIntegral V₀ x) : x ∈ O := by
  letI : Algebra V₀ ↥O := toO.toAlgebra
  haveI : IsScalarTower V₀ ↥O F := IsScalarTower.of_algebraMap_eq fun v => (htoO v).symm
  have hx' : IsIntegral ↥O x := hx.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥O) (K := F)).mp hx'
  rw [← hy]
  exact y.2

def resVα (R₁ : RegularProlongation A F Fb) (α : K →ₐ[L] F) : ↥(R₁.integers.comap α.toRingHom) →+* Fb where
  toFun v := R₁.residue ⟨α (v : K), v.2⟩
  map_one' := by
    have : (⟨α ((1 : ↥(R₁.integers.comap α.toRingHom)) : K), (1 : ↥(R₁.integers.comap α.toRingHom)).2⟩ : ↥R₁.integers) = 1 :=
      Subtype.ext (map_one α)
    rw [this, map_one]
  map_mul' v w := by
    have : (⟨α ((v * w : ↥(R₁.integers.comap α.toRingHom)) : K), (v * w).2⟩ : ↥R₁.integers) = ⟨α (v : K), v.2⟩ * ⟨α (w : K), w.2⟩ :=
      Subtype.ext (map_mul α _ _)
    rw [this, map_mul]
  map_zero' := by
    have : (⟨α ((0 : ↥(R₁.integers.comap α.toRingHom)) : K), (0 : ↥(R₁.integers.comap α.toRingHom)).2⟩ : ↥R₁.integers) = 0 :=
      Subtype.ext (map_zero α)
    rw [this, map_zero]
  map_add' v w := by
    have : (⟨α ((v + w : ↥(R₁.integers.comap α.toRingHom)) : K), (v + w).2⟩ : ↥R₁.integers) = ⟨α (v : K), v.2⟩ + ⟨α (w : K), w.2⟩ :=
      Subtype.ext (map_add α _ _)
    rw [this, map_add]

theorem resVα_apply (R₁ : RegularProlongation A F Fb) (α : K →ₐ[L] F) (v : ↥(R₁.integers.comap α.toRingHom)) :
    resVα R₁ α v = R₁.residue ⟨α (v : K), v.2⟩ := rfl

theorem residue_alpha_eq_zero_of_mem_maximalIdeal (R₁ : RegularProlongation A F Fb) (α : K →ₐ[L] F)
    (v : ↥(R₁.integers.comap α.toRingHom)) (hv : v ∈ maximalIdeal ↥(R₁.integers.comap α.toRingHom)) :
    R₁.residue ⟨α (v : K), v.2⟩ = 0 := by
  by_contra hne
  apply (mem_maximalIdeal v).mp hv
  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp (R₁.isUnit_of_residue_ne_zero hne)
  have hv0 : (v : K) ≠ 0 := by
    intro h0; apply hne
    have : (⟨α (v : K), v.2⟩ : ↥R₁.integers) = 0 := Subtype.ext (by simp [h0])
    rw [this, map_zero]
  have hb' : (b : F) = (α (v : K))⁻¹ := eq_inv_of_mul_eq_one_right (by simpa using congrArg Subtype.val hb)
  have hinv : (v : K)⁻¹ ∈ R₁.integers.comap α.toRingHom := by
    change α (v : K)⁻¹ ∈ R₁.integers
    rw [map_inv₀, ← hb']; exact b.2
  exact ⟨⟨v, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hv0), Subtype.ext (inv_mul_cancel₀ hv0)⟩, rfl⟩

omit [Algebra L K] in

theorem mem_integers_of_mem_adjoin {V₀ : Type*} [CommRing V₀] [Algebra V₀ F] (R : RegularProlongation A F Fb)
    (hV : ∀ v : V₀, algebraMap V₀ F v ∈ R.integers) (s : Finset F) (hint : ∀ g ∈ s, IsIntegral V₀ g)
    (g : F) (hg : g ∈ Algebra.adjoin V₀ (↑s : Set F)) : g ∈ R.integers := by
  let toR : V₀ →+* ↥R.integers := RingHom.codRestrict (algebraMap V₀ F) R.integers hV
  refine Algebra.adjoin_induction (fun x hx => ?_) (fun v => hV v) (fun _ _ _ _ => add_mem) (fun _ _ _ _ => mul_mem) hg
  exact mem_of_isIntegral_tower R.integers toR (fun _ => rfl) (hint x hx)

omit [Algebra L K] [Algebra L F] [Algebra (ResidueField ↥A) Fb] in

theorem span_adjoin_eq_top {V₀ : Type*} [CommRing V₀] [Algebra V₀ F] [Algebra K F] (s : Finset F)
    (hspan : Submodule.span K (↑s : Set F) = ⊤) :
    Submodule.span K ((Algebra.adjoin V₀ (↑s : Set F) : Subalgebra V₀ F) : Set F) = ⊤ :=
  eq_top_iff.mpr (hspan ▸ Submodule.span_mono Algebra.subset_adjoin)

end Common
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum.Ws49 P2MW.S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum.Ws49.NormRed"

end Ws49.NormRed
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum.Ws49 P2MW.S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum.Ws49.NormRed"
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum.Ws49 P2MW.S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum.Ws49.NormRed"

namespace Ws49
namespace NormRed
section Packaged

variable {K F Fb k : Type*} [Field K] [Field F] [Field Fb] [Field k] [Algebra K F] [Algebra k Fb]
  (V : ValuationSubring K) [Algebra ↥V F] [IsScalarTower ↥V K F]
  (resV : ↥V →+* Fb) (hker : ∀ v : ↥V, v ∈ maximalIdeal ↥V → resV v = 0) (φ : Fb →ₐ[k] Fb)
  {L : Type*} [Field L] [Algebra L F] {A : ValuationSubring L} [Algebra (ResidueField ↥A) Fb]
  (R₁ R₂ : RegularProlongation A F Fb)
  (hV₁ : ∀ v : ↥V, algebraMap ↥V F v ∈ R₁.integers)
  (hρ₁ : ∀ v : ↥V, R₁.residue ⟨algebraMap ↥V F v, hV₁ v⟩ = resV v)
  (hV₂ : ∀ v : ↥V, algebraMap ↥V F v ∈ R₂.integers)
  (hρ₂ : ∀ v : ↥V, R₂.residue ⟨algebraMap ↥V F v, hV₂ v⟩ = φ (resV v))

include hker hV₁ hρ₁ hV₂ hρ₂ in

theorem residue_norm_factorization_of_finset {p : ℕ} [Fact p.Prime] [CharP Fb p]
    (hsurjN : Function.Surjective resV)
    (hφdeg : finrankAlong k φ = p)
    (hφpow : ∀ y : Fb, ∃ c : Fb, φ c = y ^ p)
    (hdeg : Module.finrank K F = p + 1)
    (s : Finset F) (hint : ∀ g ∈ s, IsIntegral ↥V g)
    (hspan : Submodule.span K (↑s : Set F) = ⊤)
    (hsurjS : ∀ a b : Fb, ∃ g ∈ Algebra.adjoin ↥V (↑s : Set F), ∃ (hg₁ : g ∈ R₁.integers) (hg₂ : g ∈ R₂.integers),
      R₁.residue ⟨g, hg₁⟩ = a ∧ R₂.residue ⟨g, hg₂⟩ = b)
    (f : F) (hf : f ∈ Algebra.adjoin ↥V (↑s : Set F)) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers) :
    ∃ (hn : algebraMap K F (Algebra.norm K f) ∈ R₁.integers) (g₂ : Fb), φ g₂ = (R₂.residue ⟨f, h₂⟩) ^ p ∧
      R₁.residue ⟨algebraMap K F (Algebra.norm K f), hn⟩ = R₁.residue ⟨f, h₁⟩ * g₂ := by
  classical
  haveI : Module.Finite ↥V ↥(Algebra.adjoin ↥V (↑s : Set F)) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral s.finite_toSet hint
  have hS₁ : ∀ g ∈ Algebra.adjoin ↥V (↑s : Set F), g ∈ R₁.integers := mem_integers_of_mem_adjoin R₁ hV₁ s hint
  have hS₂ : ∀ g ∈ Algebra.adjoin ↥V (↑s : Set F), g ∈ R₂.integers := mem_integers_of_mem_adjoin R₂ hV₂ s hint
  have hspanS : Submodule.span K ((Algebra.adjoin ↥V (↑s : Set F) : Subalgebra ↥V F) : Set F) = ⊤ :=
    eq_top_iff.mpr (hspan ▸ Submodule.span_mono Algebra.subset_adjoin)
  have hsurjS' : ∀ a b : Fb, ∃ (g : F) (hg : g ∈ Algebra.adjoin ↥V (↑s : Set F)),
      R₁.residue ⟨g, hS₁ g hg⟩ = a ∧ R₂.residue ⟨g, hS₂ g hg⟩ = b := by
    intro a b
    obtain ⟨g, hg, hg₁, hg₂, e₁, e₂⟩ := hsurjS a b
    exact ⟨g, hg, e₁, e₂⟩
  obtain ⟨hn, g₂, hg₂, hfac⟩ := residue_norm_factorization V resV hker φ R₁ R₂ (Algebra.adjoin ↥V (↑s : Set F)) hS₁ hS₂ hV₁ hρ₁ hV₂ hρ₂
    hsurjN hφdeg hφpow hdeg hspanS hsurjS' f hf
  exact ⟨hn, g₂, hg₂, hfac⟩

end Packaged
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum.Ws49 P2MW.S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum.Ws49.NormRed"
end Ws49.NormRed
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum.Ws49 P2MW.S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum.Ws49.NormRed"
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum.Ws49 P2MW.S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum.Ws49.NormRed"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups
open Ws49.NormRed

scoped instance Ws49.NormRed.charP_qExpFunctionFieldC (κ : Type*) [Field κ] (p : ℕ) [CharP κ p] (Γ : Subgroup SL(2, ℤ)) :
    CharP ↥(qExpFunctionFieldC κ Γ) p :=
  (Algebra.charP_iff κ ↥(qExpFunctionFieldC κ Γ) p).mp inferInstance

p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum.Ws49 P2MW.S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum.Ws49.NormRed"
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩)) :
    ∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
        Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
        letI := algebraAlong α
        ∃ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), g ≠ 0 ∧
          (∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
            (∀ V, D V = V.ord (Algebra.norm ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) f)) →
            ∀ v', Finsupp.mapDomain Psp.sp D v' = v'.ord g) ∧
          ∀ u : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
            (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u).ord g =
              (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u).ord (Rpd.R₁.residue ⟨f, h₁⟩) +
                u.ord (Rpd.R₂.residue ⟨f, h₂⟩) := by
  intro f h₁ h₂ hr₁ hr₂
  clear hδ hpb hwgen hβ

  letI : Field ↥(xHFunctionFieldBar M H) := inferInstance
  letI : Field ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := inferInstance
  letI : Field (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := inferInstance
  letI : Algebra (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := inferInstance
  letI : Algebra (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := inferInstance
  letI : Algebra (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := inferInstance
  letI instKF : Algebra ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) := algebraAlong α
  classical

  let V : ValuationSubring ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := Rpd.R₁.integers.comap α.toRingHom
  letI instVF : Algebra ↥V ↥(xHFunctionFieldBar M H) := (α.toRingHom.comp V.subtype).toAlgebra
  haveI : IsScalarTower ↥V ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let resV : ↥V →+* JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A) := resVα Rpd.R₁ α
  have hker : ∀ v : ↥V, v ∈ maximalIdeal ↥V → resV v = 0 := fun v hv =>
    residue_alpha_eq_zero_of_mem_maximalIdeal Rpd.R₁ α v hv

  have hφ0 : ∀ y : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p y = 0 → y = 0 := fun y hy =>
    (map_eq_zero_iff _ (qExpFrobeniusModL_injective (ResidueField ↥A) (ΓN p M H hpM) p)).mp hy
  have hφpow : ∀ y : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), ∃ c, qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p c = y ^ p :=
    exists_qExpFrobeniusModL_eq_pow (ResidueField ↥A) (ΓN p M H hpM) p
  have hφdeg : finrankAlong (ResidueField ↥A) (qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p) = p := by
    obtain ⟨x, -, hxt, hfin⟩ := exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed (ResidueField ↥A)
      (ΓN p M H hpM) (translation_mem_GammaH _ _)
    exact (qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental (ResidueField ↥A) (ℓ := p) (ΓN p M H hpM) ⟨x, hxt, hfin⟩).2

  have hdeg := finrankAlong_eq_add_one_of_coe_eq_xHFunctionFieldBar p M H hpM hpM2 hHp α hα_coe
  dsimp only [finrankAlong] at hdeg

  have hsurjN : Function.Surjective resV := by
    intro a
    obtain ⟨v, hv, hva⟩ := JHPlaceSpecialization.ProlongationDatum.exists_residue_alpha_eq p M H hpM hpM2 A hA θ α hα_coe Psp Rpd a
    exact ⟨⟨v, hv⟩, hva⟩

  have hV₁ : ∀ v : ↥V, algebraMap ↥V ↥(xHFunctionFieldBar M H) v ∈ Rpd.R₁.integers := fun v => v.2
  have hρ₁ : ∀ v : ↥V, Rpd.R₁.residue ⟨algebraMap ↥V ↥(xHFunctionFieldBar M H) v, hV₁ v⟩ = resV v := fun v => rfl
  have hV₂ : ∀ v : ↥V, algebraMap ↥V ↥(xHFunctionFieldBar M H) v ∈ Rpd.R₂.integers := fun v =>
    mem₂_of_mem₁ Rpd.R₁ Rpd.R₂ α _ hφ0 hres₂α (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) v.2
  have hρ₂ : ∀ v : ↥V, Rpd.R₂.residue ⟨algebraMap ↥V ↥(xHFunctionFieldBar M H) v, hV₂ v⟩ =
      qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (resV v) := fun v =>
    hres₂α (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) v.2 (hV₂ v)

  obtain ⟨s, hint, hfS, hspan, hsurjS⟩ :=
    JHPlaceSpecialization.ProlongationDatum.exists_finset_isIntegral_span_residue_surjective p M H hpM hpM2 hHp A hA θ α hα_coe hα
      Psp Rpd hres₂α f h₁ h₂ hr₁ hr₂
  obtain ⟨hn, g₂, hg₂, hfac⟩ := residue_norm_factorization_of_finset V resV hker (qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p)
    Rpd.R₁ Rpd.R₂ hV₁ hρ₁ hV₂ hρ₂ hsurjN hφdeg hφpow hdeg s hint hspan hsurjS f hfS h₁ h₂

  have hg₂0 : g₂ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hg₂
    exact pow_ne_zero p hr₂ hg₂.symm
  have hne : Rpd.R₁.residue ⟨algebraMap ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) (Algebra.norm ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) f), hn⟩ ≠ 0 := by
    rw [hfac]; exact mul_ne_zero hr₁ hg₂0
  refine ⟨Rpd.R₁.residue ⟨algebraMap ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) (Algebra.norm ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) f), hn⟩, hne, ?_, ?_⟩
  · intro D hD v'
    exact JHPlaceSpecialization.ProlongationDatum.mapDomain_sp_eq_ord_residue_alpha_full p M H hpM hpM2 hHp A hA θ α hα_coe Psp Rpd
      (Algebra.norm ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) f) hn hne D hD v'
  · intro u
    rw [hfac, (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u).ord_mul hr₁ hg₂0,
      ord_qExpFrobeniusPlaceModL_eq_ord_of_qExpFrobeniusModL_eq_pow (ResidueField ↥A) p (ΓN p M H hpM) g₂ _ hg₂ u]

end
end S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_mapDomain_sp_eq_ord_and_ord_frob_eq_add_of_norm_of_prolongationDatum (solution)
