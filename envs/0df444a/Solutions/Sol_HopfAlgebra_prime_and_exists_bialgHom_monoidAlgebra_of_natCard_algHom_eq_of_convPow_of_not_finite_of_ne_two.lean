-- Prove2me | solution 1 for HopfAlgebra.prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/a8b8de22-c8ce-5649-abe7-b38745520076

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_AlgHom_comp_injective_and_exists_comp_eq_iff_of_sub_one_mem_span_of_mul_sub_eq_zero
import Theorems.Thm_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg
import Theorems.Thm_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat
import Theorems.Thm_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_ratLocalizedAt_eq_of_convPow_of_ne_two
import Theorems.Thm_Submodule_mem_of_forall_prime_exists_smul_mem
import Theorems.Thm_Submodule_mem_span_ratLocalizedAt_iff
import Theorems.Thm_Submodule_eq_of_forall_prime_span_ratLocalizedAt_eq
import Theorems.Thm_Subalgebra_eq_integralClosure_of_etale_of_span_eq_top
import Theorems.Thm_HopfAlgebra_etale_of_pow_eq_one_of_isUnit_of_finite
import Theorems.Thm_HopfAlgebra_convPow_natCard_algHom_algebraicClosure_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul mem_flatClosure_iff"

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open_scoped "TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.TensorProduct"

p2m_open "TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.TensorProduct Polynomial"

namespace Algebra
p2m_export "Algebra" "algebraMap_eq_smul_one TensorProduct.cancelBaseChange_tmul FiniteType.out ofId map_top commutes TensorProduct.includeRight adjoin_mono TensorProduct.lift_tmul mk algebraMap TensorProduct.lid TensorProduct.congr mem_top TensorProduct.lift eq_top_iff mem_sInf FiniteType.of_surjective adjoin_le adjoin_eq_span toSMul norm TensorProduct.map_tmul TensorProduct.comm IsIntegral.isIntegral FiniteType TensorProduct.ext' IsIntegral.finite toModule Etale smul_def TensorProduct.includeRight_apply adjoin FiniteType.isNoetherianRing id subset_adjoin Etale.of_equiv restrictScalars TensorProduct.comm_tmul TensorProduct.map TensorProduct.cancelBaseChange TensorProduct.ext adjoin_induction TensorProduct.lid_tmul"
namespace FiniteTypeLocal
p2m_open "Algebra"

variable {R : Type*} [CommRing R] {K : Type*} [CommRing K] [Algebra R K]

theorem isIntegral_smul_of_smul_aeval_eq_zero {P : R[X]} (hP : P.Monic) (x : K) (u : R)
    (h : u • aeval x P = 0) : IsIntegral R (u • x) := by
  have h1 : aeval x (C u * P) = 0 := by
    rw [map_mul, aeval_C, ← Algebra.smul_def, h]
  have h2 := isIntegral_leadingCoeff_smul (C u * P) x h1
  rwa [leadingCoeff_mul_monic hP, leadingCoeff_C] at h2

theorem exists_smul_isIntegral_of_finite_baseChange (p : Ideal R) [p.IsPrime]
    (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p]
    [Module.Finite Rₚ (Rₚ ⊗[R] K)] (x : K) : ∃ s ∈ p.primeCompl, IsIntegral R (s • x) := by
  have hint : IsIntegral Rₚ ((1 : Rₚ) ⊗ₜ[R] x) := Algebra.IsIntegral.isIntegral _
  obtain ⟨⟨t, ht⟩, hti⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization p.primeCompl ((1 : Rₚ) ⊗ₜ[R] x) hint
  have h1 : (⟨t, ht⟩ : p.primeCompl) • ((1 : Rₚ) ⊗ₜ[R] x) = (1 : Rₚ) ⊗ₜ[R] (t • x) := by
    change (t : R) • ((1 : Rₚ) ⊗ₜ[R] x) = _
    rw [TensorProduct.tmul_smul]
  rw [h1] at hti
  obtain ⟨P, hPm, hP0⟩ := hti
  have h2 : (TensorProduct.mk R Rₚ K 1) (aeval (t • x) P) = (TensorProduct.mk R Rₚ K 1) 0 := by
    rw [map_zero]
    have : aeval ((1 : Rₚ) ⊗ₜ[R] (t • x)) P
        = Algebra.TensorProduct.includeRight (R := R) (A := Rₚ) (aeval (t • x) P) := by
      rw [← Polynomial.aeval_algHom_apply]
      rfl
    rw [Polynomial.aeval_def] at this
    rw [TensorProduct.mk_apply]
    exact (this.symm.trans hP0 : _)
  obtain ⟨⟨u, hu⟩, hu0⟩ := (IsLocalizedModule.eq_iff_exists p.primeCompl _).mp h2
  refine ⟨u * t, mul_mem hu ht, ?_⟩
  rw [mul_smul]
  refine isIntegral_smul_of_smul_aeval_eq_zero hPm _ _ ?_
  simpa using hu0

theorem isIntegral_of_exists_smul_isIntegral_maximal
    (h : ∀ (m : Ideal R) [m.IsMaximal] (x : K), ∃ s ∈ m.primeCompl, IsIntegral R (s • x)) :
    Algebra.IsIntegral R K := by
  refine ⟨fun x => ?_⟩
  let I : Ideal R := (Subalgebra.toSubmodule (integralClosure R K)).comap (LinearMap.toSpanSingleton R K x)
  have hI : ∀ r : R, r ∈ I ↔ IsIntegral R (r • x) := fun r => Iff.rfl
  by_cases htop : I = ⊤
  · have h1 : (1 : R) ∈ I := htop ▸ Submodule.mem_top
    rw [hI, one_smul] at h1
    exact h1
  · obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I htop
    obtain ⟨s, hs, hsx⟩ := h m x
    exact absurd (hIm ((hI s).2 hsx)) hs

private theorem _root_.Module.Finite.of_exists_smul_isIntegral_maximal [Algebra.FiniteType R K]
    (h : ∀ (m : Ideal R) [m.IsMaximal] (x : K), ∃ s ∈ m.primeCompl, IsIntegral R (s • x)) :
    Module.Finite R K :=
  have := isIntegral_of_exists_smul_isIntegral_maximal h
  Algebra.IsIntegral.finite

p2m_alias "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Module.Finite.of_exists_smul_isIntegral_maximal" "Module.Finite.of_exists_smul_isIntegral_maximal"

private theorem _root_.Module.Finite.of_finite_baseChange_localization_maximal [Algebra.FiniteType R K]
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      Module.Finite (Localization.AtPrime m) (Localization.AtPrime m ⊗[R] K)) :
    Module.Finite R K :=
  Module.Finite.of_exists_smul_isIntegral_maximal fun m _ x =>
    exists_smul_isIntegral_of_finite_baseChange m (Localization.AtPrime m) x

p2m_alias "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Module.Finite.of_finite_baseChange_localization_maximal" "Module.Finite.of_finite_baseChange_localization_maximal"
end Algebra.FiniteTypeLocal

section IntModuleTransport

namespace Module p2m_export "Module" "Flat Injective equiv Finite.equiv finrank Free finite_iff_isArtinianRing mk ext' Finite.of_injective free_of_finite_type_torsion_free' Finite.iff_fg restrictScalars finrank_baseChange Flat.isSMulRegular_of_nonZeroDivisors jacobson IsPrincipal Finite.of_exists_smul_isIntegral_maximal Finite.of_finite_baseChange_localization_maximal Finite.of_finite_algHom_of_isAlgClosed Finite.rat_baseChange_of_finite_algHom" namespace Finite p2m_export "Module.Finite" "left equiv trans range map of_injective iff_fg of_surjective self of_exists_smul_isIntegral_maximal of_finite_baseChange_localization_maximal of_finite_algHom_of_isAlgClosed rat_baseChange_of_finite_algHom" end Module.Finite
namespace Module.Finite
p2m_open_scoped "Module Module.Finite" in
private theorem _root_.Module.Finite.of_intModule_eq (K : Type*) [AddCommGroup K] (i₁ i₂ : Module ℤ K)
    (h : @Module.Finite ℤ K _ _ i₁) : @Module.Finite ℤ K _ _ i₂ := by
  cases Subsingleton.elim i₁ i₂; exact h

end Module.Finite
p2m_export "" "Module.Finite.of_intModule_eq"
p2m_open_scoped "Module Module.Finite" in
theorem Module.Finite.baseChange_of_intModule_eq (S : Type*) [CommRing S] (K : Type*) [AddCommGroup K]
    (i₁ i₂ : Module ℤ K)
    (h : by letI := i₁; exact Module.Finite S (TensorProduct ℤ S K)) :
    by letI := i₂; exact Module.Finite S (TensorProduct ℤ S K) := by
  cases Subsingleton.elim i₁ i₂; exact h

end IntModuleTransport

p2m_open "TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.TensorProduct"

namespace GaloisRep
p2m_export "GaloisRep" "ratLocalizedAt"
p2m_open "GaloisRep~isFractionRing_ratLocalizedAt~isDiscreteValuationRing_ratLocalizedAt"

theorem mem_ratLocalizedAt_iff {p : ℕ} {x : ℚ} : x ∈ ratLocalizedAt p ↔ x.den.Coprime p := Iff.rfl

scoped instance isPrime_span_natCast (ℓ : ℕ) [hℓ : Fact ℓ.Prime] : (Ideal.span {(ℓ : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hℓ.out.ne_zero)).2 (Nat.prime_iff_prime_int.1 hℓ.out)

theorem mem_primeCompl_span_natCast_iff {ℓ : ℕ} [Fact ℓ.Prime] {z : ℤ} :
    z ∈ (Ideal.span {(ℓ : ℤ)}).primeCompl ↔ ¬ ℓ ∣ z.natAbs := by
  rw [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton, Int.natCast_dvd]

scoped instance isLocalizationAtPrime_ratLocalizedAt (ℓ : ℕ) [hℓ : Fact ℓ.Prime] :
    IsLocalization.AtPrime (ratLocalizedAt ℓ) (Ideal.span {(ℓ : ℤ)}) where
  map_units := by
    rintro ⟨y, hy⟩
    rw [mem_primeCompl_span_natCast_iff] at hy
    have hy0 : y ≠ 0 := by rintro rfl; exact hy (by simp)
    have hyQ : (y : ℚ) ≠ 0 := by exact_mod_cast hy0
    have hmem : (y : ℚ)⁻¹ ∈ ratLocalizedAt ℓ := by
      rw [mem_ratLocalizedAt_iff, Rat.inv_intCast_den, if_neg hy0]
      exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ.out).2 hy))
    refine isUnit_iff_exists_inv.2 ⟨⟨(y : ℚ)⁻¹, hmem⟩, ?_⟩
    apply Subtype.ext
    simp [hyQ]
  surj := by
    intro z
    have hden : ¬ ℓ ∣ (z : ℚ).den := fun h =>
      hℓ.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm z.2) h)
    refine ⟨((z : ℚ).num, ⟨((z : ℚ).den : ℤ), ?_⟩), ?_⟩
    · rw [mem_primeCompl_span_natCast_iff, Int.natAbs_natCast]
      exact hden
    · apply Subtype.ext
      simp [Rat.mul_den_eq_num]
  exists_of_eq := by
    intro x y h
    refine ⟨1, ?_⟩
    have h' := congrArg Subtype.val h
    simp only [Subring.coe_intCast, eq_intCast, Int.cast_inj] at h'
    simp [h']

end GaloisRep
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep"

section AnyIntAlgebra

p2m_attr_erase "instance" "AddCommGroup.toIntModule LieRing.instLieAlgebra"

p2m_open_scoped "Module Module.Finite" in
p2m_open "GaloisRep~isFractionRing_ratLocalizedAt~isDiscreteValuationRing_ratLocalizedAt" in open _root_.P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep in

theorem Module.Finite.of_finite_baseChange_ratLocalizedAt (K : Type*) [CommRing K] [Algebra ℤ K]
    [Algebra.FiniteType ℤ K]
    (hff : ∀ ℓ : ℕ, ℓ.Prime → Module.Finite (ratLocalizedAt ℓ) ((ratLocalizedAt ℓ) ⊗[ℤ] K)) :
    Module.Finite ℤ K := by
  refine Module.Finite.of_exists_smul_isIntegral_maximal (R := ℤ) (K := K) fun m hm x => ?_
  obtain ⟨g, hg⟩ : ∃ g : ℤ, m = Ideal.span {g} :=
    ⟨_, (Submodule.IsPrincipal.span_singleton_generator m).symm⟩
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact Ring.ne_bot_of_isMaximal_of_not_isField hm Int.not_isField (by simpa using hg)
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).1 (hg ▸ hm.isPrime)
  haveI : Fact g.natAbs.Prime := ⟨Int.prime_iff_natAbs_prime.1 hgp⟩
  have hspan : m = Ideal.span {(g.natAbs : ℤ)} := by rw [hg, Int.span_natAbs]
  haveI := hff g.natAbs Fact.out
  obtain ⟨s, hs, hsx⟩ := Algebra.FiniteTypeLocal.exists_smul_isIntegral_of_finite_baseChange
    (Ideal.span {(g.natAbs : ℤ)}) (ratLocalizedAt g.natAbs) x
  refine ⟨s, ?_, hsx⟩
  rw [Ideal.mem_primeCompl_iff] at hs ⊢
  rwa [hspan]

namespace Nat p2m_export "Nat" "Coprime.eq_one_of_dvd mod_add_div count Prime.coprime_iff_not_dvd succ Coprime Coprime.coprime_dvd_left choose Coprime.symm cast_eq_zero coprime_comm finite_of_card_ne_zero exists_eq_pow_mul_and_not_dvd divisors Prime cast_injective prime_iff_prime_int any cast_inj castRingHom card_congr all zero cast_one coprime_primes" end Nat
p2m_open_scoped "Nat" in
p2m_open "GaloisRep~isFractionRing_ratLocalizedAt~isDiscreteValuationRing_ratLocalizedAt" in open _root_.P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep in

theorem Nat.prime_of_finite_baseChange_ratLocalizedAt_of_ne_of_not_finite (p : ℕ)
    (K : Type*) [CommRing K] [Algebra ℤ K] [Algebra.FiniteType ℤ K]
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → Module.Finite (ratLocalizedAt ℓ) ((ratLocalizedAt ℓ) ⊗[ℤ] K))
    (hK : ¬ Module.Finite ℤ K) : p.Prime := by
  by_contra hp
  exact hK (Module.Finite.of_finite_baseChange_ratLocalizedAt K fun ℓ hℓ => hff ℓ hℓ (fun h => hp (h ▸ hℓ)))

end AnyIntAlgebra
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep"

namespace GaloisRep
p2m_export "GaloisRep" "ratLocalizedAt"
p2m_open "GaloisRep~isFractionRing_ratLocalizedAt~isDiscreteValuationRing_ratLocalizedAt"

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

scoped instance isFractionRing_ratLocalizedAt : IsFractionRing (ratLocalizedAt ℓ) ℚ :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Ideal.span {(ℓ : ℤ)}).primeCompl
    (ratLocalizedAt ℓ) ℚ

scoped instance isDiscreteValuationRing_ratLocalizedAt : IsDiscreteValuationRing (ratLocalizedAt ℓ) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ (P := Ideal.span {(ℓ : ℤ)})
    (by simpa using (Int.natCast_ne_zero.2 hℓ.out.ne_zero)) (ratLocalizedAt ℓ)

example : IsPrincipalIdealRing (ratLocalizedAt ℓ) := inferInstance
example : IsIntegrallyClosed (ratLocalizedAt ℓ) := inferInstance
example : IsLocalRing (ratLocalizedAt ℓ) := inferInstance
example : IsDedekindDomain (ratLocalizedAt ℓ) := inferInstance

theorem maximalIdeal_ratLocalizedAt :
    IsLocalRing.maximalIdeal (ratLocalizedAt ℓ) = Ideal.span {(ℓ : ratLocalizedAt ℓ)} := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {(ℓ : ℤ)}) (ratLocalizedAt ℓ),
    Ideal.map_span, Set.image_singleton, map_natCast]

theorem irreducible_natCast_ratLocalizedAt' : Irreducible (ℓ : ratLocalizedAt ℓ) := by
  have h := (IsDiscreteValuationRing.irreducible_iff_uniformizer (ℓ : ratLocalizedAt ℓ)).2
    (maximalIdeal_ratLocalizedAt ℓ)
  exact h

end GaloisRep
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep"

namespace GaloisRep
p2m_export "GaloisRep" "ratLocalizedAt"
p2m_open "GaloisRep~isFractionRing_ratLocalizedAt~isDiscreteValuationRing_ratLocalizedAt"

variable {p : ℕ}

theorem mem_ratLocalizedAt_iff' {x : ℚ} : x ∈ ratLocalizedAt p ↔ x.den.Coprime p := Iff.rfl

theorem natCast_mem_ratLocalizedAt (n : ℕ) : (n : ℚ) ∈ ratLocalizedAt p := by
  simp

theorem intCast_mem_ratLocalizedAt (n : ℤ) : (n : ℚ) ∈ ratLocalizedAt p := by
  simp

variable [hp : Fact p.Prime]

theorem notMem_ratLocalizedAt_iff {x : ℚ} : x ∉ ratLocalizedAt p ↔ p ∣ x.den := by
  rw [mem_ratLocalizedAt_iff', Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp.out, not_not]

theorem mem_ratLocalizedAt_iff_padicValRat_nonneg {x : ℚ} :
    x ∈ ratLocalizedAt p ↔ 0 ≤ padicValRat p x := by
  rw [← not_iff_not, notMem_ratLocalizedAt_iff, not_le, padicValRat]
  have hden : x.den ≠ 0 := x.den_nz
  constructor
  · intro h
    have hnum : ¬ (p : ℤ) ∣ x.num := by
      intro h'
      have h1 : p ∣ x.num.natAbs := Int.natCast_dvd.1 h'
      have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 x.reduced) h
      exact hp.out.one_lt.ne' this
    rw [padicValInt.eq_zero_of_not_dvd hnum]
    have : padicValNat p x.den ≠ 0 := fun h0 => by
      rcases padicValNat.eq_zero_iff.1 h0 with h0 | h0 | h0
      exacts [hp.out.one_lt.ne' h0, hden h0, h0 h]
    simp only [CharP.cast_eq_zero, zero_sub, Left.neg_neg_iff]
    exact_mod_cast Nat.pos_of_ne_zero this
  · intro h
    by_contra hnd
    have : padicValNat p x.den = 0 := padicValNat.eq_zero_of_not_dvd hnd
    rw [this] at h
    simp only [CharP.cast_eq_zero, sub_zero] at h
    omega

theorem exists_mul_eq_inv_pow_of_notMem {x : ℚ} (hx : x ∉ ratLocalizedAt p) :
    ∃ (k : ℕ) (w : ℚ), 0 < k ∧ w ∈ ratLocalizedAt p ∧ w * x = ((p : ℚ)⁻¹) ^ k := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
  have hp1 : 1 < p := hp.out.one_lt
  have hv : padicValRat p x < 0 := by
    rwa [mem_ratLocalizedAt_iff_padicValRat_nonneg, not_le] at hx
  refine ⟨(-padicValRat p x).toNat, x⁻¹ * ((p : ℚ)⁻¹) ^ (-padicValRat p x).toNat, by omega, ?_, ?_⟩
  · have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hne : x⁻¹ * ((p : ℚ)⁻¹) ^ (-padicValRat p x).toNat ≠ 0 := by
      simp [hx0, hpQ]
    rw [mem_ratLocalizedAt_iff_padicValRat_nonneg, padicValRat.mul (inv_ne_zero hx0) (by simp [hpQ]),
      padicValRat.inv, padicValRat.pow _, padicValRat.inv, padicValRat.self hp1]
    have : ((-padicValRat p x).toNat : ℤ) = -padicValRat p x := Int.toNat_of_nonneg (by omega)
    omega
  · rw [mul_assoc, mul_comm (((p : ℚ)⁻¹) ^ _) x, ← mul_assoc, inv_mul_cancel₀ hx0, one_mul]

theorem exists_mem_mul_inv_pow_eq (y : ℚ) :
    ∃ (n : ℕ) (r : ℚ), r ∈ ratLocalizedAt p ∧ y = r * ((p : ℚ)⁻¹) ^ n := by
  by_cases hy : y = 0
  · exact ⟨0, 0, zero_mem _, by simp [hy]⟩
  have hp1 : 1 < p := hp.out.one_lt
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  refine ⟨padicValNat p y.den, y * (p : ℚ) ^ padicValNat p y.den, ?_, ?_⟩
  · have hne : y * (p : ℚ) ^ padicValNat p y.den ≠ 0 := by simp [hy, hpQ]
    rw [mem_ratLocalizedAt_iff_padicValRat_nonneg, padicValRat.mul hy (by simp [hpQ]),
      padicValRat.pow _, padicValRat.self hp1, padicValRat]
    push_cast
    omega
  · rw [inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hpQ), mul_one]

end GaloisRep
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep"

p2m_open "TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.TensorProduct"

namespace Algebra
p2m_export "Algebra" "algebraMap_eq_smul_one TensorProduct.cancelBaseChange_tmul FiniteType.out ofId map_top commutes TensorProduct.includeRight adjoin_mono TensorProduct.lift_tmul mk algebraMap TensorProduct.lid TensorProduct.congr mem_top TensorProduct.lift eq_top_iff mem_sInf FiniteType.of_surjective adjoin_le adjoin_eq_span toSMul norm TensorProduct.map_tmul TensorProduct.comm IsIntegral.isIntegral FiniteType TensorProduct.ext' IsIntegral.finite toModule Etale smul_def TensorProduct.includeRight_apply adjoin FiniteType.isNoetherianRing id subset_adjoin Etale.of_equiv restrictScalars TensorProduct.comm_tmul TensorProduct.map TensorProduct.cancelBaseChange TensorProduct.ext adjoin_induction TensorProduct.lid_tmul"
namespace FiniteTypeLocal
p2m_open "Algebra"

section Field

variable (k : Type*) [Field k] (A : Type*) [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
  (Ω : Type*) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]

theorem exists_algHom_ker_eq_of_isMaximal (m : Ideal A) [hm : m.IsMaximal] :
    ∃ φ : A →ₐ[k] Ω, RingHom.ker φ = m := by
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m) (Ideal.Quotient.mkₐ_surjective k m)
  haveI : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  let ψ : (A ⧸ m) →ₐ[k] Ω := IsAlgClosed.lift
  refine ⟨ψ.comp (Ideal.Quotient.mkₐ k m), ?_⟩
  ext a
  rw [RingHom.mem_ker]
  change ψ (Ideal.Quotient.mk m a) = 0 ↔ a ∈ m
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact map_eq_zero_iff ψ (ψ : A ⧸ m →+* Ω).injective

theorem finite_maximalSpectrum_of_finite_algHom [Finite (A →ₐ[k] Ω)] : Finite (MaximalSpectrum A) := by
  classical
  choose φ hφ using fun m : MaximalSpectrum A =>
    @exists_algHom_ker_eq_of_isMaximal k _ A _ _ _ Ω _ _ _ m.asIdeal m.isMaximal
  refine Finite.of_injective φ fun m₁ m₂ h => ?_
  apply MaximalSpectrum.ext
  rw [← hφ m₁, ← hφ m₂, h]

theorem krullDimLE_zero_of_finite_algHom [Finite (A →ₐ[k] Ω)] : Ring.KrullDimLE 0 A := by
  classical
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  haveI := finite_maximalSpectrum_of_finite_algHom k A Ω
  refine Ring.KrullDimLE.mk₀ fun P hP => ?_

  let S : Set (Ideal A) := {J | P ≤ J ∧ J.IsMaximal}
  have hSfin : S.Finite := by
    have : S ⊆ Set.range (fun m : MaximalSpectrum A => m.asIdeal) := by
      rintro J ⟨-, hJ⟩
      exact ⟨⟨J, hJ⟩, rfl⟩
    exact (Set.finite_range _).subset this
  have hjac : P.jacobson = P := IsJacobsonRing.out ‹_› hP.isRadical
  have hinf : hSfin.toFinset.inf (fun J => J) ≤ P := by
    rw [← hjac]
    intro x hx
    rw [Ideal.jacobson, Submodule.mem_sInf]
    intro J hJ
    have : hSfin.toFinset.inf (fun J => J) ≤ J := Finset.inf_le (by simpa [S] using hJ)
    exact this hx
  obtain ⟨J, hJS, hJP⟩ := (Ideal.IsPrime.inf_le' hP).1 hinf
  rw [Set.Finite.mem_toFinset] at hJS
  obtain ⟨hPJ, hJmax⟩ := hJS
  have : P = J := le_antisymm hPJ hJP
  rw [this]
  exact hJmax

private theorem _root_.Module.Finite.of_finite_algHom_of_isAlgClosed [Finite (A →ₐ[k] Ω)] : Module.Finite k A := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : IsArtinianRing A :=
    isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.2 ⟨‹_›, krullDimLE_zero_of_finite_algHom k A Ω⟩
  exact (Module.finite_iff_isArtinianRing k A).2 ‹_›

p2m_alias "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Module.Finite.of_finite_algHom_of_isAlgClosed" "Module.Finite.of_finite_algHom_of_isAlgClosed"
end Field
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep"

section Int

theorem injective_comp_includeRight (K : Type*) [CommRing K] (Ω : Type*) [CommRing Ω] [Algebra ℚ Ω] :
    Function.Injective (fun F : ℚ ⊗[ℤ] K →ₐ[ℚ] Ω =>
      (F.restrictScalars ℤ).comp (Algebra.TensorProduct.includeRight : K →ₐ[ℤ] ℚ ⊗[ℤ] K)) := by
  intro F G h
  apply Algebra.TensorProduct.ext
  · ext
  · exact h

private theorem _root_.Module.Finite.rat_baseChange_of_finite_algHom (K : Type*) [CommRing K] [Algebra.FiniteType ℤ K]
    (Ω : Type*) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω]
    (hpts : Finite (K →ₐ[ℤ] Ω)) : Module.Finite ℚ (ℚ ⊗[ℤ] K) := by
  haveI : Finite (ℚ ⊗[ℤ] K →ₐ[ℚ] Ω) := Finite.of_injective _ (injective_comp_includeRight K Ω)
  exact Module.Finite.of_finite_algHom_of_isAlgClosed ℚ (ℚ ⊗[ℤ] K) Ω

p2m_alias "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Module.Finite.rat_baseChange_of_finite_algHom" "Module.Finite.rat_baseChange_of_finite_algHom"
end Int
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep"

end Algebra.FiniteTypeLocal
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep"
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep"

p2m_open "TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.TensorProduct"

section PowHom
variable {M : Type*} [Monoid M]

def powHomOfPowEqOne (u : M) {n : ℕ} [NeZero n] (hu : u ^ n = 1) : Multiplicative (ZMod n) →* M where
  toFun g := u ^ (Multiplicative.toAdd g).val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, ZMod.val_add, ← pow_add]
    conv_rhs => rw [← Nat.mod_add_div ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val) n,
      pow_add, pow_mul, hu, one_pow, mul_one]

@[scoped simp] theorem powHomOfPowEqOne_apply (u : M) {n : ℕ} [NeZero n] (hu : u ^ n = 1) (g : Multiplicative (ZMod n)) :
    powHomOfPowEqOne u hu g = u ^ (Multiplicative.toAdd g).val := rfl

theorem powHomOfPowEqOne_ofAdd_one (u : M) {n : ℕ} [Fact (1 < n)] (hu : u ^ n = 1) :
    haveI : NeZero n := ⟨(zero_lt_one.trans (Fact.out : 1 < n)).ne'⟩
    powHomOfPowEqOne u hu (Multiplicative.ofAdd 1) = u := by
  simp [ZMod.val_one]

end PowHom
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep"

namespace MonoidAlgebra
p2m_export "MonoidAlgebra" "lsingle_apply module mapDomainAlgHom of_injective mapDomainBialgHom_apply of mapDomain_single unique mapAlgHom lift_single lift_apply lift mapDomainBialgHom one_def ringHom_ext mapRingHom smul_single' of_apply ring induction_on basis_apply single_pow basis smul_single map semiring mapDomain counit_single single mapDomainAlgHom_apply lift_of mapAlgHom_single ext smul_apply single_apply mapRingHom_apply algHom_ext comul_single sum_single algebra mapRingHom_single mapAlgHom_apply mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg"
p2m_open "MonoidAlgebra"

section Lift
variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Bialgebra R A] {G : Type*} [Monoid G]

noncomputable def liftBialgHom (φ : G →* A) (hφ : ∀ g, IsGroupLikeElem R (φ g)) :
    MonoidAlgebra R G →ₐc[R] A :=
  BialgHom.ofAlgHom (MonoidAlgebra.lift R A G φ)
    (by
      refine MonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
      simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, MonoidAlgebra.lift_single, one_smul,
        MonoidAlgebra.counit_single, CommSemiring.counit_apply]
      exact ((isGroupLikeElem_iff R _).1 (hφ g)).1)
    (by
      refine MonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, MonoidAlgebra.lift_single, one_smul,
        MonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul,
        MonoidAlgebra.lsingle_apply, Algebra.TensorProduct.map_tmul]
      exact ((isGroupLikeElem_iff R _).1 (hφ g)).2.symm)

@[scoped simp] theorem liftBialgHom_apply (φ : G →* A) (hφ : ∀ g, IsGroupLikeElem R (φ g)) (x : MonoidAlgebra R G) :
    liftBialgHom φ hφ x = MonoidAlgebra.lift R A G φ x :=
  BialgHom.ofAlgHom_apply _ _ _ _

theorem liftBialgHom_single (φ : G →* A) (hφ : ∀ g, IsGroupLikeElem R (φ g)) (g : G) (r : R) :
    liftBialgHom φ hφ (single g r) = r • φ g := by
  rw [liftBialgHom_apply, MonoidAlgebra.lift_single]

theorem coe_liftBialgHom_eq_linearCombination (φ : G →* A) (hφ : ∀ g, IsGroupLikeElem R (φ g)) :
    ⇑(liftBialgHom φ hφ) =
      ⇑(Finsupp.linearCombination R (φ : G → A) ∘ₗ (MonoidAlgebra.coeffLinearEquiv R).toLinearMap) := by
  funext x
  rw [liftBialgHom_apply, MonoidAlgebra.lift_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    MonoidAlgebra.coeffLinearEquiv_apply, Finsupp.linearCombination_apply]

theorem liftBialgHom_injective_iff (φ : G →* A) (hφ : ∀ g, IsGroupLikeElem R (φ g)) :
    Function.Injective (liftBialgHom φ hφ) ↔ LinearIndependent R (φ : G → A) := by
  rw [coe_liftBialgHom_eq_linearCombination, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap,
    EquivLike.injective_comp]
  rfl

theorem liftBialgHom_surjective_iff (φ : G →* A) (hφ : ∀ g, IsGroupLikeElem R (φ g)) :
    Function.Surjective (liftBialgHom φ hφ) ↔ Submodule.span R (Set.range (φ : G → A)) = ⊤ := by
  rw [coe_liftBialgHom_eq_linearCombination, LinearMap.coe_comp, LinearEquiv.coe_toLinearMap,
    EquivLike.surjective_comp]
  change Function.Surjective (Finsupp.linearCombination R (φ : G → A) : (G →₀ R) →ₗ[R] A) ↔ _
  rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]

noncomputable def liftBialgEquiv (φ : G →* A) (hφ : ∀ g, IsGroupLikeElem R (φ g))
    (hli : LinearIndependent R (φ : G → A)) (hsp : Submodule.span R (Set.range (φ : G → A)) = ⊤) :
    MonoidAlgebra R G ≃ₐc[R] A :=
  BialgEquiv.ofBijective (liftBialgHom φ hφ)
    ⟨(liftBialgHom_injective_iff φ hφ).2 hli, (liftBialgHom_surjective_iff φ hφ).2 hsp⟩

@[scoped simp] theorem liftBialgEquiv_apply (φ : G →* A) (hφ : ∀ g, IsGroupLikeElem R (φ g))
    (hli : LinearIndependent R (φ : G → A)) (hsp : Submodule.span R (Set.range (φ : G → A)) = ⊤)
    (x : MonoidAlgebra R G) : liftBialgEquiv φ hφ hli hsp x = liftBialgHom φ hφ x := rfl

end Lift
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep"

section Hull
variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Bialgebra R A]

noncomputable def hullLift (u : A) {n : ℕ} [NeZero n] (hu : IsGroupLikeElem R u) (hun : u ^ n = 1) :
    MonoidAlgebra R (Multiplicative (ZMod n)) →ₐc[R] A :=
  liftBialgHom (powHomOfPowEqOne u hun) fun _ => hu.pow

theorem hullLift_single (u : A) {n : ℕ} [NeZero n] (hu : IsGroupLikeElem R u) (hun : u ^ n = 1)
    (g : Multiplicative (ZMod n)) (r : R) :
    hullLift u hu hun (single g r) = r • u ^ (Multiplicative.toAdd g).val :=
  liftBialgHom_single _ _ _ _

theorem hullLift_single_ofAdd_one (u : A) {n : ℕ} [Fact (1 < n)] (hu : IsGroupLikeElem R u) (hun : u ^ n = 1) :
    haveI : NeZero n := ⟨(zero_lt_one.trans (Fact.out : 1 < n)).ne'⟩
    hullLift u hu hun (single (Multiplicative.ofAdd 1) 1) = u := by
  rw [hullLift_single, one_smul, toAdd_ofAdd, ZMod.val_one, pow_one]

theorem hullLift_injective_iff (u : A) {n : ℕ} [NeZero n] (hu : IsGroupLikeElem R u) (hun : u ^ n = 1) :
    Function.Injective (hullLift u hu hun) ↔
      LinearIndependent R (fun g : Multiplicative (ZMod n) => u ^ (Multiplicative.toAdd g).val) :=
  liftBialgHom_injective_iff _ _

end Hull
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep"

end MonoidAlgebra
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra"

section Descent
variable {R : Type*} [CommRing R] (F : Type*) [CommRing F] [Algebra R F] (S : Submonoid R) [IsLocalization S F]
  {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace LinearMap p2m_export "LinearMap" "single_apply mem_range range coe_range rank add_apply id module baseChange_tmul range_comp rTensor_tmul map_span smul_apply mulLeft coe_restrictScalars mk coe_coe toSpanSingleton id_apply mul ext range_eq_top map_smul_of_tower comp isIntegral single rTensor baseChange convMul_apply restrictScalars range_eq_map ker convOne_apply mem_ker comp_apply restrict mulRight" end LinearMap
p2m_open_scoped "LinearMap" in

theorem LinearMap.injective_of_injective_baseChange_of_isLocalization
    (hS : ∀ (s : S) (x : M), s • x = 0 → x = 0)
    (f : M →ₗ[R] N) (h : Function.Injective (f.baseChange F)) : Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h1 : (1 : F) ⊗ₜ[R] x = 0 := by
    apply h
    rw [LinearMap.baseChange_tmul, hx, tmul_zero, map_zero]
  have h2 : (TensorProduct.mk R F M 1) x = (TensorProduct.mk R F M 1) 0 := by simpa using h1
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists S _).1 h2
  exact hS s x (by simpa using hs)

p2m_open_scoped "LinearMap" in

theorem LinearMap.injective_of_injective_baseChange_fractionRing [IsDomain R] (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] [NoZeroSMulDivisors R M]
    (f : M →ₗ[R] N) (h : Function.Injective (f.baseChange K)) : Function.Injective f :=
  LinearMap.injective_of_injective_baseChange_of_isLocalization K (nonZeroDivisors R)
    (fun s _ hsx => (smul_eq_zero.1 hsx).resolve_left (nonZeroDivisors.coe_ne_zero s)) f h

end Descent
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra"

section PointsBaseChange

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]
  (K : Type*) [Semiring K] [Bialgebra R K]
  (Ω : Type*) [CommSemiring Ω] [Algebra S Ω] [Algebra R Ω] [IsScalarTower R S Ω]

namespace Algebra p2m_export "Algebra" "algebraMap_eq_smul_one TensorProduct.cancelBaseChange_tmul FiniteType.out ofId map_top commutes TensorProduct.includeRight adjoin_mono TensorProduct.lift_tmul mk algebraMap TensorProduct.lid TensorProduct.congr mem_top TensorProduct.lift eq_top_iff mem_sInf FiniteType.of_surjective adjoin_le adjoin_eq_span toSMul norm TensorProduct.map_tmul TensorProduct.comm IsIntegral.isIntegral FiniteType TensorProduct.ext' IsIntegral.finite toModule Etale smul_def TensorProduct.includeRight_apply adjoin FiniteType.isNoetherianRing id subset_adjoin Etale.of_equiv restrictScalars TensorProduct.comm_tmul TensorProduct.map TensorProduct.cancelBaseChange TensorProduct.ext adjoin_induction TensorProduct.lid_tmul" namespace TensorProduct p2m_export "Algebra.TensorProduct" "cancelBaseChange_tmul basis_apply includeRight lift_tmul congr tensorTensorTensorComm lift map_tmul rTensor algebraMap_apply basis ext' includeRight_apply tensorTensorTensorComm_tmul comm_tmul map ringHom_ext cancelBaseChange ext one_def mul lid_tmul" end Algebra.TensorProduct
p2m_open_scoped "Algebra Algebra.TensorProduct" in

noncomputable def Algebra.TensorProduct.pointsEquiv : (S ⊗[R] K →ₐ[S] Ω) ≃ (K →ₐ[R] Ω) where
  toFun F := (F.restrictScalars R).comp Algebra.TensorProduct.includeRight
  invFun f := Algebra.TensorProduct.lift (Algebra.ofId S Ω) f fun _ _ => Commute.all _ _
  left_inv F := by
    apply Algebra.TensorProduct.ext
    · ext
    · ext k
      simp
  right_inv f := by
    ext k
    simp

p2m_open_scoped "Algebra Algebra.TensorProduct" in
@[scoped simp] theorem Algebra.TensorProduct.pointsEquiv_apply (F : S ⊗[R] K →ₐ[S] Ω) (k : K) :
    Algebra.TensorProduct.pointsEquiv R S K Ω F k = F (1 ⊗ₜ[R] k) := rfl

p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct"
p2m_open_scoped "Algebra Algebra.TensorProduct" in
@[scoped simp] theorem Algebra.TensorProduct.pointsEquiv_symm_apply_tmul (f : K →ₐ[R] Ω) (s : S) (k : K) :
    (Algebra.TensorProduct.pointsEquiv R S K Ω).symm f (s ⊗ₜ[R] k) = algebraMap S Ω s * f k :=
  Algebra.TensorProduct.lift_tmul _ _ (fun _ _ => Commute.all _ _) _ _

p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct"
p2m_open_scoped "Algebra Algebra.TensorProduct" in

theorem Algebra.TensorProduct.pointsEquiv_convMul (F G : WithConv (S ⊗[R] K →ₐ[S] Ω)) :
    Algebra.TensorProduct.pointsEquiv R S K Ω (F * G).ofConv =
      WithConv.ofConv (WithConv.toConv (Algebra.TensorProduct.pointsEquiv R S K Ω F.ofConv) *
        WithConv.toConv (Algebra.TensorProduct.pointsEquiv R S K Ω G.ofConv)) := by
  apply AlgHom.ext
  intro k
  rw [Algebra.TensorProduct.pointsEquiv_apply, AlgHom.convMul_apply, AlgHom.convMul_apply,
    WithConv.ofConv_toConv, WithConv.ofConv_toConv, TensorProduct.comul_tmul, CommSemiring.comul_apply]
  generalize CoalgebraStruct.comul (R := R) k = z
  induction z using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, map_zero]
  | tmul x y =>
      simp only [AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.lift_tmul,
        Algebra.TensorProduct.pointsEquiv_apply]
  | add a b ha hb => simp only [tmul_add, map_add, ha, hb]

p2m_open_scoped "Algebra Algebra.TensorProduct" in

noncomputable def Algebra.TensorProduct.pointsMulEquiv :
    WithConv (S ⊗[R] K →ₐ[S] Ω) ≃* WithConv (K →ₐ[R] Ω) where
  toFun F := WithConv.toConv (Algebra.TensorProduct.pointsEquiv R S K Ω F.ofConv)
  invFun f := WithConv.toConv ((Algebra.TensorProduct.pointsEquiv R S K Ω).symm f.ofConv)
  left_inv F := by simp
  right_inv f := by simp
  map_mul' F G := by
    rw [Algebra.TensorProduct.pointsEquiv_convMul, WithConv.toConv_ofConv]

p2m_open_scoped "Algebra Algebra.TensorProduct" in
@[scoped simp] theorem Algebra.TensorProduct.pointsMulEquiv_apply (F : WithConv (S ⊗[R] K →ₐ[S] Ω)) (k : K) :
    (Algebra.TensorProduct.pointsMulEquiv R S K Ω F).ofConv k = F.ofConv (1 ⊗ₜ[R] k) := rfl

p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct"
end PointsBaseChange
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct"

p2m_open "TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.TensorProduct"

section GroupLikeBaseChange

variable {R : Type*} [CommRing R] (F : Type*) [CommRing F] [Algebra R F]
  {B : Type*} [CommRing B] [Bialgebra R B]

namespace IsGroupLikeElem p2m_export "IsGroupLikeElem" "ne_zero mul pow mk map" end IsGroupLikeElem
namespace IsGroupLikeElem
p2m_open_scoped "IsGroupLikeElem" in

private theorem _root_.IsGroupLikeElem.one_tmul {b : B} (hb : IsGroupLikeElem R b) :
    IsGroupLikeElem F ((1 : F) ⊗ₜ[R] b) := by
  rw [isGroupLikeElem_iff] at hb ⊢
  obtain ⟨hc, hm⟩ := hb
  constructor
  · rw [TensorProduct.counit_tmul, hc, CommSemiring.counit_apply, one_smul]
  · rw [TensorProduct.comul_tmul, hm, CommSemiring.comul_apply,
      AlgebraTensorModule.tensorTensorTensorComm_tmul]

end IsGroupLikeElem
p2m_export "" "IsGroupLikeElem.one_tmul"
variable (S : Submonoid R) [IsLocalization S F]

p2m_open_scoped "IsGroupLikeElem" in

theorem IsGroupLikeElem.of_one_tmul [Module.Flat R B] (hS : S ≤ nonZeroDivisors R) {b : B}
    (hb : IsGroupLikeElem F ((1 : F) ⊗ₜ[R] b)) : IsGroupLikeElem R b := by
  rw [isGroupLikeElem_iff] at hb ⊢
  obtain ⟨hc, hm⟩ := hb
  constructor
  · rw [TensorProduct.counit_tmul, CommSemiring.counit_apply] at hc
    have h1 : algebraMap R F (CoalgebraStruct.counit (R := R) b) = algebraMap R F 1 := by
      rw [Algebra.algebraMap_eq_smul_one, hc, map_one]
    exact IsLocalization.injective F hS h1
  · rw [TensorProduct.comul_tmul, CommSemiring.comul_apply] at hm

    have h2 : (AlgebraTensorModule.tensorTensorTensorComm R F R F F F B B)
        (((1 : F) ⊗ₜ[F] (1 : F)) ⊗ₜ[R] CoalgebraStruct.comul (R := R) b) =
        (AlgebraTensorModule.tensorTensorTensorComm R F R F F F B B)
        (((1 : F) ⊗ₜ[F] (1 : F)) ⊗ₜ[R] (b ⊗ₜ[R] b)) := by
      rw [hm, AlgebraTensorModule.tensorTensorTensorComm_tmul]
    have h3 : ((1 : F) ⊗ₜ[F] (1 : F)) ⊗ₜ[R] CoalgebraStruct.comul (R := R) b =
        ((1 : F) ⊗ₜ[F] (1 : F)) ⊗ₜ[R] (b ⊗ₜ[R] b) :=
      (AlgebraTensorModule.tensorTensorTensorComm R F R F F F B B).injective h2

    let θ : (F ⊗[F] F) ⊗[R] (B ⊗[R] B) →ₗ[R] F ⊗[R] (B ⊗[R] B) :=
      LinearMap.rTensor (B ⊗[R] B) ((TensorProduct.lid F F).toLinearMap.restrictScalars R)
    have h4 := congrArg θ h3
    simp only [θ, LinearMap.rTensor_tmul, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
      TensorProduct.lid_tmul, one_smul] at h4

    have h5 : (TensorProduct.mk R F (B ⊗[R] B) 1) (CoalgebraStruct.comul (R := R) b) =
        (TensorProduct.mk R F (B ⊗[R] B) 1) (b ⊗ₜ[R] b) := h4
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists S _).1 h5
    exact (Module.Flat.isSMulRegular_of_nonZeroDivisors (hS s.2)) hs

theorem isGroupLikeElem_one_tmul_iff [Module.Flat R B] (hS : S ≤ nonZeroDivisors R) (b : B) :
    IsGroupLikeElem F ((1 : F) ⊗ₜ[R] b) ↔ IsGroupLikeElem R b :=
  ⟨IsGroupLikeElem.of_one_tmul F S hS, IsGroupLikeElem.one_tmul F⟩

end GroupLikeBaseChange
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct"

section Embedding

variable {R : Type*} [CommRing R] (S : Submonoid R) (F : Type*) [CommRing F] [Algebra R F] [IsLocalization S F]

namespace TensorProduct p2m_export "TensorProduct" "map_tmul congr map_comm tmul_zero smul_tmul' tensorTensorTensorComm_tmul lift mk tensorTensorTensorComm AlgebraTensorModule.tensorTensorTensorComm ext tmul map ext' AlgebraTensorModule.tensorTensorTensorComm_tmul mk_apply Algebra.smul_def lid_tmul comm_tmul tmul_add tmul_smul counit_tmul comul_tmul" end TensorProduct
p2m_open_scoped "TensorProduct" in
theorem TensorProduct.mk_one_injective_of_isSMulRegular {M : Type*} [AddCommGroup M] [Module R M]
    (hS : ∀ s : S, IsSMulRegular M (s : R)) : Function.Injective (TensorProduct.mk R F M 1) := by
  intro x y h
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists S _).1 h
  exact hS s hs

p2m_open_scoped "TensorProduct" in
theorem TensorProduct.mk_one_injective_of_flat {M : Type*} [AddCommGroup M] [Module R M] [Module.Flat R M]
    (hS : S ≤ nonZeroDivisors R) : Function.Injective (TensorProduct.mk R F M 1) :=
  TensorProduct.mk_one_injective_of_isSMulRegular S F fun s =>
    Module.Flat.isSMulRegular_of_nonZeroDivisors (hS s.2)

p2m_open_scoped "Algebra Algebra.TensorProduct" in

theorem Algebra.TensorProduct.includeRight_injective_of_flat {K : Type*} [Ring K] [Algebra R K]
    [Module.Flat R K] (hS : S ≤ nonZeroDivisors R) :
    Function.Injective (Algebra.TensorProduct.includeRight : K →ₐ[R] F ⊗[R] K) := by
  intro x y h
  apply TensorProduct.mk_one_injective_of_flat S F hS
  simpa [Algebra.TensorProduct.includeRight_apply] using h

end Embedding
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct"

section EBridge

variable {R : Type*} [CommRing R] (S : Submonoid R) (F : Type*) [CommRing F] [Algebra R F] [IsLocalization S F]
  {K : Type*} [CommRing K] [Bialgebra R K]
  {V : Type*} [Semiring V] [Bialgebra F V] [Algebra R V] [IsScalarTower R F V]

namespace Algebra.TensorProduct
p2m_open_scoped "Algebra Algebra.TensorProduct" in

private noncomputable def _root_.Algebra.TensorProduct.restrictBaseChange (ψ : F ⊗[R] K →ₐ[F] V) : K →ₐ[R] V :=
  (ψ.restrictScalars R).comp Algebra.TensorProduct.includeRight

end Algebra.TensorProduct
p2m_export "" "Algebra.TensorProduct.restrictBaseChange"
p2m_open_scoped "Algebra Algebra.TensorProduct" in
omit [IsLocalization S F] in
@[scoped simp] theorem Algebra.TensorProduct.restrictBaseChange_apply (ψ : F ⊗[R] K →ₐ[F] V) (k : K) :
    Algebra.TensorProduct.restrictBaseChange F ψ k = ψ ((1 : F) ⊗ₜ[R] k) := rfl

p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct"
p2m_open_scoped "Algebra Algebra.TensorProduct" in

theorem Algebra.TensorProduct.restrictBaseChange_injective [Module.Flat R K] (hS : S ≤ nonZeroDivisors R)
    (ψ : F ⊗[R] K →ₐ[F] V) (hψ : Function.Injective ψ) :
    Function.Injective (Algebra.TensorProduct.restrictBaseChange F ψ) :=
  hψ.comp (Algebra.TensorProduct.includeRight_injective_of_flat S F hS)

p2m_open_scoped "Algebra Algebra.TensorProduct" in

theorem Algebra.TensorProduct.exists_smul_mem_range_restrictBaseChange (ψ : F ⊗[R] K →ₐ[F] V)
    (hψ : Function.Surjective ψ) (v : V) :
    ∃ d : S, (d : R) • v ∈ Set.range (Algebra.TensorProduct.restrictBaseChange F ψ) := by
  obtain ⟨x, rfl⟩ := hψ v
  obtain ⟨⟨k, d⟩, hkd⟩ := IsLocalizedModule.surj S (TensorProduct.mk R F K 1) x
  refine ⟨d, k, ?_⟩
  rw [Algebra.TensorProduct.restrictBaseChange_apply, ← TensorProduct.mk_apply, ← hkd]
  change ψ ((d : R) • x) = (d : R) • ψ x
  exact ψ.toLinearMap.map_smul_of_tower (d : R) x

p2m_open_scoped "Algebra Algebra.TensorProduct" in
omit [IsLocalization S F] in

theorem Algebra.TensorProduct.counit_restrictBaseChange (ψ : F ⊗[R] K →ₐc[F] V) (k : K) :
    CoalgebraStruct.counit (R := F) (Algebra.TensorProduct.restrictBaseChange F (ψ : F ⊗[R] K →ₐ[F] V) k) =
      algebraMap R F (CoalgebraStruct.counit (R := R) k) := by
  rw [Algebra.TensorProduct.restrictBaseChange_apply]
  change CoalgebraStruct.counit (ψ ((1 : F) ⊗ₜ[R] k)) = _
  rw [CoalgHomClass.counit_comp_apply (R := F) ψ, TensorProduct.counit_tmul, CommSemiring.counit_apply,
    Algebra.algebraMap_eq_smul_one]

namespace IsGroupLikeElem
p2m_open_scoped "IsGroupLikeElem" in
omit [IsLocalization S F] in

private theorem _root_.IsGroupLikeElem.restrictBaseChange (ψ : F ⊗[R] K →ₐc[F] V) {k : K} (hk : IsGroupLikeElem R k) :
    IsGroupLikeElem F (Algebra.TensorProduct.restrictBaseChange F (ψ : F ⊗[R] K →ₐ[F] V) k) := by
  rw [Algebra.TensorProduct.restrictBaseChange_apply]
  exact IsGroupLikeElem.map ψ (hk.one_tmul F)

end IsGroupLikeElem
p2m_export "" "IsGroupLikeElem.restrictBaseChange"

theorem isGroupLikeElem_restrictBaseChange_iff [Module.Flat R K] (hS : S ≤ nonZeroDivisors R)
    {W : Type*} [CommRing W] [Bialgebra F W] [Algebra R W] [IsScalarTower R F W]
    (φ : F ⊗[R] K ≃ₐc[F] W) (k : K) :
    IsGroupLikeElem F (Algebra.TensorProduct.restrictBaseChange F (φ : F ⊗[R] K →ₐ[F] W) k) ↔
      IsGroupLikeElem R k := by
  rw [Algebra.TensorProduct.restrictBaseChange_apply]
  change IsGroupLikeElem F (φ ((1 : F) ⊗ₜ[R] k)) ↔ _
  constructor
  · intro h
    have h' := IsGroupLikeElem.map φ.symm h
    rw [BialgEquiv.symm_apply_apply] at h'
    exact IsGroupLikeElem.of_one_tmul F S hS h'
  · intro h
    exact IsGroupLikeElem.map φ (h.one_tmul F)

end EBridge
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct"

namespace AlgHom
p2m_export "AlgHom" "ext toLinearMap_apply map_adjoin commutes toLinearMap convOne_apply restrictScalars id_apply map_smul_of_tower coe_pow comp range_comp mk coe_restrictScalars coe_range card range_eq_top Finite bijective FiniteType comp_apply FiniteType.of_surjective convMul_apply mem_range comp_injective_and_exists_comp_eq_iff_of_sub_one_mem_span_of_mul_sub_eq_zero"
p2m_open "AlgHom"

section PostComp
variable {R : Type*} [CommSemiring R] {C : Type*} [Semiring C] [Bialgebra R C]
  {A B : Type*} [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra R B]

theorem comp_convMul_ofConv (ψ : A →ₐ[R] B) (f g : WithConv (C →ₐ[R] A)) :
    ψ.comp (f * g).ofConv = (WithConv.toConv (ψ.comp f.ofConv) * WithConv.toConv (ψ.comp g.ofConv)).ofConv := by
  apply AlgHom.ext
  intro c
  rw [AlgHom.comp_apply, AlgHom.convMul_apply, AlgHom.convMul_apply, WithConv.ofConv_toConv,
    WithConv.ofConv_toConv]
  generalize CoalgebraStruct.comul (R := R) c = z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y => simp only [Algebra.TensorProduct.lift_tmul, map_mul, AlgHom.comp_apply]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem comp_convOne_ofConv (ψ : A →ₐ[R] B) :
    ψ.comp (1 : WithConv (C →ₐ[R] A)).ofConv = (1 : WithConv (C →ₐ[R] B)).ofConv := by
  apply AlgHom.ext
  intro c
  rw [AlgHom.comp_apply, AlgHom.convOne_apply, AlgHom.convOne_apply, AlgHom.commutes]

noncomputable def convPostcomp (ψ : A →ₐ[R] B) : WithConv (C →ₐ[R] A) →* WithConv (C →ₐ[R] B) where
  toFun f := WithConv.toConv (ψ.comp f.ofConv)
  map_one' := by rw [comp_convOne_ofConv, WithConv.toConv_ofConv]
  map_mul' f g := by rw [comp_convMul_ofConv, WithConv.toConv_ofConv]

@[scoped simp] theorem convPostcomp_apply (ψ : A →ₐ[R] B) (f : WithConv (C →ₐ[R] A)) :
    convPostcomp ψ f = WithConv.toConv (ψ.comp f.ofConv) := rfl

end PostComp
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct"

section PreComp
variable {R : Type*} [CommSemiring R] {C D : Type*} [Semiring C] [Bialgebra R C] [Semiring D] [Bialgebra R D]
  {A : Type*} [CommSemiring A] [Algebra R A]

theorem convMul_ofConv_comp (π : C →ₐc[R] D) (ψ₁ ψ₂ : WithConv (D →ₐ[R] A)) :
    (ψ₁ * ψ₂).ofConv.comp (π : C →ₐ[R] D)
      = (WithConv.toConv (ψ₁.ofConv.comp (π : C →ₐ[R] D)) * WithConv.toConv (ψ₂.ofConv.comp (π : C →ₐ[R] D))).ofConv := by
  apply AlgHom.ext
  intro h
  rw [AlgHom.comp_apply, AlgHom.convMul_apply, AlgHom.convMul_apply]
  have hc := LinearMap.congr_fun (CoalgHomClass.map_comp_comul π) h
  simp only [LinearMap.comp_apply] at hc
  rw [show CoalgebraStruct.comul (R := R) ((π : C →ₐ[R] D) h) = _ from hc.symm]
  generalize CoalgebraStruct.comul (R := R) h = z
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
      simp only [TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply]
      rfl
  | add a b ha hb => simp only [map_add, ha, hb]

theorem convOne_ofConv_comp (π : C →ₐc[R] D) :
    (1 : WithConv (D →ₐ[R] A)).ofConv.comp (π : C →ₐ[R] D) = (1 : WithConv (C →ₐ[R] A)).ofConv := by
  apply AlgHom.ext
  intro h
  rw [AlgHom.comp_apply, AlgHom.convOne_apply, AlgHom.convOne_apply]
  change (algebraMap R A) (CoalgebraStruct.counit (π h)) = _
  rw [CoalgHomClass.counit_comp_apply (R := R) π]

noncomputable def convPrecomp (π : C →ₐc[R] D) : WithConv (D →ₐ[R] A) →* WithConv (C →ₐ[R] A) where
  toFun ψ := WithConv.toConv (ψ.ofConv.comp (π : C →ₐ[R] D))
  map_one' := by rw [convOne_ofConv_comp, WithConv.toConv_ofConv]
  map_mul' ψ₁ ψ₂ := by rw [convMul_ofConv_comp, WithConv.toConv_ofConv]

@[scoped simp] theorem convPrecomp_apply (π : C →ₐc[R] D) (ψ : WithConv (D →ₐ[R] A)) :
    convPrecomp π ψ = WithConv.toConv (ψ.ofConv.comp (π : C →ₐ[R] D)) := rfl

theorem convPow_ofConv_comp (π : C →ₐc[R] D) (ψ : WithConv (D →ₐ[R] A)) (n : ℕ) :
    (ψ ^ n).ofConv.comp (π : C →ₐ[R] D) = ((WithConv.toConv (ψ.ofConv.comp (π : C →ₐ[R] D))) ^ n).ofConv := by
  have := map_pow (convPrecomp (A := A) π) ψ n
  simp only [convPrecomp_apply] at this
  rw [← this, WithConv.ofConv_toConv]

end PreComp
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct"

section PostCompPow
variable {R : Type*} [CommSemiring R] {C : Type*} [Semiring C] [Bialgebra R C]
  {A B : Type*} [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra R B]

theorem comp_convPow_ofConv (ψ : A →ₐ[R] B) (f : WithConv (C →ₐ[R] A)) (n : ℕ) :
    ψ.comp (f ^ n).ofConv = ((WithConv.toConv (ψ.comp f.ofConv)) ^ n).ofConv := by
  have := map_pow (convPostcomp (C := C) ψ) f n
  simp only [convPostcomp_apply] at this
  rw [← this, WithConv.ofConv_toConv]

end PostCompPow
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct"

end AlgHom
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

section Adams

variable {R : Type*} [CommRing R] (F : Type*) [CommRing F] [Algebra R F]
  {K : Type*} [CommRing K] [Bialgebra R K]
  {W : Type*} [CommRing W] [Bialgebra F W] [Algebra R W] [IsScalarTower R F W]

p2m_open_scoped "Algebra Algebra.TensorProduct" in

theorem Algebra.TensorProduct.convPow_id_restrictBaseChange (ψ : F ⊗[R] K →ₐc[F] W) (n : ℕ) (k : K) :
    ((WithConv.toConv (AlgHom.id F W)) ^ n).ofConv
        (Algebra.TensorProduct.restrictBaseChange F (ψ : F ⊗[R] K →ₐ[F] W) k) =
      Algebra.TensorProduct.restrictBaseChange F (ψ : F ⊗[R] K →ₐ[F] W)
        (((WithConv.toConv (AlgHom.id R K)) ^ n).ofConv k) := by

  have h1 : ((WithConv.toConv (AlgHom.id F W)) ^ n).ofConv.comp (ψ : F ⊗[R] K →ₐ[F] W)
      = ((WithConv.toConv (ψ : F ⊗[R] K →ₐ[F] W)) ^ n).ofConv := by
    rw [AlgHom.convPow_ofConv_comp]
    rfl

  have h2 : Algebra.TensorProduct.pointsMulEquiv R F K W ((WithConv.toConv (ψ : F ⊗[R] K →ₐ[F] W)) ^ n)
      = (Algebra.TensorProduct.pointsMulEquiv R F K W (WithConv.toConv (ψ : F ⊗[R] K →ₐ[F] W))) ^ n :=
    map_pow _ _ _
  have h2' : Algebra.TensorProduct.pointsMulEquiv R F K W (WithConv.toConv (ψ : F ⊗[R] K →ₐ[F] W))
      = WithConv.toConv (Algebra.TensorProduct.restrictBaseChange F (ψ : F ⊗[R] K →ₐ[F] W)) := rfl

  have h3 : (Algebra.TensorProduct.restrictBaseChange F (ψ : F ⊗[R] K →ₐ[F] W)).comp
      (((WithConv.toConv (AlgHom.id R K)) ^ n).ofConv)
      = ((WithConv.toConv (Algebra.TensorProduct.restrictBaseChange F (ψ : F ⊗[R] K →ₐ[F] W))) ^ n).ofConv := by
    rw [AlgHom.comp_convPow_ofConv]
    rfl

  have e1 := congrArg (fun x : WithConv (K →ₐ[R] W) => x.ofConv k) h2
  simp only [h2'] at e1
  rw [Algebra.TensorProduct.pointsMulEquiv_apply] at e1

  rw [← h1, ← h3] at e1
  simpa [Algebra.TensorProduct.restrictBaseChange_apply] using e1

end Adams
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

p2m_open "TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.TensorProduct"

section GroupLikeEval
variable {R : Type*} [CommSemiring R] {C : Type*} [Semiring C] [Bialgebra R C] {A : Type*} [CommSemiring A] [Algebra R A]

namespace AlgHom p2m_export "AlgHom" "ext toLinearMap_apply map_adjoin commutes toLinearMap convOne_apply restrictScalars id_apply map_smul_of_tower coe_pow comp range_comp mk coe_restrictScalars coe_range card range_eq_top Finite bijective FiniteType comp_apply FiniteType.of_surjective convMul_apply mem_range comp_injective_and_exists_comp_eq_iff_of_sub_one_mem_span_of_mul_sub_eq_zero" end AlgHom
p2m_open_scoped "AlgHom" in
theorem AlgHom.convMul_apply_of_isGroupLikeElem (f g : WithConv (C →ₐ[R] A)) {x : C} (hx : IsGroupLikeElem R x) :
    (f * g).ofConv x = f.ofConv x * g.ofConv x := by
  rw [AlgHom.convMul_apply, ((isGroupLikeElem_iff R x).1 hx).2, Algebra.TensorProduct.lift_tmul]

p2m_open_scoped "AlgHom" in
theorem AlgHom.convOne_apply_of_isGroupLikeElem {x : C} (hx : IsGroupLikeElem R x) :
    (1 : WithConv (C →ₐ[R] A)).ofConv x = 1 := by
  rw [AlgHom.convOne_apply, ((isGroupLikeElem_iff R x).1 hx).1, map_one]

p2m_open_scoped "AlgHom" in

theorem AlgHom.convPow_apply_of_isGroupLikeElem (f : WithConv (C →ₐ[R] A)) {x : C} (hx : IsGroupLikeElem R x) (n : ℕ) :
    (f ^ n).ofConv x = (f.ofConv x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, AlgHom.convOne_apply_of_isGroupLikeElem hx]
  | succ n ih => rw [pow_succ, pow_succ, AlgHom.convMul_apply_of_isGroupLikeElem _ _ hx, ih]

end GroupLikeEval
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

namespace MonoidAlgebra
p2m_export "MonoidAlgebra" "lsingle_apply module mapDomainAlgHom of_injective mapDomainBialgHom_apply of mapDomain_single unique mapAlgHom lift_single lift_apply lift mapDomainBialgHom one_def ringHom_ext mapRingHom smul_single' of_apply ring induction_on basis_apply single_pow basis smul_single map semiring mapDomain counit_single single mapDomainAlgHom_apply lift_of mapAlgHom_single ext smul_apply single_apply mapRingHom_apply algHom_ext comul_single sum_single algebra mapRingHom_single mapAlgHom_apply mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg"
p2m_open "MonoidAlgebra"
variable (R : Type*) [CommSemiring R] {G : Type*}

theorem isGroupLikeElem_single_one [Monoid G] (g : G) : IsGroupLikeElem R (single g (1 : R) : MonoidAlgebra R G) := by
  rw [isGroupLikeElem_iff]
  constructor
  · rw [MonoidAlgebra.counit_single, CommSemiring.counit_apply]
  · rw [MonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply]

theorem isGroupLikeElem_of [Monoid G] (g : G) : IsGroupLikeElem R (MonoidAlgebra.of R G g) :=
  isGroupLikeElem_single_one R g

theorem convPow_id_ofConv_single [CommMonoid G] (n : ℕ) (g : G) (r : R) :
    ((WithConv.toConv (AlgHom.id R (MonoidAlgebra R G))) ^ n).ofConv (single g r) = single (g ^ n) r := by
  have h1 : single g r = r • (single g (1 : R) : MonoidAlgebra R G) := by
    rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  rw [h1, map_smul, AlgHom.convPow_apply_of_isGroupLikeElem _ (isGroupLikeElem_single_one R g),
    WithConv.ofConv_toConv, AlgHom.id_apply, MonoidAlgebra.single_pow, one_pow, MonoidAlgebra.smul_single,
    smul_eq_mul, mul_one]

theorem convPow_id_ofConv_eq_mapDomainAlgHom [CommMonoid G] (n : ℕ) :
    ((WithConv.toConv (AlgHom.id R (MonoidAlgebra R G))) ^ n).ofConv =
      MonoidAlgebra.mapDomainAlgHom R R (powMonoidHom n : G →* G) := by
  refine MonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
  rw [convPow_id_ofConv_single, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single,
    powMonoidHom_apply]

theorem convPow_id_ofConv_eq_mapDomainBialgHom [CommMonoid G] (n : ℕ) :
    ((WithConv.toConv (AlgHom.id R (MonoidAlgebra R G))) ^ n).ofConv =
      (MonoidAlgebra.mapDomainBialgHom R (powMonoidHom n : G →* G) : MonoidAlgebra R G →ₐ[R] MonoidAlgebra R G) := by
  refine MonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
  rw [convPow_id_ofConv_single]
  change single (g ^ n) 1 = MonoidAlgebra.mapDomainBialgHom R (powMonoidHom n : G →* G) (single g 1)
  rw [MonoidAlgebra.mapDomainBialgHom_single, powMonoidHom_apply]

end MonoidAlgebra
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

p2m_open "TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.TensorProduct"

section IsCocommTransfer
variable {R : Type*} [CommSemiring R] {A B : Type*} [AddCommMonoid A] [Module R A] [Coalgebra R A]
  [AddCommMonoid B] [Module R B] [Coalgebra R B]

namespace Coalgebra p2m_export "Coalgebra" "TensorProduct.lid TensorProduct.lid_tmul mk TensorProduct.map TensorProduct.map_tmul IsCocomm comm_comul" namespace IsCocomm p2m_export "Coalgebra.IsCocomm" "mk" end Coalgebra.IsCocomm
p2m_open_scoped "Coalgebra Coalgebra.IsCocomm" in

theorem Coalgebra.IsCocomm.of_map_injective (f : A →ₗc[R] B) [Coalgebra.IsCocomm R B]
    (hf : Function.Injective (_root_.TensorProduct.map f.toLinearMap f.toLinearMap)) :
    Coalgebra.IsCocomm R A := by
  refine ⟨?_⟩
  apply LinearMap.ext
  intro a
  apply hf
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, _root_.TensorProduct.map_comm]
  have h1 : _root_.TensorProduct.map f.toLinearMap f.toLinearMap (CoalgebraStruct.comul a)
      = CoalgebraStruct.comul (f a) := by
    have := LinearMap.congr_fun (CoalgHomClass.map_comp_comul f) a
    simpa using this
  rw [h1, Coalgebra.comm_comul]

p2m_open_scoped "Coalgebra Coalgebra.IsCocomm" in

theorem Coalgebra.IsCocomm.of_coalgEquiv (e : A ≃ₗc[R] B) [Coalgebra.IsCocomm R B] : Coalgebra.IsCocomm R A := by
  refine Coalgebra.IsCocomm.of_map_injective (e : A →ₗc[R] B) ?_
  have : _root_.TensorProduct.map (e : A →ₗc[R] B).toLinearMap (e : A →ₗc[R] B).toLinearMap
      = (_root_.TensorProduct.congr (e : A ≃ₗ[R] B) (e : A ≃ₗ[R] B)).toLinearMap := by
    apply _root_.TensorProduct.ext'
    intro x y
    rfl
  rw [this]
  exact (_root_.TensorProduct.congr _ _).injective

end IsCocommTransfer
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

section IsCocommDescent
variable {R : Type*} [CommRing R] (S : Submonoid R) (F : Type*) [CommRing F] [Algebra R F] [IsLocalization S F]
  {B : Type*} [CommRing B] [Bialgebra R B]

p2m_open_scoped "Coalgebra Coalgebra.IsCocomm" in

theorem Coalgebra.IsCocomm.of_baseChange_isLocalization [Module.Flat R B] (hS : S ≤ nonZeroDivisors R)
    [Coalgebra.IsCocomm F (F ⊗[R] B)] : Coalgebra.IsCocomm R B := by
  refine ⟨?_⟩
  apply LinearMap.ext
  intro b
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe]

  have h := Coalgebra.comm_comul F ((1 : F) ⊗ₜ[R] b)
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply] at h

  have key : ∀ z : B ⊗[R] B,
      (TensorProduct.comm F (F ⊗[R] B) (F ⊗[R] B))
        ((AlgebraTensorModule.tensorTensorTensorComm R F R F F F B B) (((1 : F) ⊗ₜ[F] (1 : F)) ⊗ₜ[R] z))
      = (AlgebraTensorModule.tensorTensorTensorComm R F R F F F B B)
        (((1 : F) ⊗ₜ[F] (1 : F)) ⊗ₜ[R] (TensorProduct.comm R B B z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [tmul_zero, LinearEquiv.map_zero]
    | tmul x y =>
        simp only [AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.comm_tmul]
    | add x y hx hy => simp only [tmul_add, LinearEquiv.map_add, hx, hy]
  rw [key] at h
  have h3 : ((1 : F) ⊗ₜ[F] (1 : F)) ⊗ₜ[R] (TensorProduct.comm R B B (CoalgebraStruct.comul (R := R) b)) =
      ((1 : F) ⊗ₜ[F] (1 : F)) ⊗ₜ[R] CoalgebraStruct.comul (R := R) b :=
    (AlgebraTensorModule.tensorTensorTensorComm R F R F F F B B).injective h
  let θ : (F ⊗[F] F) ⊗[R] (B ⊗[R] B) →ₗ[R] F ⊗[R] (B ⊗[R] B) :=
    LinearMap.rTensor (B ⊗[R] B) ((TensorProduct.lid F F).toLinearMap.restrictScalars R)
  have h4 := congrArg θ h3
  simp only [θ, LinearMap.rTensor_tmul, LinearMap.coe_restrictScalars] at h4
  have h5 : (TensorProduct.mk R F (B ⊗[R] B) 1) (TensorProduct.comm R B B (CoalgebraStruct.comul (R := R) b)) =
      (TensorProduct.mk R F (B ⊗[R] B) 1) (CoalgebraStruct.comul (R := R) b) := by
    simpa using h4
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_iff_exists S _).1 h5
  exact (Module.Flat.isSMulRegular_of_nonZeroDivisors (hS s.2)) hs

end IsCocommDescent
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

section FreeRank
variable (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

namespace Module p2m_export "Module" "Flat Injective equiv Finite.equiv finrank Free finite_iff_isArtinianRing mk ext' Finite.of_injective free_of_finite_type_torsion_free' Finite.iff_fg restrictScalars finrank_baseChange Flat.isSMulRegular_of_nonZeroDivisors jacobson IsPrincipal Finite.of_exists_smul_isIntegral_maximal Finite.of_finite_baseChange_localization_maximal Finite.of_finite_algHom_of_isAlgClosed Finite.rat_baseChange_of_finite_algHom" end Module
p2m_open_scoped "Module" in

theorem Module.free_of_finite_of_flat (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Flat R M] : Module.Free R M :=
  Module.free_of_finite_type_torsion_free'

p2m_open_scoped "Module" in

theorem Module.finrank_eq_finrank_baseChange_of_flat (F : Type*) [Field F] [Algebra R F]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] :
    Module.finrank R M = Module.finrank F (F ⊗[R] M) := by
  haveI := Module.free_of_finite_of_flat R M
  rw [Module.finrank_baseChange]

end FreeRank
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

section CyclotomicExponent

theorem exists_pow_eq_apply_of_pow_eq_one (L : Type*) [CommRing L] [IsDomain L] (q : ℕ) [NeZero q]
    (σ : L ≃+* L) : ∃ n : ℕ, ∀ ζ : L, ζ ^ q = 1 → σ ζ = ζ ^ n := by
  haveI : IsCyclic (rootsOfUnity q L) := rootsOfUnity.isCyclic L q
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := rootsOfUnity q L)
  have hgq : (((g : Lˣ) : L)) ^ q = 1 := by
    have := g.2
    rw [mem_rootsOfUnity] at this
    have := congrArg (fun u : Lˣ => (u : L)) this
    simpa using this
  have hσg : (σ ((g : Lˣ) : L)) ^ q = 1 := by rw [← map_pow, hgq, map_one]

  have hpow : ∀ ζ : L, ∀ hζ : ζ ^ q = 1, ∃ k : ℕ, ζ = ((g : Lˣ) : L) ^ k := by
    intro ζ hζ
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.2 (hg (rootsOfUnity.mkOfPowEq ζ hζ)))
    refine ⟨k, ?_⟩
    have := congrArg (fun x : rootsOfUnity q L => ((x : Lˣ) : L)) hk
    simp only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, rootsOfUnity.val_mkOfPowEq_coe] at this
    exact this.symm
  obtain ⟨n, hn⟩ := hpow _ hσg
  refine ⟨n, fun ζ hζ => ?_⟩
  obtain ⟨k, rfl⟩ := hpow ζ hζ
  rw [map_pow, hn, ← pow_mul, ← pow_mul, mul_comm]

end CyclotomicExponent
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

p2m_open "TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.TensorProduct"

section CancelBaseChange

variable (R S F : Type*) [CommRing R] [CommRing S] [CommRing F] [Algebra R S] [Algebra S F] [Algebra R F]
  [IsScalarTower R S F] (B : Type*) [CommRing B] [Bialgebra R B]

p2m_open_scoped "Algebra Algebra.TensorProduct" in
theorem Algebra.TensorProduct.counit_cancelBaseChange (x : F ⊗[S] (S ⊗[R] B)) :
    CoalgebraStruct.counit (R := F) (Algebra.TensorProduct.cancelBaseChange R S F F B x) =
      CoalgebraStruct.counit (R := F) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul f t =>
      induction t using TensorProduct.induction_on with
      | zero => simp only [tmul_zero, map_zero]
      | tmul s b =>
          rw [Algebra.TensorProduct.cancelBaseChange_tmul]
          simp only [TensorProduct.counit_tmul, CommSemiring.counit_apply]
          exact (smul_assoc _ _ _).symm
      | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

p2m_open_scoped "Algebra Algebra.TensorProduct" in
theorem Algebra.TensorProduct.comul_cancelBaseChange (x : F ⊗[S] (S ⊗[R] B)) :
    CoalgebraStruct.comul (R := F) (Algebra.TensorProduct.cancelBaseChange R S F F B x) =
      _root_.TensorProduct.map (Algebra.TensorProduct.cancelBaseChange R S F F B).toLinearMap
        (Algebra.TensorProduct.cancelBaseChange R S F F B).toLinearMap
        (CoalgebraStruct.comul (R := F) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul f t =>
      induction t using TensorProduct.induction_on with
      | zero => simp only [tmul_zero, map_zero]
      | tmul s b =>
          rw [Algebra.TensorProduct.cancelBaseChange_tmul]
          simp only [TensorProduct.comul_tmul, CommSemiring.comul_apply]
          generalize CoalgebraStruct.comul (R := R) b = z
          induction z using TensorProduct.induction_on with
          | zero => simp only [tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero]
          | tmul b₁ b₂ =>
              simp only [AlgebraTensorModule.tensorTensorTensorComm_tmul, _root_.TensorProduct.map_tmul,
                AlgEquiv.toLinearMap_apply, Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
          | add x y hx hy => simp only [tmul_add, LinearEquiv.map_add, LinearMap.map_add, hx, hy]
      | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

p2m_open_scoped "Algebra Algebra.TensorProduct" in

noncomputable def Algebra.TensorProduct.cancelBaseChangeBialgEquiv :
    F ⊗[S] (S ⊗[R] B) ≃ₐc[F] F ⊗[R] B :=
  BialgEquiv.ofAlgEquiv (Algebra.TensorProduct.cancelBaseChange R S F F B)
    (by
      apply AlgHom.ext
      intro x
      simp only [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply]
      exact Algebra.TensorProduct.counit_cancelBaseChange R S F B x)
    (by
      apply AlgHom.ext
      intro x
      simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
      exact (Algebra.TensorProduct.comul_cancelBaseChange R S F B x).symm)

p2m_open_scoped "Algebra Algebra.TensorProduct" in
@[scoped simp] theorem Algebra.TensorProduct.cancelBaseChangeBialgEquiv_apply (x : F ⊗[S] (S ⊗[R] B)) :
    Algebra.TensorProduct.cancelBaseChangeBialgEquiv R S F B x = Algebra.TensorProduct.cancelBaseChange R S F F B x :=
  rfl

p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"
end CancelBaseChange
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

section GroupLikeMonoidAlgebra

variable (F : Type*) [Field F] (Γ : Type*)

namespace MonoidAlgebra p2m_export "MonoidAlgebra" "lsingle_apply module mapDomainAlgHom of_injective mapDomainBialgHom_apply of mapDomain_single unique mapAlgHom lift_single lift_apply lift mapDomainBialgHom one_def ringHom_ext mapRingHom smul_single' of_apply ring induction_on basis_apply single_pow basis smul_single map semiring mapDomain counit_single single mapDomainAlgHom_apply lift_of mapAlgHom_single ext smul_apply single_apply mapRingHom_apply algHom_ext comul_single sum_single algebra mapRingHom_single mapAlgHom_apply mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg" end MonoidAlgebra
p2m_open_scoped "MonoidAlgebra" in
theorem MonoidAlgebra.isGroupLikeElem_single_one' (g : Γ) : IsGroupLikeElem F (MonoidAlgebra.single g (1 : F)) := by
  rw [isGroupLikeElem_iff]
  constructor
  · rw [MonoidAlgebra.counit_single, CommSemiring.counit_apply]
  · rw [MonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply]

p2m_open_scoped "MonoidAlgebra" in

theorem MonoidAlgebra.isGroupLikeElem_iff_exists_eq_single (x : MonoidAlgebra F Γ) :
    IsGroupLikeElem F x ↔ ∃ g : Γ, x = MonoidAlgebra.single g 1 := by
  constructor
  · intro hx
    by_contra hne
    simp only [not_exists] at hne
    have hli : LinearIndepOn F id {y : MonoidAlgebra F Γ | IsGroupLikeElem F y} := linearIndepOn_isGroupLikeElem
    set s : Set (MonoidAlgebra F Γ) := Set.range fun g : Γ => MonoidAlgebra.single g (1 : F) with hs
    have hxs : x ∉ s := by
      rintro ⟨g, rfl⟩
      exact hne g rfl
    have hsub : insert x s ⊆ {y : MonoidAlgebra F Γ | IsGroupLikeElem F y} := by
      rintro y (rfl | ⟨g, rfl⟩)
      · exact hx
      · exact MonoidAlgebra.isGroupLikeElem_single_one' F Γ g
    have h2 := (linearIndepOn_insert hxs).1 (hli.mono hsub)
    have hspan : Submodule.span F (id '' s) = ⊤ := by
      rw [Set.image_id, hs, show (fun g : Γ => MonoidAlgebra.single g (1 : F)) = ⇑(MonoidAlgebra.basis Γ F) from
        funext fun g => (MonoidAlgebra.basis_apply F g).symm]
      exact (MonoidAlgebra.basis Γ F).span_eq
    exact h2.2 (by rw [hspan]; exact Submodule.mem_top)
  · rintro ⟨g, rfl⟩
    exact MonoidAlgebra.isGroupLikeElem_single_one' F Γ g

end GroupLikeMonoidAlgebra
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

section SpannedByGroupLikes

variable {S : Type*} [CommRing S] {H : Type*} [CommRing H] [Bialgebra S H] {Γ' : Type*} [Monoid Γ']

theorem isGroupLikeElem_symm_single (ψ : H ≃ₐc[S] MonoidAlgebra S Γ') (γ : Γ') :
    IsGroupLikeElem S (ψ.symm (MonoidAlgebra.single γ 1)) := by
  apply IsGroupLikeElem.map ψ.symm
  rw [isGroupLikeElem_iff]
  constructor
  · rw [MonoidAlgebra.counit_single, CommSemiring.counit_apply]
  · rw [MonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply]

theorem span_range_symm_single_eq_top (ψ : H ≃ₐc[S] MonoidAlgebra S Γ') :
    Submodule.span S (Set.range fun γ : Γ' => ψ.symm (MonoidAlgebra.single γ 1)) = ⊤ := by
  have h1 : (Set.range fun γ : Γ' => ψ.symm (MonoidAlgebra.single γ 1))
      = (ψ.symm : MonoidAlgebra S Γ' →ₗ[S] H) '' Set.range (fun γ : Γ' => MonoidAlgebra.single γ (1 : S)) := by
    ext x
    simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and]
    rfl
  rw [h1, Submodule.span_image]
  have h2 : Submodule.span S (Set.range fun γ : Γ' => MonoidAlgebra.single γ (1 : S)) = ⊤ := by
    rw [show (fun γ : Γ' => MonoidAlgebra.single γ (1 : S)) = ⇑(MonoidAlgebra.basis Γ' S) from
      funext fun γ => (MonoidAlgebra.basis_apply S γ).symm]
    exact (MonoidAlgebra.basis Γ' S).span_eq
  rw [h2, Submodule.map_top, LinearMap.range_eq_top]
  exact ψ.symm.surjective

end SpannedByGroupLikes
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

section LocQMain
set_option linter.unusedSectionVars false
p2m_attr_erase "instance" "AddCommGroup.toIntModule LieRing.instLieAlgebra"
p2m_open "GaloisRep~isFractionRing_ratLocalizedAt~isDiscreteValuationRing_ratLocalizedAt P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct"

variable (q : ℕ) [hq : Fact q.Prime] (n : ℕ) [NeZero n] (K : Type) [CommRing K] [HopfAlgebra ℤ K]

local notation "S" => (ratLocalizedAt q)
local notation "G" => Multiplicative (ZMod n)
local notation "V" => MonoidAlgebra ℚ (Multiplicative (ZMod n))
local notation "T" => (ratLocalizedAt q) ⊗[ℤ] K

scoped instance : IsScalarTower ℤ (ratLocalizedAt q) ℚ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

noncomputable def locQGenericEquiv (φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] V) : ℚ ⊗[S] T ≃ₐc[ℚ] V :=
  (Algebra.TensorProduct.cancelBaseChangeBialgEquiv ℤ S ℚ K).trans φ

noncomputable def locQMap (φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] V) : T →ₐ[S] V :=
  restrictBaseChange ℚ (locQGenericEquiv q n K φ : ℚ ⊗[S] T →ₐ[ℚ] V)

omit hq [NeZero n] in
theorem locQMap_tmul (φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] V) (s : S) (k : K) :
    locQMap q n K φ (s ⊗ₜ[ℤ] k) = s • restrictBaseChange ℚ (φ : ℚ ⊗[ℤ] K →ₐ[ℚ] V) k := by
  rw [locQMap, restrictBaseChange_apply, restrictBaseChange_apply]
  change φ (Algebra.TensorProduct.cancelBaseChange ℤ S ℚ ℚ K ((1 : ℚ) ⊗ₜ[S] (s ⊗ₜ[ℤ] k))) = s • φ ((1 : ℚ) ⊗ₜ[ℤ] k)
  rw [Algebra.TensorProduct.cancelBaseChange_tmul]

  rw [show (s • (1 : ℚ)) ⊗ₜ[ℤ] k = s • ((1 : ℚ) ⊗ₜ[ℤ] k) from (TensorProduct.smul_tmul' s (1 : ℚ) k).symm]
  exact (φ : ℚ ⊗[ℤ] K →ₐ[ℚ] V).toLinearMap.map_smul_of_tower s _

theorem range_locQMap (φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] V) :
    LinearMap.range (locQMap q n K φ).toLinearMap =
      Submodule.span S (Set.range (restrictBaseChange ℚ (φ : ℚ ⊗[ℤ] K →ₐ[ℚ] V))) := by
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]; exact zero_mem _
    | tmul s k =>
        rw [AlgHom.toLinearMap_apply, locQMap_tmul]
        exact Submodule.smul_mem _ s (Submodule.subset_span ⟨k, rfl⟩)
    | add x y hx hy =>
        rw [AlgHom.toLinearMap_apply, map_add]
        exact add_mem hx hy
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine ⟨(1 : S) ⊗ₜ[ℤ] k, ?_⟩
    rw [AlgHom.toLinearMap_apply, locQMap_tmul, one_smul]

variable [Module.Flat ℤ K]

omit [NeZero n] in
theorem locQMap_injective (φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] V) : Function.Injective (locQMap q n K φ) :=
  restrictBaseChange_injective (nonZeroDivisors S) ℚ le_rfl _ (locQGenericEquiv q n K φ).injective

omit hq [NeZero n] [Module.Flat ℤ K] in
theorem isGroupLikeElem_locQMap {φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] V} {t : T} (ht : IsGroupLikeElem S t) :
    IsGroupLikeElem ℚ (locQMap q n K φ t) :=
  IsGroupLikeElem.restrictBaseChange ℚ (locQGenericEquiv q n K φ : ℚ ⊗[S] T →ₐc[ℚ] V) ht

theorem span_range_restrictBaseChange_eq_span_range_of
    (φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] V)
    (ψ : T ≃ₐc[S] MonoidAlgebra (ratLocalizedAt q) (Multiplicative (ZMod n))) :
    Submodule.span S (Set.range (restrictBaseChange ℚ (φ : ℚ ⊗[ℤ] K →ₐ[ℚ] V)))
      = Submodule.span S (Set.range (MonoidAlgebra.of ℚ (Multiplicative (ZMod n)))) := by
  classical

  set u : G → T := fun γ => ψ.symm (MonoidAlgebra.single γ 1) with hu
  have hu_gl : ∀ γ, IsGroupLikeElem S (u γ) := fun γ => isGroupLikeElem_symm_single ψ γ
  have hu_span : Submodule.span S (Set.range u) = ⊤ := span_range_symm_single_eq_top ψ

  have hex : ∀ γ, ∃ g : G, locQMap q n K φ (u γ) = MonoidAlgebra.single g 1 := fun γ =>
    (MonoidAlgebra.isGroupLikeElem_iff_exists_eq_single ℚ G _).1 (isGroupLikeElem_locQMap q n K (hu_gl γ))
  choose g hg using hex

  have hginj : Function.Injective g := by
    intro γ₁ γ₂ h
    have h1 : locQMap q n K φ (u γ₁) = locQMap q n K φ (u γ₂) := by rw [hg, hg, h]
    have h2 := ψ.symm.injective (locQMap_injective q n K φ h1)
    exact MonoidAlgebra.single_left_injective one_ne_zero h2
  have hgbij : Function.Bijective g := Finite.injective_iff_bijective.1 hginj

  rw [← range_locQMap, LinearMap.range_eq_map, ← hu_span, Submodule.map_span, ← Set.range_comp]
  congr 1
  ext v
  simp only [Set.mem_range, Function.comp_apply, AlgHom.toLinearMap_apply, MonoidAlgebra.of_apply]
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨g γ, (hg γ).symm⟩
  · rintro ⟨g', rfl⟩
    obtain ⟨γ, rfl⟩ := hgbij.2 g'
    exact ⟨γ, hg γ⟩

end LocQMain
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

section PointsTransportLoc
p2m_attr_erase "instance" "AddCommGroup.toIntModule LieRing.instLieAlgebra"
p2m_open "GaloisRep~isFractionRing_ratLocalizedAt~isDiscreteValuationRing_ratLocalizedAt P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct"

variable (ℓ : ℕ) (K : Type) [CommRing K] [HopfAlgebra ℤ K]

local notation "S" => (ratLocalizedAt ℓ)
local notation "Ω" => AlgebraicClosure ℚ
local notation "T" => (ratLocalizedAt ℓ) ⊗[ℤ] K

scoped instance instIsScalarTowerIntRatLocAlgClosure :
    @IsScalarTower ℤ (ratLocalizedAt ℓ) (AlgebraicClosure ℚ) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

theorem natCard_algHom_baseChange_ratLocalizedAt (n : ℕ) (hgenq : Nat.card (K →ₐ[ℤ] Ω) = n) :
    Nat.card (T →ₐ[S] Ω) = n := by
  rw [Nat.card_congr (Algebra.TensorProduct.pointsEquiv ℤ S K Ω), hgenq]

omit [HopfAlgebra ℤ K] in

theorem ringEquiv_apply_algebraMap_ratLocalizedAt (σ : Ω ≃+* Ω) (s : S) :
    σ (algebraMap S Ω s) = algebraMap S Ω s := by
  have h : ((σ : Ω →+* Ω).comp (algebraMap ℚ Ω)) = algebraMap ℚ Ω := Subsingleton.elim _ _
  exact RingHom.congr_fun h (s : ℚ)

theorem galois_convPow_baseChange_ratLocalizedAt (q : ℕ)
    (hgal : ∀ (σ : Ω ≃+* Ω) (nσ : ℕ), (∀ ζ : Ω, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : K →ₐ[ℤ] Ω) (k : K), σ (ψ k) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) k)
    (σ : Ω ≃+* Ω) (nσ : ℕ) (hσ : ∀ ζ : Ω, ζ ^ q = 1 → σ ζ = ζ ^ nσ)
    (ψ : T →ₐ[S] Ω) (t : T) :
    σ (ψ t) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) t := by
  have hK : ∀ k : K, σ (ψ ((1 : S) ⊗ₜ[ℤ] k)) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) ((1 : S) ⊗ₜ[ℤ] k) := by
    intro k
    have h1 := hgal σ nσ hσ (Algebra.TensorProduct.pointsEquiv ℤ S K Ω ψ) k
    rw [Algebra.TensorProduct.pointsEquiv_apply] at h1
    rw [h1]
    have h2 : WithConv.toConv (Algebra.TensorProduct.pointsEquiv ℤ S K Ω ψ)
        = Algebra.TensorProduct.pointsMulEquiv ℤ S K Ω (WithConv.toConv ψ) := rfl
    rw [h2, ← map_pow, Algebra.TensorProduct.pointsMulEquiv_apply, WithConv.ofConv_toConv]
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s k =>
      have hs : s ⊗ₜ[ℤ] k = s • ((1 : S) ⊗ₜ[ℤ] k) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hs, map_smul ψ s, map_smul (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) s, Algebra.smul_def,
        Algebra.smul_def, map_mul σ, ringEquiv_apply_algebraMap_ratLocalizedAt, hK]
  | add x y hx hy => simp only [map_add, hx, hy]

end PointsTransportLoc
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

section PointsTransportRat
p2m_attr_erase "instance" "AddCommGroup.toIntModule LieRing.instLieAlgebra"
p2m_open "Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct"

variable (K : Type) [CommRing K] [HopfAlgebra ℤ K]

local notation "Ω" => AlgebraicClosure ℚ

scoped instance instIsScalarTowerIntRatAlgClosure :
    @IsScalarTower ℤ ℚ (AlgebraicClosure ℚ) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

theorem natCard_algHom_baseChange_rat (n : ℕ) (hgenq : Nat.card (K →ₐ[ℤ] Ω) = n) :
    Nat.card (ℚ ⊗[ℤ] K →ₐ[ℚ] Ω) = n := by
  rw [Nat.card_congr (Algebra.TensorProduct.pointsEquiv ℤ ℚ K Ω), hgenq]

omit [HopfAlgebra ℤ K] in
theorem ringEquiv_apply_algebraMap_rat (σ : Ω ≃+* Ω) (r : ℚ) : σ (algebraMap ℚ Ω r) = algebraMap ℚ Ω r := by
  have h : ((σ : Ω →+* Ω).comp (algebraMap ℚ Ω)) = algebraMap ℚ Ω := Subsingleton.elim _ _
  exact RingHom.congr_fun h r

theorem galois_convPow_baseChange_rat (q : ℕ)
    (hgal : ∀ (σ : Ω ≃+* Ω) (nσ : ℕ), (∀ ζ : Ω, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : K →ₐ[ℤ] Ω) (k : K), σ (ψ k) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) k)
    (σ : Ω ≃+* Ω) (nσ : ℕ) (hσ : ∀ ζ : Ω, ζ ^ q = 1 → σ ζ = ζ ^ nσ)
    (ψ : ℚ ⊗[ℤ] K →ₐ[ℚ] Ω) (t : ℚ ⊗[ℤ] K) :
    σ (ψ t) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) t := by
  have hK : ∀ k : K, σ (ψ ((1 : ℚ) ⊗ₜ[ℤ] k)) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) ((1 : ℚ) ⊗ₜ[ℤ] k) := by
    intro k
    have h1 := hgal σ nσ hσ (Algebra.TensorProduct.pointsEquiv ℤ ℚ K Ω ψ) k
    rw [Algebra.TensorProduct.pointsEquiv_apply] at h1
    rw [h1]
    have h2 : WithConv.toConv (Algebra.TensorProduct.pointsEquiv ℤ ℚ K Ω ψ)
        = Algebra.TensorProduct.pointsMulEquiv ℤ ℚ K Ω (WithConv.toConv ψ) := rfl
    rw [h2, ← map_pow, Algebra.TensorProduct.pointsMulEquiv_apply, WithConv.ofConv_toConv]
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s k =>
      have hs : s ⊗ₜ[ℤ] k = s • ((1 : ℚ) ⊗ₜ[ℤ] k) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hs, map_smul ψ s, map_smul (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) s, Algebra.smul_def,
        Algebra.smul_def, map_mul σ, ringEquiv_apply_algebraMap_rat, hK]
  | add x y hx hy => simp only [map_add, hx, hy]

end PointsTransportRat
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

section NotFG
p2m_attr_erase "instance" "AddCommGroup.toIntModule LieRing.instLieAlgebra"
p2m_open "GaloisRep~isFractionRing_ratLocalizedAt~isDiscreteValuationRing_ratLocalizedAt P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct"

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) [NeZero n] (K : Type) [CommRing K] [HopfAlgebra ℤ K]
  [Algebra.FiniteType ℤ K] [Module.Flat ℤ K]

omit [Algebra.FiniteType ℤ K] in

theorem finite_baseChange_of_fg_span_range
    (φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod n)))
    (hfg : (Submodule.span (ratLocalizedAt p)
      (Set.range (restrictBaseChange ℚ (φ : ℚ ⊗[ℤ] K →ₐ[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod n)))))).FG) :
    Module.Finite (ratLocalizedAt p) ((ratLocalizedAt p) ⊗[ℤ] K) := by
  rw [← range_locQMap] at hfg
  haveI : Module.Finite (ratLocalizedAt p) (LinearMap.range (locQMap p n K φ).toLinearMap) :=
    Module.Finite.iff_fg.2 hfg
  exact Module.Finite.equiv
    (LinearEquiv.ofInjective (locQMap p n K φ).toLinearMap (locQMap_injective p n K φ)).symm

theorem not_fg_span_range_of_not_finite
    (hff' : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → Module.Finite (ratLocalizedAt ℓ) ((ratLocalizedAt ℓ) ⊗[ℤ] K))
    (hK' : ¬ Module.Finite ℤ K)
    (φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod n))) :
    ¬ (Submodule.span (ratLocalizedAt p)
      (Set.range (restrictBaseChange ℚ (φ : ℚ ⊗[ℤ] K →ₐ[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod n)))))).FG := by
  intro hfg
  apply hK'
  have hp' := finite_baseChange_of_fg_span_range p n K φ hfg
  refine Module.Finite.of_finite_baseChange_ratLocalizedAt K fun ℓ hℓ => ?_
  by_cases h : ℓ = p
  · subst h
    exact hp'
  · exact hff' ℓ hℓ h

end NotFG
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

section LocQLeg
p2m_attr_erase "instance" "AddCommGroup.toIntModule LieRing.instLieAlgebra"
p2m_open "GaloisRep~isFractionRing_ratLocalizedAt~isDiscreteValuationRing_ratLocalizedAt P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct"

theorem span_range_restrictBaseChange_eq_span_range_of_face
    (q : ℕ) [Fact q.Prime] (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Module.Flat ℤ K]
    [Module.Finite (ratLocalizedAt q) ((ratLocalizedAt q) ⊗[ℤ] K)]
    (φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod q)))
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ) (k : K), σ (ψ k) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) k)
    (face : ∀ (H : Type) [CommRing H] [HopfAlgebra (ratLocalizedAt q) H]
      [Module.Finite (ratLocalizedAt q) H] [Module.Flat (ratLocalizedAt q) H],
      Nat.card (H →ₐ[ratLocalizedAt q] AlgebraicClosure ℚ) = q →
      (∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
        ∀ (ψ : H →ₐ[ratLocalizedAt q] AlgebraicClosure ℚ) (h : H),
          σ (ψ h) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) h) →
      Nonempty (H ≃ₐc[ratLocalizedAt q] MonoidAlgebra (ratLocalizedAt q) (Multiplicative (ZMod q)))) :
    Submodule.span (ratLocalizedAt q)
        (Set.range (restrictBaseChange ℚ (φ : ℚ ⊗[ℤ] K →ₐ[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod q)))))
      = Submodule.span (ratLocalizedAt q) (Set.range (MonoidAlgebra.of ℚ (Multiplicative (ZMod q)))) := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨ψ⟩ := face ((ratLocalizedAt q) ⊗[ℤ] K)
    (natCard_algHom_baseChange_ratLocalizedAt q K q hgenq)
    (fun σ nσ hσ ψ t => galois_convPow_baseChange_ratLocalizedAt q K q hgal σ nσ hσ ψ t)
  exact span_range_restrictBaseChange_eq_span_range_of q q K φ ψ

end LocQLeg
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

section GenMuLeg
p2m_attr_erase "instance" "AddCommGroup.toIntModule LieRing.instLieAlgebra"
p2m_open "Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct"

theorem nonempty_bialgEquiv_rat_baseChange_of_face
    (q : ℕ) [Fact q.Prime] (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K] [Module.Flat ℤ K]
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ) (k : K), σ (ψ k) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) k)
    (face : ∀ (A : Type) [CommRing A] [HopfAlgebra ℚ A] [Module.Finite ℚ A],
      Nat.card (A →ₐ[ℚ] AlgebraicClosure ℚ) = q →
      (∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
        ∀ (ψ : A →ₐ[ℚ] AlgebraicClosure ℚ) (a : A), σ (ψ a) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) a) →
      Nonempty (A ≃ₐc[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod q)))) :
    Nonempty (ℚ ⊗[ℤ] K ≃ₐc[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod q))) := by
  have hcard := natCard_algHom_baseChange_rat K q hgenq
  haveI : Finite (ℚ ⊗[ℤ] K →ₐ[ℚ] AlgebraicClosure ℚ) :=
    Nat.finite_of_card_ne_zero (hcard ▸ (Fact.out : q.Prime).ne_zero)
  haveI : Module.Finite ℚ (ℚ ⊗[ℤ] K) :=
    Module.Finite.of_finite_algHom_of_isAlgClosed ℚ (ℚ ⊗[ℤ] K) (AlgebraicClosure ℚ)
  exact face (ℚ ⊗[ℤ] K) hcard (fun σ nσ hσ ψ a => galois_convPow_baseChange_rat K q hgal σ nσ hσ ψ a)

end GenMuLeg
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

section LocRange
set_option linter.unusedSectionVars false
p2m_attr_erase "instance" "AddCommGroup.toIntModule LieRing.instLieAlgebra"
p2m_open "GaloisRep~isFractionRing_ratLocalizedAt~isDiscreteValuationRing_ratLocalizedAt P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct"

variable (q : ℕ) [hq : Fact q.Prime] (n : ℕ) [NeZero n] (K : Type) [CommRing K] [HopfAlgebra ℤ K]

local notation "S" => (ratLocalizedAt q)
local notation "V" => MonoidAlgebra ℚ (Multiplicative (ZMod n))
local notation "T" => (ratLocalizedAt q) ⊗[ℤ] K

noncomputable def locQRange (φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] V) : Subalgebra S V := (locQMap q n K φ).range

theorem coe_locQRange (φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] V) : (locQRange q n K φ : Set V) = Set.range (locQMap q n K φ) :=
  AlgHom.coe_range _

theorem locQRange_toSubmodule (φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] V) :
    Subalgebra.toSubmodule (locQRange q n K φ) =
      Submodule.span S (Set.range (restrictBaseChange ℚ (φ : ℚ ⊗[ℤ] K →ₐ[ℚ] V))) := by
  rw [← range_locQMap]
  exact Submodule.toSubMulAction_inj.mp rfl

noncomputable def locQAlgEquiv [Module.Flat ℤ K] (φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] V) : T ≃ₐ[S] locQRange q n K φ :=
  AlgEquiv.ofInjective (locQMap q n K φ) (locQMap_injective q n K φ)

@[scoped simp] theorem locQAlgEquiv_apply [Module.Flat ℤ K] (φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] V) (t : T) :
    (locQAlgEquiv q n K φ t : V) = locQMap q n K φ t := rfl

theorem finite_locQRange [Module.Flat ℤ K] [Module.Finite S T] (φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] V) :
    Module.Finite S (locQRange q n K φ) :=
  Module.Finite.equiv (locQAlgEquiv q n K φ).toLinearEquiv

theorem span_rat_coe_locQRange_eq_top (φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] V) :
    Submodule.span ℚ (locQRange q n K φ : Set V) = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  have hsurj : Function.Surjective (locQGenericEquiv q n K φ) := (locQGenericEquiv q n K φ).toEquiv.surjective
  obtain ⟨x, rfl⟩ := hsurj v
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul r t =>
      have : r ⊗ₜ[S] t = r • ((1 : ℚ) ⊗ₜ[S] t) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this, map_smul]
      refine Submodule.smul_mem _ r (Submodule.subset_span ?_)
      rw [coe_locQRange]
      exact ⟨t, rfl⟩
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

end LocRange
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

section NORM
p2m_open "MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra"

variable (R : Type) [CommRing R] (G : Type) [Group G] [Fintype G]

p2m_open_scoped "MonoidAlgebra" in

noncomputable def MonoidAlgebra.normElem : MonoidAlgebra R G := ∑ g : G, MonoidAlgebra.of R G g

p2m_open_scoped "MonoidAlgebra" in
theorem MonoidAlgebra.of_mul_normElem (g : G) :
    MonoidAlgebra.of R G g * MonoidAlgebra.normElem R G = MonoidAlgebra.normElem R G := by
  classical
  unfold MonoidAlgebra.normElem
  rw [Finset.mul_sum]
  simp_rw [← map_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun h => rfl)

p2m_open_scoped "MonoidAlgebra" in
theorem MonoidAlgebra.single_mul_normElem (g : G) (r : R) :
    MonoidAlgebra.single g r * MonoidAlgebra.normElem R G = r • MonoidAlgebra.normElem R G := by
  classical
  have : MonoidAlgebra.single g r = r • MonoidAlgebra.of R G g := by
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
  rw [this, smul_mul_assoc, MonoidAlgebra.of_mul_normElem]

p2m_open_scoped "MonoidAlgebra" in

theorem MonoidAlgebra.mul_normElem_eq_counit_smul (x : MonoidAlgebra R G) :
    x * MonoidAlgebra.normElem R G = (Coalgebra.counit (R := R) x) • MonoidAlgebra.normElem R G := by
  classical
  induction x using MonoidAlgebra.induction_on with
  | of g => rw [MonoidAlgebra.of_mul_normElem, MonoidAlgebra.of_apply, MonoidAlgebra.counit_single,
      CommSemiring.counit_apply, one_smul]
  | add x y hx hy => rw [add_mul, hx, hy, map_add, add_smul]
  | smul r x hx => rw [smul_mul_assoc, hx, map_smul, smul_eq_mul, mul_smul]

p2m_open_scoped "MonoidAlgebra" in
theorem MonoidAlgebra.counit_normElem :
    Coalgebra.counit (R := R) (MonoidAlgebra.normElem R G) = Fintype.card G := by
  classical
  unfold MonoidAlgebra.normElem
  rw [map_sum]
  simp [MonoidAlgebra.of_apply, MonoidAlgebra.counit_single]

p2m_open_scoped "MonoidAlgebra" in
theorem MonoidAlgebra.normElem_mul_normElem :
    MonoidAlgebra.normElem R G * MonoidAlgebra.normElem R G = (Fintype.card G : R) • MonoidAlgebra.normElem R G := by
  rw [MonoidAlgebra.mul_normElem_eq_counit_smul, MonoidAlgebra.counit_normElem]

p2m_open_scoped "MonoidAlgebra" in
theorem MonoidAlgebra.normElem_mul_of (g : G) :
    MonoidAlgebra.normElem R G * MonoidAlgebra.of R G g = MonoidAlgebra.normElem R G := by
  classical
  unfold MonoidAlgebra.normElem
  rw [Finset.sum_mul]
  simp_rw [← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun h => rfl)

p2m_open_scoped "MonoidAlgebra" in

theorem MonoidAlgebra.normElem_mul_eq_counit_smul (x : MonoidAlgebra R G) :
    MonoidAlgebra.normElem R G * x = (Coalgebra.counit (R := R) x) • MonoidAlgebra.normElem R G := by
  classical
  induction x using MonoidAlgebra.induction_on with
  | of g => rw [MonoidAlgebra.normElem_mul_of, MonoidAlgebra.of_apply, MonoidAlgebra.counit_single,
      CommSemiring.counit_apply, one_smul]
  | add x y hx hy => rw [mul_add, hx, hy, map_add, add_smul]
  | smul r x hx => rw [mul_smul_comm, hx, map_smul, smul_eq_mul, mul_smul]

p2m_open_scoped "MonoidAlgebra" in

theorem MonoidAlgebra.normElem_mul_sub_algebraMap_counit (x : MonoidAlgebra R G) :
    MonoidAlgebra.normElem R G * (x - algebraMap R (MonoidAlgebra R G) (Coalgebra.counit (R := R) x)) = 0 := by
  rw [mul_sub, MonoidAlgebra.normElem_mul_eq_counit_smul, ← Algebra.commutes, ← Algebra.smul_def, sub_self]

p2m_open_scoped "MonoidAlgebra" in
theorem MonoidAlgebra.sub_algebraMap_counit_mul_normElem (x : MonoidAlgebra R G) :
    (x - algebraMap R (MonoidAlgebra R G) (Coalgebra.counit (R := R) x)) * MonoidAlgebra.normElem R G = 0 := by
  rw [sub_mul, MonoidAlgebra.mul_normElem_eq_counit_smul, ← Algebra.smul_def, sub_self]

#print axioms MonoidAlgebra.normElem_mul_sub_algebraMap_counit
end NORM
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

section ETP_ADAMS
p2m_open "MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra"

variable (q : ℕ)

noncomputable abbrev adamsOp (a : ℕ) :
    MonoidAlgebra ℚ (Multiplicative (ZMod q)) →ₐ[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod q)) :=
  MonoidAlgebra.mapDomainAlgHom ℚ ℚ (powMonoidHom a)

theorem adamsOp_single (a : ℕ) (g : Multiplicative (ZMod q)) (r : ℚ) :
    adamsOp q a (single g r) = single (g ^ a) r := by
  rw [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single, powMonoidHom_apply]

theorem pow_eq_ofAdd_mul_toAdd (g : Multiplicative (ZMod q)) (n : ℕ) :
    g ^ n = Multiplicative.ofAdd ((n : ZMod q) * Multiplicative.toAdd g) := by
  conv_lhs => rw [← ofAdd_toAdd g]
  rw [← ofAdd_nsmul, nsmul_eq_mul]

theorem pow_val_bijective [NeZero q] (c : (ZMod q)ˣ) :
    Function.Bijective (fun g : Multiplicative (ZMod q) => g ^ (c : ZMod q).val) := by
  have h : (fun g : Multiplicative (ZMod q) => g ^ (c : ZMod q).val) =
      fun g => Multiplicative.ofAdd ((c : ZMod q) * Multiplicative.toAdd g) := by
    funext g; rw [pow_eq_ofAdd_mul_toAdd, ZMod.natCast_zmod_val]
  rw [h]
  exact (Multiplicative.ofAdd.bijective.comp (Units.mulLeft c).bijective).comp Multiplicative.toAdd.bijective

theorem exists_unit_pow_val_eq [Fact q.Prime] {g h : Multiplicative (ZMod q)} (hg : g ≠ 1) (hh : h ≠ 1) :
    ∃ c : (ZMod q)ˣ, g ^ (c : ZMod q).val = h := by
  have hg' : Multiplicative.toAdd g ≠ 0 := fun e => hg (by simpa using congrArg Multiplicative.ofAdd e)
  have hh' : Multiplicative.toAdd h ≠ 0 := fun e => hh (by simpa using congrArg Multiplicative.ofAdd e)
  refine ⟨Units.mk0 (Multiplicative.toAdd h * (Multiplicative.toAdd g)⁻¹) (mul_ne_zero hh' (inv_ne_zero hg')), ?_⟩
  rw [pow_eq_ofAdd_mul_toAdd, ZMod.natCast_zmod_val, Units.val_mk0, inv_mul_cancel_right₀ hg', ofAdd_toAdd]

theorem apply_pow_eq_of_adamsOp_eq [NeZero q] (c : (ZMod q)ˣ) (v : MonoidAlgebra ℚ (Multiplicative (ZMod q)))
    (hv : adamsOp q (c : ZMod q).val v = v) (g : Multiplicative (ZMod q)) :
    v.coeff (g ^ (c : ZMod q).val) = v.coeff g := by
  conv_lhs => rw [← hv]
  rw [MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain, MonoidAlgebra.coeff_ofCoeff]
  exact Finsupp.mapDomain_apply (f := fun g : Multiplicative (ZMod q) => g ^ (c : ZMod q).val)
    (pow_val_bijective q c).1 v.coeff g

theorem normElem_apply [NeZero q] (g : Multiplicative (ZMod q)) :
    (MonoidAlgebra.normElem ℚ (Multiplicative (ZMod q))).coeff g = 1 := by
  classical
  unfold MonoidAlgebra.normElem
  rw [MonoidAlgebra.coeff_sum, Finset.sum_apply']
  simp_rw [MonoidAlgebra.of_apply]
  simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem exists_eq_algebraMap_add_smul_normElem_of_forall_adamsOp_eq [hq : Fact q.Prime]
    (v : MonoidAlgebra ℚ (Multiplicative (ZMod q)))
    (hv : ∀ c : (ZMod q)ˣ, adamsOp q (c : ZMod q).val v = v) :
    ∃ α β : ℚ, v = algebraMap ℚ _ α + β • MonoidAlgebra.normElem ℚ (Multiplicative (ZMod q)) := by
  classical
  haveI : Fact (1 < q) := ⟨hq.out.one_lt⟩
  have hq1 : (Multiplicative.ofAdd (1 : ZMod q)) ≠ (1 : Multiplicative (ZMod q)) := by
    intro e
    have := congrArg Multiplicative.toAdd e
    simp only [toAdd_ofAdd, toAdd_one] at this
    exact one_ne_zero this
  refine ⟨v.coeff 1 - v.coeff (Multiplicative.ofAdd 1), v.coeff (Multiplicative.ofAdd 1), ?_⟩
  refine MonoidAlgebra.ext (Finsupp.ext fun g => ?_)
  simp only [Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def, MonoidAlgebra.smul_single', smul_eq_mul, mul_one]
  rw [MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_single, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.single_apply]
  rw [normElem_apply, smul_eq_mul, mul_one]
  by_cases hg : g = 1
  · subst hg
    rw [if_pos rfl, sub_add_cancel]
  · obtain ⟨c, hc⟩ := exists_unit_pow_val_eq q hq1 hg
    have := apply_pow_eq_of_adamsOp_eq q c v (hv c) (Multiplicative.ofAdd 1)
    rw [hc] at this
    rw [this, if_neg (Ne.symm hg), zero_add]

end ETP_ADAMS
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

section LATTICE_KIT

namespace Submodule p2m_export "Submodule" "span_eq inclusion map_top closure_le mk smul_mem torsion IsPrincipal Quotient.mk span restrictScalars coe_restrictScalars mem_sInf span_le toAddSubgroup mem_top mem_span_singleton IsPrincipal.span_singleton_generator mem_map mul span_image baseChange zero map_span map mapAlgHom smul_of_tower_mem subset_span module smul_def FG ext add comap toSubMulAction_inj span_induction smul mem_of_forall_prime_exists_smul_mem mem_span_ratLocalizedAt_iff" end Submodule
p2m_open_scoped "Submodule" in

theorem Submodule.mem_of_mem_of_mem_span_ratLocalizedAt_of_forall_ne_span_eq
    {V : Type*} [AddCommGroup V] [Module ℚ V] (M N : Submodule ℤ V) (p : ℕ) (hp : p.Prime)
    (hloc : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Submodule.span (GaloisRep.ratLocalizedAt ℓ) (M : Set V) =
        Submodule.span (GaloisRep.ratLocalizedAt ℓ) (N : Set V))
    (x : V) (hxN : x ∈ N) (hxp : x ∈ Submodule.span (GaloisRep.ratLocalizedAt p) (M : Set V)) :
    x ∈ M := by
  refine Submodule.mem_of_forall_prime_exists_smul_mem M x fun ℓ hℓ => ?_
  by_cases hℓp : ℓ = p
  · subst hℓp
    exact (Submodule.mem_span_ratLocalizedAt_iff M ℓ hℓ x).1 hxp
  · refine (Submodule.mem_span_ratLocalizedAt_iff M ℓ hℓ x).1 ?_
    rw [hloc ℓ hℓ hℓp]
    exact Submodule.subset_span hxN

namespace Submodule
p2m_open_scoped "Submodule" in

private theorem _root_.Submodule.exists_pow_smul_mem_of_forall_ne_span_eq
    {V : Type*} [AddCommGroup V] [Module ℚ V] (M N : Submodule ℤ V) (p : ℕ) (hp : p.Prime)
    (hloc : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Submodule.span (GaloisRep.ratLocalizedAt ℓ) (M : Set V) =
        Submodule.span (GaloisRep.ratLocalizedAt ℓ) (N : Set V))
    (hN : ∀ v : V, ∃ d : ℤ, d ≠ 0 ∧ d • v ∈ N)
    (x : V) (hxM : x ∈ M) : ∃ n : ℕ, ((p : ℤ) ^ n) • x ∈ N := by
  obtain ⟨d, hd0, hdx⟩ := hN x

  obtain ⟨n, s, hs, hds⟩ : ∃ (n : ℕ) (s : ℤ), ¬ (p : ℤ) ∣ s ∧ d = (p : ℤ) ^ n * s := by
    obtain ⟨e, n', hn', he⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hd0) p hp.one_lt.ne'
    refine ⟨e, d.sign * n', fun h => hn' ?_, ?_⟩
    · rw [Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hd0, one_mul, Int.natAbs_natCast] at h
      exact h
    · calc d = d.sign * (d.natAbs : ℤ) := (Int.sign_mul_natAbs d).symm
        _ = d.sign * (((p ^ e * n' : ℕ)) : ℤ) := by rw [he]
        _ = (p : ℤ) ^ e * (d.sign * n') := by push_cast; ring
  refine ⟨n, Submodule.mem_of_forall_prime_exists_smul_mem N _ fun ℓ hℓ => ?_⟩
  by_cases hℓp : ℓ = p
  · subst hℓp
    refine ⟨s, hs, ?_⟩
    rw [smul_smul, mul_comm, ← hds]
    exact hdx
  ·
    have hx : ((p : ℤ) ^ n) • x ∈ Submodule.span (GaloisRep.ratLocalizedAt ℓ) (N : Set V) := by
      rw [← hloc ℓ hℓ hℓp]
      exact Submodule.smul_of_tower_mem _ ((p : ℤ) ^ n) (Submodule.subset_span hxM)
    exact (Submodule.mem_span_ratLocalizedAt_iff N ℓ hℓ _).1 hx

end Submodule
p2m_export "" "Submodule.exists_pow_smul_mem_of_forall_ne_span_eq"
end LATTICE_KIT
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

section BRIDGE
p2m_open "GaloisRep~isFractionRing_ratLocalizedAt~isDiscreteValuationRing_ratLocalizedAt P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep"

namespace AddSubgroup p2m_export "AddSubgroup" "closure_le mem_top closure add FG mem_sInf subset_closure zero mk ext map index comap inclusion toIntSubmodule zsmul mem_map" end AddSubgroup
p2m_open_scoped "AddSubgroup" in

theorem AddSubgroup.mem_of_forall_prime_mem_span_ratLocalizedAt
    {V : Type*} [AddCommGroup V] [Module ℚ V] (M : AddSubgroup V) (x : V)
    (h : ∀ ℓ : ℕ, ℓ.Prime → x ∈ Submodule.span (ratLocalizedAt ℓ) (M : Set V)) : x ∈ M := by
  have := Submodule.mem_of_forall_prime_exists_smul_mem M.toIntSubmodule x fun ℓ hℓ =>
    (Submodule.mem_span_ratLocalizedAt_iff M.toIntSubmodule ℓ hℓ x).1 (by simpa using h ℓ hℓ)
  first | exact this | simpa using this

namespace AddSubgroup
p2m_open_scoped "AddSubgroup" in

private theorem _root_.AddSubgroup.exists_pow_smul_mem_of_forall_ne_span_eq
    {V : Type*} [AddCommGroup V] [Module ℚ V] (M N : AddSubgroup V) (p : ℕ) (hp : p.Prime)
    (hloc : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Submodule.span (ratLocalizedAt ℓ) (M : Set V) = Submodule.span (ratLocalizedAt ℓ) (N : Set V))
    (hN : ∀ v : V, ∃ d : ℤ, d ≠ 0 ∧ (d : ℚ) • v ∈ N)
    (x : V) (hxM : x ∈ M) : ∃ n : ℕ, ((p : ℚ) ^ n) • x ∈ N := by
  have hN' : ∀ v : V, ∃ d : ℤ, d ≠ 0 ∧ d • v ∈ N.toIntSubmodule := fun v => by
    obtain ⟨d, hd, h⟩ := hN v
    exact ⟨d, hd, by rw [Int.cast_smul_eq_zsmul] at h; exact h⟩
  obtain ⟨n, hn⟩ := Submodule.exists_pow_smul_mem_of_forall_ne_span_eq M.toIntSubmodule N.toIntSubmodule p hp
    (by simpa using hloc) hN' x hxM
  refine ⟨n, ?_⟩
  have : ((p : ℚ) ^ n) • x = ((p : ℤ) ^ n) • x := by
    rw [← Int.cast_smul_eq_zsmul ℚ]; push_cast; rfl
  rw [this]
  exact hn

end AddSubgroup
p2m_export "" "AddSubgroup.exists_pow_smul_mem_of_forall_ne_span_eq"
p2m_open_scoped "AddSubgroup" in

theorem AddSubgroup.exists_zsmul_mem_of_span_eq_top
    {V : Type*} [AddCommGroup V] [Module ℚ V] (N : AddSubgroup V)
    (hN : Submodule.span ℚ (N : Set V) = ⊤) (v : V) : ∃ d : ℤ, d ≠ 0 ∧ (d : ℚ) • v ∈ N := by
  simp_rw [Int.cast_smul_eq_zsmul ℚ]
  have hv : v ∈ Submodule.span ℚ (N : Set V) := by rw [hN]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.zsmul_mem h₁ d₂
    · rw [mul_smul]; exact N.zsmul_mem h₂ d₁
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    refine ⟨c.den * d, mul_ne_zero (by exact_mod_cast c.den_ne_zero) hd, ?_⟩
    have : ((c.den : ℤ) * d) • c • x = c.num • (d • x) := by
      rw [mul_comm, mul_smul, ← Int.cast_smul_eq_zsmul ℚ (c.den : ℤ), smul_smul, Int.cast_natCast,
        Rat.den_mul_eq_num, Int.cast_smul_eq_zsmul, smul_comm]
    rw [this]
    exact N.zsmul_mem h c.num

end BRIDGE
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

namespace Module p2m_export "Module" "Flat Injective equiv Finite.equiv finrank Free finite_iff_isArtinianRing mk ext' Finite.of_injective free_of_finite_type_torsion_free' Finite.iff_fg restrictScalars finrank_baseChange Flat.isSMulRegular_of_nonZeroDivisors jacobson IsPrincipal Finite.of_exists_smul_isIntegral_maximal Finite.of_finite_baseChange_localization_maximal Finite.of_finite_algHom_of_isAlgClosed Finite.rat_baseChange_of_finite_algHom" namespace Flat p2m_export "Module.Flat" "out toAlgebra self trans baseChange isSMulRegular_of_nonZeroDivisors mk" end Module.Flat
namespace Module.Flat
p2m_open_scoped "Module Module.Flat" in

private theorem _root_.Module.Flat.of_intModule_eq (K : Type*) [AddCommGroup K] (i₁ i₂ : Module ℤ K)
    (h : @Module.Flat ℤ K _ _ i₁) : @Module.Flat ℤ K _ _ i₂ := by
  cases Subsingleton.elim i₁ i₂; exact h

end Module.Flat
p2m_export "" "Module.Flat.of_intModule_eq"
namespace HopfAlgebra
p2m_export "HopfAlgebra" "mk ofAlgHom nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_ratLocalizedAt_eq_of_convPow_of_ne_two etale_of_pow_eq_one_of_isUnit_of_finite convPow_natCard_algHom_algebraicClosure_eq_one"
namespace LocEt
p2m_open "HopfAlgebra"
p2m_open "GaloisRep~isFractionRing_ratLocalizedAt~isDiscreteValuationRing_ratLocalizedAt P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep WithConv"

section GroupAlgebra
variable (R : Type*) [CommRing R] (n : ℕ) [NeZero n]

omit [NeZero n] in
theorem pow_eq_one_multiplicative_zmod (g : Multiplicative (ZMod n)) : g ^ n = 1 := by
  rw [← ofAdd_toAdd g, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]

omit [NeZero n] in

theorem convPow_eq_one_monoidAlgebra (T : Type*) [CommRing T] [Algebra R T]
    (f : WithConv (MonoidAlgebra R (Multiplicative (ZMod n)) →ₐ[R] T)) : f ^ n = 1 := by
  apply WithConv.ext
  refine MonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
  rw [AlgHom.convPow_apply_of_isGroupLikeElem _ (MonoidAlgebra.isGroupLikeElem_single_one R g),
    AlgHom.convOne_apply_of_isGroupLikeElem (MonoidAlgebra.isGroupLikeElem_single_one R g),
    ← map_pow, MonoidAlgebra.single_pow, one_pow, pow_eq_one_multiplicative_zmod, ← MonoidAlgebra.one_def,
    map_one]

theorem etale_monoidAlgebra [IsNoetherianRing R] (hn : IsUnit (n : R)) :
    Algebra.Etale R (MonoidAlgebra R (Multiplicative (ZMod n))) :=
  HopfAlgebra.etale_of_pow_eq_one_of_isUnit_of_finite n hn
    (fun T _ _ f => convPow_eq_one_monoidAlgebra R n T f)

end GroupAlgebra
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

section StandardOrder
variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (q : ℕ) [hq : Fact q.Prime]

local notation "Rℓ" => ratLocalizedAt ℓ
local notation "G" => Multiplicative (ZMod q)
local notation "V" => MonoidAlgebra ℚ (Multiplicative (ZMod q))

theorem isUnit_natCast_ratLocalizedAt (hℓq : ℓ ≠ q) : IsUnit ((q : ℕ) : Rℓ) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hmem : (q : ℚ)⁻¹ ∈ Rℓ := by
    rw [mem_ratLocalizedAt_iff, Rat.inv_natCast_den, if_neg hq.out.ne_zero]
    exact (Nat.coprime_primes hq.out hℓ.out).2 hℓq.symm
  refine isUnit_iff_exists_inv.2 ⟨⟨(q : ℚ)⁻¹, hmem⟩, ?_⟩
  apply Subtype.ext
  simp [hq0]

noncomputable def orderMap : MonoidAlgebra Rℓ G →ₐ[Rℓ] V :=
  MonoidAlgebra.mapAlgHom G (Algebra.ofId Rℓ ℚ)

omit hℓ in
theorem orderMap_single (g : G) (r : Rℓ) :
    orderMap ℓ q (MonoidAlgebra.single g r) = MonoidAlgebra.single g (r : ℚ) := by
  rw [orderMap, MonoidAlgebra.mapAlgHom_single]
  rfl

omit hℓ in
theorem orderMap_apply_apply (x : MonoidAlgebra Rℓ G) (m : G) : (orderMap ℓ q x).coeff m = (x.coeff m : ℚ) := by
  rw [orderMap, MonoidAlgebra.coeff_mapAlgHom]
  rfl

omit hℓ in
theorem orderMap_injective : Function.Injective (orderMap ℓ q) := by
  intro x y h
  refine MonoidAlgebra.ext (Finsupp.ext fun m => Subtype.val_injective ?_)
  rw [← orderMap_apply_apply, ← orderMap_apply_apply, h]

noncomputable def stdOrder : Subalgebra Rℓ V := (orderMap ℓ q).range

omit hℓ in
theorem stdOrder_toSubmodule :
    Subalgebra.toSubmodule (stdOrder ℓ q) = Submodule.span Rℓ (Set.range (MonoidAlgebra.of ℚ G)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    change orderMap ℓ q x ∈ _
    induction x using MonoidAlgebra.induction_on with
    | of g =>
        rw [MonoidAlgebra.of_apply, orderMap_single, OneMemClass.coe_one, ← MonoidAlgebra.of_apply]
        exact Submodule.subset_span ⟨g, rfl⟩
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | smul r x hx => rw [map_smul]; exact Submodule.smul_mem _ r hx
  · rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    refine ⟨MonoidAlgebra.single g 1, ?_⟩
    change orderMap ℓ q (MonoidAlgebra.single g 1) = _
    rw [orderMap_single, MonoidAlgebra.of_apply, OneMemClass.coe_one]

scoped instance finite_stdOrder : Module.Finite Rℓ ↥(stdOrder ℓ q) :=
  Module.Finite.equiv (AlgEquiv.ofInjective (orderMap ℓ q) (orderMap_injective ℓ q)).toLinearEquiv

theorem etale_stdOrder (hℓq : ℓ ≠ q) : Algebra.Etale Rℓ ↥(stdOrder ℓ q) :=
  haveI := etale_monoidAlgebra (Rℓ) q (isUnit_natCast_ratLocalizedAt ℓ q hℓq)
  Algebra.Etale.of_equiv (AlgEquiv.ofInjective (orderMap ℓ q) (orderMap_injective ℓ q))

omit hℓ in
theorem span_stdOrder_eq_top : Submodule.span ℚ ((stdOrder ℓ q : Subalgebra Rℓ V) : Set V) = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  induction v using MonoidAlgebra.induction_on with
  | of g =>
      apply Submodule.subset_span
      refine ⟨MonoidAlgebra.single g 1, ?_⟩
      change orderMap ℓ q (MonoidAlgebra.single g 1) = _
      rw [orderMap_single, MonoidAlgebra.of_apply, OneMemClass.coe_one]
  | add x y hx hy => exact add_mem hx hy
  | smul r x hx => exact Submodule.smul_mem _ r hx

theorem stdOrder_eq_integralClosure (hℓq : ℓ ≠ q) : stdOrder ℓ q = integralClosure Rℓ V :=
  haveI := etale_stdOrder ℓ q hℓq
  Subalgebra.eq_integralClosure_of_etale_of_span_eq_top (stdOrder ℓ q) (span_stdOrder_eq_top ℓ q)

end StandardOrder
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

section KSide
p2m_attr_erase "instance" "AddCommGroup.toIntModule LieRing.instLieAlgebra"
p2m_open "Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct"

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (q : ℕ) [hq : Fact q.Prime]
  (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K] [Module.Flat ℤ K]

local notation "Rℓ" => ratLocalizedAt ℓ
local notation "G" => Multiplicative (ZMod q)
local notation "V" => MonoidAlgebra ℚ (Multiplicative (ZMod q))
local notation "T" => (ratLocalizedAt ℓ) ⊗[ℤ] K

omit hℓ hq in

theorem convPow_eq_one_baseChange (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (T' : Type) [CommRing T'] [Algebra Rℓ T'] (f : WithConv (T →ₐ[Rℓ] T')) : f ^ q = 1 := by
  haveI : @Module.Flat ℤ K _ _ (AddCommGroup.toIntModule K) :=
    Module.Flat.of_intModule_eq K _ _ ‹Module.Flat ℤ K›
  let e := Algebra.TensorProduct.pointsMulEquiv ℤ (Rℓ) K T'
  apply e.injective
  calc e (f ^ q) = (e f) ^ q := map_pow e f q
    _ = 1 := by
        rw [← hgenq]
        exact HopfAlgebra.convPow_natCard_algHom_algebraicClosure_eq_one K T' (e f)
    _ = e 1 := (map_one e).symm

theorem etale_baseChange (hℓq : ℓ ≠ q) (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    [Module.Finite Rℓ T] : Algebra.Etale Rℓ T :=
  HopfAlgebra.etale_of_pow_eq_one_of_isUnit_of_finite q (isUnit_natCast_ratLocalizedAt ℓ q hℓq)
    (fun T' _ _ f => convPow_eq_one_baseChange ℓ q K hgenq T' f)

theorem locQRange_eq_integralClosure (hℓq : ℓ ≠ q)
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] V) [Module.Finite Rℓ T] :
    locQRange ℓ q K φ = integralClosure Rℓ V := by
  haveI : Module.Finite Rℓ ↥(locQRange ℓ q K φ) := finite_locQRange ℓ q K φ
  haveI : Algebra.Etale Rℓ T := etale_baseChange ℓ q K hℓq hgenq
  haveI : Algebra.Etale Rℓ ↥(locQRange ℓ q K φ) := Algebra.Etale.of_equiv (locQAlgEquiv ℓ q K φ)
  exact Subalgebra.eq_integralClosure_of_etale_of_span_eq_top _ (span_rat_coe_locQRange_eq_top ℓ q K φ)

theorem span_range_restrictBaseChange_eq_span_range_of_of_ne
    (hℓq : ℓ ≠ q)
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod q)))
    [Module.Finite (GaloisRep.ratLocalizedAt ℓ) ((GaloisRep.ratLocalizedAt ℓ) ⊗[ℤ] K)] :
    Submodule.span (GaloisRep.ratLocalizedAt ℓ)
        (Set.range ⇑(Algebra.TensorProduct.restrictBaseChange ℚ
          (φ : ℚ ⊗[ℤ] K →ₐ[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod q))))) =
      Submodule.span (GaloisRep.ratLocalizedAt ℓ)
        (Set.range ⇑(MonoidAlgebra.of ℚ (Multiplicative (ZMod q)))) := by
  rw [← locQRange_toSubmodule ℓ q K φ, ← stdOrder_toSubmodule, locQRange_eq_integralClosure ℓ q K hℓq hgenq φ,
    stdOrder_eq_integralClosure ℓ q hℓq]

end KSide
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom"

end HopfAlgebra.LocEt
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.HopfAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.HopfAlgebra.LocEt"
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.HopfAlgebra"

section LocEtLeg
p2m_attr_erase "instance" "AddCommGroup.toIntModule LieRing.instLieAlgebra"
p2m_open_scoped "TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.TensorProduct"

theorem span_range_restrictBaseChange_eq_span_range_of_of_ne
    (q : ℕ) [Fact q.Prime] (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q)
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K] [Module.Flat ℤ K]
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (φ : ℚ ⊗[ℤ] K ≃ₐc[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod q)))
    [Module.Finite (GaloisRep.ratLocalizedAt ℓ) ((GaloisRep.ratLocalizedAt ℓ) ⊗[ℤ] K)] :
    Submodule.span (GaloisRep.ratLocalizedAt ℓ)
        (Set.range ⇑(Algebra.TensorProduct.restrictBaseChange ℚ
          (φ : ℚ ⊗[ℤ] K →ₐ[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod q))))) =
      Submodule.span (GaloisRep.ratLocalizedAt ℓ)
        (Set.range ⇑(MonoidAlgebra.of ℚ (Multiplicative (ZMod q)))) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  exact HopfAlgebra.LocEt.span_range_restrictBaseChange_eq_span_range_of_of_ne ℓ q K hℓq hgenq φ

end LocEtLeg
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.HopfAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.HopfAlgebra.LocEt"

section N1R2
p2m_attr_erase "instance" "AddCommGroup.toIntModule LieRing.instLieAlgebra"
p2m_open "TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.TensorProduct Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct GaloisRep~isFractionRing_ratLocalizedAt~isDiscreteValuationRing_ratLocalizedAt P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra"

set_option maxHeartbeats 3200000 in

theorem N1_core
    (p : ℕ) (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K] [Module.Flat ℤ K]
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ) (k : K),
        σ (ψ k) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) k)
    (hK : ¬ Module.Finite ℤ K) :
    p.Prime ∧
      ∃ ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐc[ℤ] K,
      ∀ (R : Type) [CommRing R],
        (∀ f g : K →ₐ[ℤ] R, f.comp (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) =
            g.comp (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) → f = g) ∧
        ∀ g : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] R,
          (∃ f : K →ₐ[ℤ] R, f.comp (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) = g) ↔
            ∃ a : R, a - 1 ∈ Ideal.span {(p : R)} ∧
              ∀ h : MonoidAlgebra ℤ (Multiplicative (ZMod q)),
                a * (g h - algebraMap ℤ R
                  (Bialgebra.counitAlgHom ℤ (MonoidAlgebra ℤ (Multiplicative (ZMod q))) h)) = 0 := by
  classical

  have hPrime : p.Prime := Nat.prime_of_finite_baseChange_ratLocalizedAt_of_ne_of_not_finite p K hff hK
  haveI hpF : Fact p.Prime := ⟨hPrime⟩
  haveI : Fact (1 < q) := ⟨(Fact.out : q.Prime).one_lt⟩

  have htf : ∀ k : K, (p : K) * k = 0 → k = 0 := by
    intro k hk
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := K)
      (mem_nonZeroDivisors_of_ne_zero (Int.natCast_ne_zero.2 hPrime.ne_zero))
    apply hreg
    dsimp only
    rw [smul_zero, Algebra.smul_def, map_natCast]
    exact hk

  have hφ : Nonempty (ℚ ⊗[ℤ] K ≃ₐc[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod q))) :=
    nonempty_bialgEquiv_rat_baseChange_of_face q K hgenq hgal
      (fun A _ _ _ => HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_eq_of_convPow_rat q A)
  obtain ⟨φ⟩ := hφ

  set j : K →ₐ[ℤ] MonoidAlgebra ℚ (Multiplicative (ZMod q)) :=
    restrictBaseChange ℚ (φ : ℚ ⊗[ℤ] K →ₐ[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod q))) with hjdef
  have hj_inj : Function.Injective j :=
    restrictBaseChange_injective (nonZeroDivisors ℤ) ℚ le_rfl _ φ.injective
  have hj_sat : ∀ v : MonoidAlgebra ℚ (Multiplicative (ZMod q)), ∃ d : nonZeroDivisors ℤ, (d : ℤ) • v ∈ Set.range j :=
    exists_smul_mem_range_restrictBaseChange (nonZeroDivisors ℤ) ℚ _ φ.surjective
  have hj_cou : ∀ k : K, Coalgebra.counit (R := ℚ) (j k) = algebraMap ℤ ℚ (Coalgebra.counit (R := ℤ) k) :=
    fun k => counit_restrictBaseChange ℚ (φ : ℚ ⊗[ℤ] K →ₐc[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod q))) k
  have hj_gl : ∀ k : K, IsGroupLikeElem ℚ (j k) ↔ IsGroupLikeElem ℤ k :=
    fun k => isGroupLikeElem_restrictBaseChange_iff (nonZeroDivisors ℤ) ℚ le_rfl φ k
  have hj_adams : ∀ (a : ℕ) (k : K),
      MonoidAlgebra.mapDomainAlgHom ℚ ℚ (powMonoidHom a) (j k) ∈ Set.range j := by
    intro a k
    refine ⟨((WithConv.toConv (AlgHom.id ℤ K)) ^ a).ofConv k, ?_⟩
    have := Algebra.TensorProduct.convPow_id_restrictBaseChange ℚ
      (φ : ℚ ⊗[ℤ] K →ₐc[ℚ] MonoidAlgebra ℚ (Multiplicative (ZMod q))) a k
    rw [MonoidAlgebra.convPow_id_ofConv_eq_mapDomainAlgHom] at this
    exact this.symm

  let Bp : Subalgebra (ratLocalizedAt p) (MonoidAlgebra ℚ (Multiplicative (ZMod q))) :=
    Algebra.adjoin (ratLocalizedAt p) (Set.range j)
  have hrange_closed : (Submonoid.closure (Set.range ⇑j) : Set (MonoidAlgebra ℚ (Multiplicative (ZMod q)))) = Set.range j := by
    have : Submonoid.closure (Set.range ⇑j) = (j : K →+* MonoidAlgebra ℚ (Multiplicative (ZMod q))).rangeS.toSubmonoid :=
      le_antisymm (Submonoid.closure_le.2 fun x hx => hx) fun x hx => Submonoid.subset_closure hx
    rw [this]; rfl
  have hBp_sub : Subalgebra.toSubmodule Bp = Submodule.span (ratLocalizedAt p) (Set.range j) := by
    rw [Algebra.adjoin_eq_span, hrange_closed]
  have hRsmul : ∀ (r : ratLocalizedAt p) (x : MonoidAlgebra ℚ (Multiplicative (ZMod q))), r • x = (r : ℚ) • x :=
    fun r x => rfl

  have hfg : Bp.FG := by
    obtain ⟨T, hT⟩ := Algebra.FiniteType.out (R := ℤ) (A := K)
    refine ⟨T.image j, le_antisymm (Algebra.adjoin_mono (by
      intro y hy
      rw [Finset.coe_image] at hy
      obtain ⟨x, -, rfl⟩ := hy
      exact ⟨x, rfl⟩)) (Algebra.adjoin_le ?_)⟩
    rintro _ ⟨k, rfl⟩
    have hk : k ∈ Algebra.adjoin ℤ (T : Set K) := by rw [hT]; exact Algebra.mem_top
    have : j k ∈ (Algebra.adjoin ℤ (T : Set K)).map j := Subalgebra.mem_map.2 ⟨k, hk, rfl⟩
    rw [AlgHom.map_adjoin] at this
    refine (Algebra.adjoin_le (R := ℤ) ?_ : Algebra.adjoin ℤ (⇑j '' ↑T) ≤
      (Algebra.adjoin (ratLocalizedAt p) (↑(T.image j) : Set _)).restrictScalars ℤ) this
    intro x hx
    exact Algebra.subset_adjoin (by simpa using hx)

  have haug : ∀ b ∈ Bp, Coalgebra.counit (R := ℚ) b ∈ ratLocalizedAt p := by
    intro b hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [hj_cou]
      exact intCast_mem_ratLocalizedAt _
    | algebraMap r =>
      rw [IsScalarTower.algebraMap_apply (ratLocalizedAt p) ℚ (MonoidAlgebra ℚ (Multiplicative (ZMod q))),
        Bialgebra.counit_algebraMap]
      exact r.2
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [Bialgebra.counit_mul]; exact mul_mem hx hy

  have hsat : ∀ v : MonoidAlgebra ℚ (Multiplicative (ZMod q)), ∃ n : ℕ, 0 < n ∧ (n : ℚ) • v ∈ Bp := by
    intro v
    obtain ⟨d, hd⟩ := hj_sat v
    have hd0 : (d : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero d
    refine ⟨(d : ℤ).natAbs, Int.natAbs_pos.2 hd0, ?_⟩
    have hmem : ((d : ℤ) : ℚ) • v ∈ Bp := by
      rw [Int.cast_smul_eq_zsmul]
      exact Algebra.subset_adjoin hd
    rcases Int.natAbs_eq (d : ℤ) with h | h
    · rw [h, Int.cast_natCast] at hmem
      exact hmem
    · rw [h, Int.cast_neg, Int.cast_natCast, neg_smul] at hmem
      exact (neg_mem_iff).1 hmem

  have hadams : ∀ a : ℕ, a.Coprime q → ∀ b ∈ Bp,
      MonoidAlgebra.mapDomainAlgHom ℚ ℚ (powMonoidHom a) b ∈ Bp := by
    intro a _ b hb
    let σ : MonoidAlgebra ℚ (Multiplicative (ZMod q)) →ₐ[ratLocalizedAt p] MonoidAlgebra ℚ (Multiplicative (ZMod q)) :=
      (MonoidAlgebra.mapDomainAlgHom ℚ ℚ (powMonoidHom a)).restrictScalars (ratLocalizedAt p)
    have : σ b ∈ Bp.map σ := Subalgebra.mem_map.2 ⟨b, hb, rfl⟩
    rw [AlgHom.map_adjoin] at this
    refine Algebra.adjoin_le ?_ this
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact Algebra.subset_adjoin (hj_adams a k)

  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have hinf : ¬ (Subalgebra.toSubmodule Bp).FG := by
    rw [hBp_sub]
    exact not_fg_span_range_of_not_finite p q K hff hK φ

  have hBp : ∀ v, v ∈ Bp ↔ Coalgebra.counit (R := ℚ) v ∈ ratLocalizedAt p :=
    MonoidAlgebra.mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg p hPrime q Bp hfg haug hsat hadams hinf

  have hloc : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Submodule.span (ratLocalizedAt ℓ) (Set.range ⇑j) =
        Submodule.span (ratLocalizedAt ℓ) (Set.range ⇑(MonoidAlgebra.of ℚ (Multiplicative (ZMod q)))) := by
    intro ℓ hℓ hℓp
    by_cases hℓq : ℓ = q
    · subst hℓq
      haveI := hff ℓ hℓ hℓp
      exact span_range_restrictBaseChange_eq_span_range_of_face ℓ K φ hgenq hgal
        (fun H _ _ _ _ => HopfAlgebra.nonempty_bialgEquiv_monoidAlgebra_of_natCard_algHom_ratLocalizedAt_eq_of_convPow_of_ne_two ℓ hq2 H)
    · haveI := hff ℓ hℓ hℓp
      exact span_range_restrictBaseChange_eq_span_range_of_of_ne q ℓ hℓ hℓq K hgenq φ

  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hPrime.ne_zero
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  set ιV : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →+* MonoidAlgebra ℚ (Multiplicative (ZMod q)) :=
    MonoidAlgebra.mapRingHom (Multiplicative (ZMod q)) (Int.castRingHom ℚ) with hιV
  let M : AddSubgroup (MonoidAlgebra ℚ (Multiplicative (ZMod q))) :=
    (j : K →+* MonoidAlgebra ℚ (Multiplicative (ZMod q))).range.toAddSubgroup
  let N : AddSubgroup (MonoidAlgebra ℚ (Multiplicative (ZMod q))) := ιV.range.toAddSubgroup
  have hMcoe : (M : Set (MonoidAlgebra ℚ (Multiplicative (ZMod q)))) = Set.range j := RingHom.coe_range _
  have hNcoe : (N : Set (MonoidAlgebra ℚ (Multiplicative (ZMod q)))) = Set.range ιV := RingHom.coe_range _
  have hmemN : ∀ x, x ∈ N ↔ ∃ h, ιV h = x := fun x => RingHom.mem_range
  have hmemM : ∀ x, x ∈ M ↔ ∃ k, j k = x := fun x => RingHom.mem_range
  have hιV_single : ∀ (g : Multiplicative (ZMod q)) (z : ℤ), ιV (single g z) = single g (z : ℚ) :=
    fun g z => MonoidAlgebra.mapRingHom_single _ _ _
  have hιV_apply : ∀ (x : MonoidAlgebra ℤ (Multiplicative (ZMod q))) (m : Multiplicative (ZMod q)),
      (ιV x).coeff m = ((x.coeff m : ℤ) : ℚ) := fun x m => MonoidAlgebra.coeff_mapRingHom _ _ _
  have hιV_inj : Function.Injective ιV := by
    intro x y hxy
    refine MonoidAlgebra.ext (Finsupp.ext fun m => ?_)
    have h : (ιV x).coeff m = (ιV y).coeff m := by rw [hxy]
    rw [hιV_apply, hιV_apply] at h
    exact Int.cast_injective h
  have hof_mem_N : ∀ g, MonoidAlgebra.of ℚ (Multiplicative (ZMod q)) g ∈ N := fun g =>
    (hmemN _).2 ⟨single g 1, by rw [hιV_single, Int.cast_one, MonoidAlgebra.of_apply]⟩
  have hs_N : MonoidAlgebra.normElem ℚ (Multiplicative (ZMod q)) ∈ N := by
    unfold MonoidAlgebra.normElem
    exact sum_mem fun g _ => hof_mem_N g

  have hspanN : ∀ ℓ : ℕ, Submodule.span (ratLocalizedAt ℓ) (N : Set (MonoidAlgebra ℚ (Multiplicative (ZMod q)))) =
      Submodule.span (ratLocalizedAt ℓ) (Set.range ⇑(MonoidAlgebra.of ℚ (Multiplicative (ZMod q)))) := by
    intro ℓ
    apply le_antisymm
    · rw [Submodule.span_le, hNcoe]
      rintro _ ⟨h, rfl⟩
      have hsum : ιV h = (ιV h).coeff.sum (fun g c => single g c) := (MonoidAlgebra.sum_coeff_single _).symm
      rw [hsum]
      refine Submodule.sum_mem _ fun g _ => ?_
      change single g ((ιV h).coeff g) ∈ _
      rw [hιV_apply, ← mul_one ((h.coeff g : ℤ) : ℚ), ← MonoidAlgebra.smul_single', ← MonoidAlgebra.of_apply]
      change ((⟨((h.coeff g : ℤ) : ℚ), intCast_mem_ratLocalizedAt _⟩ : ratLocalizedAt ℓ) •
        MonoidAlgebra.of ℚ (Multiplicative (ZMod q)) g) ∈ _
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact Submodule.subset_span (hof_mem_N g)
  have hspanQN : Submodule.span ℚ (N : Set (MonoidAlgebra ℚ (Multiplicative (ZMod q)))) = ⊤ := by
    apply eq_top_iff.2
    rintro v -
    induction v using MonoidAlgebra.induction_on with
    | of g => exact Submodule.subset_span (hof_mem_N g)
    | add x y hx hy => exact add_mem hx hy
    | smul r x hx => exact Submodule.smul_mem _ r hx
  have hsatN : ∀ v, ∃ d : ℤ, d ≠ 0 ∧ (d : ℚ) • v ∈ N := AddSubgroup.exists_zsmul_mem_of_span_eq_top N hspanQN
  have hMN : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Submodule.span (ratLocalizedAt ℓ) (M : Set (MonoidAlgebra ℚ (Multiplicative (ZMod q)))) =
        Submodule.span (ratLocalizedAt ℓ) (N : Set (MonoidAlgebra ℚ (Multiplicative (ZMod q)))) := by
    intro ℓ hℓ hℓp
    rw [hMcoe, hloc ℓ hℓ hℓp, hspanN]

  have hmem_range : ∀ x : MonoidAlgebra ℚ (Multiplicative (ZMod q)),
      (∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → x ∈ Submodule.span (ratLocalizedAt ℓ) (N : Set (MonoidAlgebra ℚ (Multiplicative (ZMod q))))) →
      Coalgebra.counit (R := ℚ) x ∈ ratLocalizedAt p → x ∈ Set.range j := by
    intro x hx hxp
    rw [← hMcoe]
    refine AddSubgroup.mem_of_forall_prime_mem_span_ratLocalizedAt M x fun ℓ hℓ => ?_
    by_cases hℓp : ℓ = p
    · subst hℓp
      rw [hMcoe, ← hBp_sub, Subalgebra.mem_toSubmodule]
      exact (hBp x).2 hxp
    · rw [hMN ℓ hℓ hℓp]
      exact hx ℓ hℓ hℓp

  obtain ⟨uK, huK⟩ : MonoidAlgebra.of ℚ (Multiplicative (ZMod q)) (Multiplicative.ofAdd 1) ∈ Set.range j :=
    hmem_range _ (fun ℓ _ _ => Submodule.subset_span (hof_mem_N _))
      (by rw [MonoidAlgebra.of_apply, MonoidAlgebra.counit_single, CommSemiring.counit_apply]; exact one_mem _)
  have huK_gl : IsGroupLikeElem ℤ uK :=
    (hj_gl uK).1 (by rw [huK, MonoidAlgebra.of_apply]; exact MonoidAlgebra.isGroupLikeElem_single_one ℚ _)
  have hu_pow_V : (MonoidAlgebra.of ℚ (Multiplicative (ZMod q)) (Multiplicative.ofAdd 1)) ^ q = 1 := by
    rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, ofAdd_zero, map_one]
  have huK_pow : uK ^ q = 1 := hj_inj (by rw [map_pow, huK, hu_pow_V, map_one])
  let ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐc[ℤ] K := MonoidAlgebra.hullLift uK huK_gl huK_pow
  have hjι : ∀ h, j (ι h) = ιV h := by
    have hcomp : (j : K →+* MonoidAlgebra ℚ (Multiplicative (ZMod q))).comp
        (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →+* K) = ιV := by
      refine MonoidAlgebra.ringHom_ext (fun z => ?_) (fun g => ?_)
      · rw [RingHom.comp_apply, hιV_single]
        change j (MonoidAlgebra.hullLift uK huK_gl huK_pow (single 1 z)) = _
        rw [MonoidAlgebra.hullLift_single, toAdd_one, ZMod.val_zero, pow_zero, ← Algebra.algebraMap_eq_smul_one,
          AlgHom.commutes, IsScalarTower.algebraMap_apply ℤ ℚ (MonoidAlgebra ℚ (Multiplicative (ZMod q))),
          eq_intCast, Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def, MonoidAlgebra.smul_single', mul_one]
      · rw [RingHom.comp_apply, hιV_single, Int.cast_one]
        change j (MonoidAlgebra.liftBialgHom (powHomOfPowEqOne uK huK_pow) (fun _ => huK_gl.pow)
          (MonoidAlgebra.of ℤ (Multiplicative (ZMod q)) g)) = _
        rw [MonoidAlgebra.liftBialgHom_apply, MonoidAlgebra.lift_of, powHomOfPowEqOne_apply,
          map_pow, huK, ← map_pow, pow_eq_ofAdd_mul_toAdd, toAdd_ofAdd, mul_one, ZMod.natCast_zmod_val,
          ofAdd_toAdd, MonoidAlgebra.of_apply]
    intro h
    exact (RingHom.congr_fun hcomp h :)
  have hι_inj : Function.Injective ι := by
    have hc : (⇑j ∘ ⇑ι) = ⇑ιV := funext hjι
    exact Function.Injective.of_comp (f := ⇑j) (by rw [hc]; exact hιV_inj)

  obtain ⟨c, hc1, hc2⟩ : ∃ c : ℤ, (p : ℤ) ∣ c - 1 ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ((c : ℚ) / q) ∈ ratLocalizedAt ℓ := by
    have hden : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ q → ((q : ℚ)⁻¹) ∈ ratLocalizedAt ℓ := by
      intro ℓ hℓ hℓq
      rw [mem_ratLocalizedAt_iff', Rat.inv_natCast_den, if_neg (Fact.out : q.Prime).ne_zero]
      exact (Nat.coprime_primes (Fact.out : q.Prime) hℓ).2 (Ne.symm hℓq)
    by_cases hqp : q = p
    · refine ⟨1, by simp, fun ℓ hℓ hℓp => ?_⟩
      rw [Int.cast_one, one_div]
      exact hden ℓ hℓ (hqp ▸ hℓp)
    · have hcop : IsCoprime (p : ℤ) (q : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
        exact (Nat.coprime_primes hPrime (Fact.out : q.Prime)).2 (Ne.symm hqp)
      obtain ⟨x, y, hxy⟩ := hcop
      refine ⟨y * q, ⟨-x, by linear_combination hxy⟩, fun ℓ hℓ hℓp => ?_⟩
      rw [show (((y * q : ℤ)) : ℚ) / q = (y : ℚ) by push_cast; field_simp]
      exact intCast_mem_ratLocalizedAt _
  set s : MonoidAlgebra ℚ (Multiplicative (ZMod q)) := MonoidAlgebra.normElem ℚ (Multiplicative (ZMod q)) with hs
  set xa : MonoidAlgebra ℚ (Multiplicative (ZMod q)) := ((c : ℚ) / q) • s with hxa
  have hxa_span : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      xa ∈ Submodule.span (ratLocalizedAt ℓ) (N : Set (MonoidAlgebra ℚ (Multiplicative (ZMod q)))) := by
    intro ℓ hℓ hℓp
    change ((⟨(c : ℚ) / q, hc2 ℓ hℓ hℓp⟩ : ratLocalizedAt ℓ) • s) ∈ _
    exact Submodule.smul_mem _ _ (Submodule.subset_span hs_N)
  have hεxa : Coalgebra.counit (R := ℚ) xa = c := by
    rw [hxa, map_smul, hs, MonoidAlgebra.counit_normElem, Fintype.card_multiplicative, ZMod.card, smul_eq_mul]
    field_simp
  obtain ⟨a, ha⟩ : xa ∈ Set.range j := hmem_range xa hxa_span (by rw [hεxa]; exact intCast_mem_ratLocalizedAt _)
  set ya : MonoidAlgebra ℚ (Multiplicative (ZMod q)) := ((p : ℚ)⁻¹) • (xa - 1) with hya
  obtain ⟨t, ht⟩ := hc1
  have hpinv : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → ((p : ℚ)⁻¹) ∈ ratLocalizedAt ℓ := by
    intro ℓ hℓ hℓp
    rw [mem_ratLocalizedAt_iff', Rat.inv_natCast_den, if_neg hPrime.ne_zero]
    exact (Nat.coprime_primes hPrime hℓ).2 (Ne.symm hℓp)
  obtain ⟨a', ha'⟩ : ya ∈ Set.range j := by
    refine hmem_range ya (fun ℓ hℓ hℓp => ?_) ?_
    · change ((⟨(p : ℚ)⁻¹, hpinv ℓ hℓ hℓp⟩ : ratLocalizedAt ℓ) • (xa - 1)) ∈ _
      refine Submodule.smul_mem _ _ (sub_mem (hxa_span ℓ hℓ hℓp) (Submodule.subset_span ?_))
      rw [MonoidAlgebra.one_def, ← MonoidAlgebra.of_apply]
      exact hof_mem_N 1
    · rw [hya, map_smul, map_sub, hεxa, Bialgebra.counit_one, smul_eq_mul,
        show ((c : ℚ) - 1) = (p : ℚ) * t by exact_mod_cast ht, ← mul_assoc, inv_mul_cancel₀ hp0, one_mul]
      exact intCast_mem_ratLocalizedAt _

  have hS1 : a - 1 ∈ Ideal.span {(p : K)} := by
    refine Ideal.mem_span_singleton'.2 ⟨a', hj_inj ?_⟩
    rw [map_mul, map_natCast, map_sub, map_one, ha, ha', hya, mul_comm,
      ← map_natCast (algebraMap ℚ (MonoidAlgebra ℚ (Multiplicative (ZMod q)))) p, ← Algebra.smul_def, smul_smul,
      mul_inv_cancel₀ hp0, one_smul]
  have hS2 : ∀ k : K, a * (k - algebraMap ℤ K (Bialgebra.counitAlgHom ℤ K k)) = 0 := by
    intro k
    apply hj_inj
    rw [map_mul, map_sub, map_zero, ha, AlgHom.commutes, Bialgebra.counitAlgHom_apply,
      IsScalarTower.algebraMap_apply ℤ ℚ (MonoidAlgebra ℚ (Multiplicative (ZMod q))), ← hj_cou k, hxa,
      smul_mul_assoc, hs, MonoidAlgebra.normElem_mul_sub_algebraMap_counit, smul_zero]
  have hS3 : ∀ k : K, ∃ (n : ℕ) (h : MonoidAlgebra ℤ (Multiplicative (ZMod q))), (p : K) ^ n * k = ι h := by
    intro k
    obtain ⟨n, hn⟩ := AddSubgroup.exists_pow_smul_mem_of_forall_ne_span_eq M N p hPrime hMN hsatN (j k)
      ((hmemM _).2 ⟨k, rfl⟩)
    obtain ⟨h, hh⟩ := (hmemN _).1 hn
    refine ⟨n, h, hj_inj ?_⟩
    rw [map_mul, map_pow, map_natCast, hjι, hh,
      ← map_natCast (algebraMap ℚ (MonoidAlgebra ℚ (Multiplicative (ZMod q)))) p, ← map_pow, ← Algebra.smul_def]

  refine ⟨hPrime, ι, fun R _ => ?_⟩
  have hP := AlgHom.comp_injective_and_exists_comp_eq_iff_of_sub_one_mem_span_of_mul_sub_eq_zero
    (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) (Bialgebra.counitAlgHom ℤ K) p a hι_inj htf hS1 hS2 hS3 R
  have hcou : ∀ h : MonoidAlgebra ℤ (Multiplicative (ZMod q)),
      Bialgebra.counitAlgHom ℤ K ((ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) h) =
        Bialgebra.counitAlgHom ℤ (MonoidAlgebra ℤ (Multiplicative (ZMod q))) h := by
    intro h
    rw [Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply]
    exact @CoalgHomClass.counit_comp_apply ℤ _ _ _ _ _ Algebra.toModule _ Algebra.toModule _ _ _ _ ι h
  refine ⟨hP.1, fun g => ?_⟩
  rw [hP.2 g]
  simp only [hcou]

end N1R2
p2m_reactivate "P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.MonoidAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.Algebra.TensorProduct P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.AlgHom P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.HopfAlgebra P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.HopfAlgebra.LocEt"

p2m_open_scoped "Module Module.Flat" in
theorem Module.Flat.of_intModule_eq' (K : Type*) [AddCommGroup K] (i₁ i₂ : Module ℤ K)
    (h : @Module.Flat ℤ K _ _ i₁) : @Module.Flat ℤ K _ _ i₂ := by
  cases Subsingleton.elim i₁ i₂; exact h

p2m_open "GaloisRep~isFractionRing_ratLocalizedAt~isDiscreteValuationRing_ratLocalizedAt" in open _root_.P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two.GaloisRep in
theorem solution
    (p : ℕ) (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (K : Type) [CommRing K] [HopfAlgebra ℤ K] [Algebra.FiniteType ℤ K] [Module.Flat ℤ K]
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (nσ : ℕ),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ q = 1 → σ ζ = ζ ^ nσ) →
      ∀ (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ) (k : K),
        σ (ψ k) = (WithConv.ofConv (WithConv.toConv ψ ^ nσ)) k)
    (hK : ¬ Module.Finite ℤ K) :
    p.Prime ∧
      ∃ ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐc[ℤ] K,
      ∀ (R : Type) [CommRing R],
        (∀ f g : K →ₐ[ℤ] R, f.comp (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) =
            g.comp (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) → f = g) ∧
        ∀ g : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] R,
          (∃ f : K →ₐ[ℤ] R, f.comp (ι : MonoidAlgebra ℤ (Multiplicative (ZMod q)) →ₐ[ℤ] K) = g) ↔
            ∃ a : R, a - 1 ∈ Ideal.span {(p : R)} ∧
              ∀ h : MonoidAlgebra ℤ (Multiplicative (ZMod q)),
                a * (g h - algebraMap ℤ R
                  (Bialgebra.counitAlgHom ℤ (MonoidAlgebra ℤ (Multiplicative (ZMod q))) h)) = 0 := by
  refine @N1_core p q _ hq2 K _ _ _ (Module.Flat.of_intModule_eq' K _ _ ‹Module.Flat ℤ K›) ?_ hgenq hgal ?_
  · intro ℓ hℓ hℓp
    exact Module.Finite.baseChange_of_intModule_eq (ratLocalizedAt ℓ) K _ _ (hff ℓ hℓ hℓp)
  · exact fun h => hK (Module.Finite.of_intModule_eq K _ _ h)

end S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two
end P2MW
export P2MW.S_HopfAlgebra_prime_and_exists_bialgHom_monoidAlgebra_of_natCard_algHom_eq_of_convPow_of_not_finite_of_ne_two (solution)
