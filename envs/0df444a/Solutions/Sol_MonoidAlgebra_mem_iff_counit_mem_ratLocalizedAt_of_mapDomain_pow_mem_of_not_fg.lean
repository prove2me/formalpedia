-- Prove2me | solution 1 for MonoidAlgebra.mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/26a0f4c8-74d0-577b-b878-78679162c6a7

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option autoImplicit false

open TensorProduct Polynomial

namespace Algebra
p2m_export "Algebra" "algebraMap_eq_smul_one commutes TensorProduct.includeRight mk algebraMap mem_top norm IsIntegral.isIntegral FiniteType IsIntegral.finite toModule smul_def id"
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

p2m_alias "P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg.Module.Finite.of_exists_smul_isIntegral_maximal" "Module.Finite.of_exists_smul_isIntegral_maximal"

private theorem _root_.Module.Finite.of_finite_baseChange_localization_maximal [Algebra.FiniteType R K]
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      Module.Finite (Localization.AtPrime m) (Localization.AtPrime m ⊗[R] K)) :
    Module.Finite R K :=
  Module.Finite.of_exists_smul_isIntegral_maximal fun m _ x =>
    exists_smul_isIntegral_of_finite_baseChange m (Localization.AtPrime m) x

p2m_alias "P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg.Module.Finite.of_finite_baseChange_localization_maximal" "Module.Finite.of_finite_baseChange_localization_maximal"
end Algebra.FiniteTypeLocal

section IntModuleTransport

namespace Module p2m_export "Module" "mk Finite.iff_fg IsPrincipal Finite.of_exists_smul_isIntegral_maximal Finite.of_finite_baseChange_localization_maximal" namespace Finite p2m_export "Module.Finite" "left trans map iff_fg self of_exists_smul_isIntegral_maximal of_finite_baseChange_localization_maximal" end Module.Finite
p2m_open_scoped "Module Module.Finite" in
theorem Module.Finite.of_intModule_eq (K : Type*) [AddCommGroup K] (i₁ i₂ : Module ℤ K)
    (h : @Module.Finite ℤ K _ _ i₁) : @Module.Finite ℤ K _ _ i₂ := by
  cases Subsingleton.elim i₁ i₂; exact h

p2m_open_scoped "Module Module.Finite" in
theorem Module.Finite.baseChange_of_intModule_eq (S : Type*) [CommRing S] (K : Type*) [AddCommGroup K]
    (i₁ i₂ : Module ℤ K)
    (h : by letI := i₁; exact Module.Finite S (TensorProduct ℤ S K)) :
    by letI := i₂; exact Module.Finite S (TensorProduct ℤ S K) := by
  cases Subsingleton.elim i₁ i₂; exact h

end IntModuleTransport

open TensorProduct

namespace GaloisRep
p2m_export "GaloisRep" "ratLocalizedAt"
p2m_open "GaloisRep"

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
p2m_reactivate "P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg.GaloisRep"

section AnyIntAlgebra

p2m_attr_erase "instance" "AddCommGroup.toIntModule LieRing.instLieAlgebra"

p2m_open_scoped "Module Module.Finite" in
open _root_.GaloisRep _root_.P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg.GaloisRep in

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

namespace Nat p2m_export "Nat" "exists_eq_succ_of_ne_zero Coprime.eq_one_of_dvd Prime.coprime_iff_not_dvd succ Coprime Coprime.coprime_dvd_left Coprime.symm cast_eq_zero coprime_comm lt_succ_self Prime prime_iff_prime_int any cast_inj succ_sub_one all zero" end Nat
p2m_open_scoped "Nat" in
open _root_.GaloisRep _root_.P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg.GaloisRep in

theorem Nat.prime_of_finite_baseChange_ratLocalizedAt_of_ne_of_not_finite (p : ℕ)
    (K : Type*) [CommRing K] [Algebra ℤ K] [Algebra.FiniteType ℤ K]
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → Module.Finite (ratLocalizedAt ℓ) ((ratLocalizedAt ℓ) ⊗[ℤ] K))
    (hK : ¬ Module.Finite ℤ K) : p.Prime := by
  by_contra hp
  exact hK (Module.Finite.of_finite_baseChange_ratLocalizedAt K fun ℓ hℓ => hff ℓ hℓ (fun h => hp (h ▸ hℓ)))

end AnyIntAlgebra
p2m_reactivate "P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg.GaloisRep"

namespace GaloisRep
p2m_export "GaloisRep" "ratLocalizedAt"
p2m_open "GaloisRep"

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
p2m_reactivate "P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg.GaloisRep"

namespace GaloisRep
p2m_export "GaloisRep" "ratLocalizedAt"
p2m_open "GaloisRep"

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
p2m_reactivate "P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg.GaloisRep"

section NORM
p2m_open "MonoidAlgebra P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg.MonoidAlgebra"

variable (R : Type) [CommRing R] (G : Type) [Group G] [Fintype G]

namespace MonoidAlgebra p2m_export "MonoidAlgebra" "coeff module mapDomainAlgHom of mapDomain_single unique one_def smul_single' of_apply ring induction_on map mapDomain counit_single single mapDomainAlgHom_apply ext smul_apply single_apply algHom_ext algebra coeff_map" end MonoidAlgebra
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

end NORM
p2m_reactivate "P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg.GaloisRep"

section ETP_ADAMS
p2m_open "MonoidAlgebra P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg.MonoidAlgebra"

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
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp_rw [MonoidAlgebra.of_apply]
  simp [Finsupp.single_apply, MonoidAlgebra.coeff_single]

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
  apply MonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro g
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
p2m_reactivate "P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg.GaloisRep"

section ETP_INTEGRAL
p2m_open "MonoidAlgebra P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg.MonoidAlgebra Polynomial"

variable (q : ℕ)

theorem adamsOp_congr [NeZero q] {a a' : ℕ} (h : (a : ZMod q) = a') : adamsOp q a = adamsOp q a' := by
  apply MonoidAlgebra.algHom_ext
  · intro g
    rw [← MonoidAlgebra.of_apply, MonoidAlgebra.of_apply, adamsOp_single, adamsOp_single,
      pow_eq_ofAdd_mul_toAdd, pow_eq_ofAdd_mul_toAdd, h]
  · exact Subsingleton.elim _ _

theorem adamsOp_adamsOp (m n : ℕ) (v : MonoidAlgebra ℚ (Multiplicative (ZMod q))) :
    adamsOp q m (adamsOp q n v) = adamsOp q (n * m) v := by
  revert v
  rw [← funext_iff]
  change ⇑((adamsOp q m).comp (adamsOp q n)) = ⇑(adamsOp q (n * m))
  congr 1
  apply MonoidAlgebra.algHom_ext
  · intro g
    rw [AlgHom.comp_apply, ← MonoidAlgebra.of_apply, MonoidAlgebra.of_apply, adamsOp_single, adamsOp_single,
      adamsOp_single, pow_mul]
  · exact Subsingleton.elim _ _

theorem adamsOp_one [NeZero q] (v : MonoidAlgebra ℚ (Multiplicative (ZMod q))) : adamsOp q 1 v = v := by
  revert v
  rw [← funext_iff]
  change ⇑(adamsOp q 1) = ⇑(AlgHom.id ℚ (MonoidAlgebra ℚ (Multiplicative (ZMod q))))
  congr 1
  apply MonoidAlgebra.algHom_ext
  · intro g
    rw [← MonoidAlgebra.of_apply, MonoidAlgebra.of_apply, adamsOp_single, pow_one, AlgHom.id_apply]
  · exact Subsingleton.elim _ _

theorem adamsOp_unit_mul [NeZero q] (d a : (ZMod q)ˣ) (v : MonoidAlgebra ℚ (Multiplicative (ZMod q))) :
    adamsOp q (d : ZMod q).val (adamsOp q (a : ZMod q).val v) = adamsOp q ((d * a : (ZMod q)ˣ) : ZMod q).val v := by
  rw [adamsOp_adamsOp]
  apply congrFun (congrArg _ (adamsOp_congr q ?_))
  push_cast
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, mul_comm]

variable (p : ℕ)

theorem exists_mem_not_isIntegral
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (B : Subalgebra R A)
    (hfg : B.FG) (hinf : ¬ (Subalgebra.toSubmodule B).FG) : ∃ b ∈ B, ¬ IsIntegral R b := by
  by_contra h
  push Not at h
  haveI : Algebra.FiniteType R ↥B := (Subalgebra.fg_iff_finiteType B).1 hfg
  haveI : Algebra.IsIntegral R ↥B :=
    ⟨fun x => (isIntegral_algHom_iff B.val Subtype.val_injective).1 (h x x.2)⟩
  have hfin : Module.Finite R ↥B := Algebra.IsIntegral.finite
  exact hinf (Module.Finite.iff_fg.1 hfin)

theorem exists_mem_forall_adamsOp_eq_not_isIntegral [hq : Fact q.Prime]
    {R : Type} [CommRing R] [Algebra R (MonoidAlgebra ℚ (Multiplicative (ZMod q)))]
    (B : Subalgebra R (MonoidAlgebra ℚ (Multiplicative (ZMod q))))
    (hadams : ∀ (c : (ZMod q)ˣ), ∀ b ∈ B, adamsOp q (c : ZMod q).val b ∈ B)
    (hlin : ∀ (c : (ZMod q)ˣ) (r : R) (v : MonoidAlgebra ℚ (Multiplicative (ZMod q))),
      adamsOp q (c : ZMod q).val (r • v) = r • adamsOp q (c : ZMod q).val v)
    (b : MonoidAlgebra ℚ (Multiplicative (ZMod q))) (hbB : b ∈ B) (hb : ¬ IsIntegral R b) :
    ∃ c ∈ B, (∀ d : (ZMod q)ˣ, adamsOp q (d : ZMod q).val c = c) ∧ ¬ IsIntegral R c := by
  classical
  haveI : Fact (1 < q) := ⟨hq.out.one_lt⟩

  let PB : Polynomial ↥B := ∏ a : (ZMod q)ˣ, (X - C ⟨adamsOp q (a : ZMod q).val b, hadams a b hbB⟩)
  let P : Polynomial (MonoidAlgebra ℚ (Multiplicative (ZMod q))) := PB.map (B.val : ↥B →+* _)
  have hP : P = ∏ a : (ZMod q)ˣ, (X - C (adamsOp q (a : ZMod q).val b)) := by
    simp only [P, PB, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    rfl
  have hPmonic : P.Monic := by
    rw [hP]; exact monic_prod_of_monic _ _ fun a _ => monic_X_sub_C _
  have hProot : P.eval b = 0 := by
    rw [hP, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ (1 : (ZMod q)ˣ))
    rw [eval_sub, eval_X, eval_C, Units.val_one, ZMod.val_one, adamsOp_one, sub_self]
  have hPcoeff : ∀ n, P.coeff n ∈ B := by
    intro n; rw [Polynomial.coeff_map]; exact (PB.coeff n).2

  have hPinv : ∀ (d : (ZMod q)ˣ) (n : ℕ), adamsOp q (d : ZMod q).val (P.coeff n) = P.coeff n := by
    intro d n
    have hmap : P.map (adamsOp q (d : ZMod q).val).toRingHom = P := by
      rw [hP, Polynomial.map_prod]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe]
      exact Fintype.prod_equiv (Equiv.mulLeft d) _ _ fun a => by
        simp only [Equiv.coe_mulLeft]
        rw [adamsOp_unit_mul]
    have := Polynomial.coeff_map ((adamsOp q (d : ZMod q).val).toRingHom) n (p := P)
    rw [hmap] at this
    exact this.symm

  have hnot : ∃ n, ¬ IsIntegral R (P.coeff n) := by
    by_contra hall
    push Not at hall
    apply hb

    let IC := integralClosure R (MonoidAlgebra ℚ (Multiplicative (ZMod q)))
    have hsub : (↑P.coeffs : Set (MonoidAlgebra ℚ (Multiplicative (ZMod q)))) ⊆
        (IC.toSubring : Set (MonoidAlgebra ℚ (Multiplicative (ZMod q)))) := by
      intro x hx
      obtain ⟨n, -, rfl⟩ := (Polynomial.mem_coeffs_iff).1 (Finset.mem_coe.1 hx)
      exact hall n
    let Q : Polynomial ↥IC.toSubring := P.toSubring IC.toSubring hsub
    have hQmap : Q.map (IC.toSubring.subtype) = P := Polynomial.map_toSubring _ _ _
    have hQmonic : Q.Monic := Polynomial.monic_toSubring _ _ _ |>.2 hPmonic
    have hbIC : IsIntegral ↥IC b := by
      refine ⟨Q, hQmonic, ?_⟩
      rw [Polynomial.eval₂_eq_eval_map]
      change (Q.map IC.toSubring.subtype).eval b = 0
      rw [hQmap, hProot]
    exact isIntegral_trans b hbIC
  obtain ⟨n, hn⟩ := hnot
  exact ⟨P.coeff n, hPcoeff n, fun d => hPinv d n, hn⟩

end ETP_INTEGRAL
p2m_reactivate "P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg.GaloisRep"

section ETP_MAIN
p2m_open "MonoidAlgebra P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg.MonoidAlgebra Polynomial GaloisRep P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg.GaloisRep"

variable (p q : ℕ)

theorem counit_algebraMap_add_smul_normElem [NeZero q] (α β : ℚ) :
    Coalgebra.counit (R := ℚ) (algebraMap ℚ (MonoidAlgebra ℚ (Multiplicative (ZMod q))) α +
      β • MonoidAlgebra.normElem ℚ (Multiplicative (ZMod q))) = α + β * q := by
  rw [map_add, Bialgebra.counit_algebraMap, map_smul, MonoidAlgebra.counit_normElem, Fintype.card_multiplicative,
    ZMod.card, smul_eq_mul]

theorem not_mem_ratLocalizedAt_of_not_isIntegral [Fact p.Prime] [NeZero q] {α β : ℚ}
    (hε : α + β * q ∈ ratLocalizedAt p)
    (hc : ¬ IsIntegral (ratLocalizedAt p) (algebraMap ℚ (MonoidAlgebra ℚ (Multiplicative (ZMod q))) α +
      β • MonoidAlgebra.normElem ℚ (Multiplicative (ZMod q)))) : α ∉ ratLocalizedAt p := by
  intro hα
  apply hc
  have hβq : β * q ∈ ratLocalizedAt p := by simpa using sub_mem hε hα
  refine IsIntegral.add ?_ ?_
  · rw [show algebraMap ℚ (MonoidAlgebra ℚ (Multiplicative (ZMod q))) α =
        algebraMap (ratLocalizedAt p) (MonoidAlgebra ℚ (Multiplicative (ZMod q))) ⟨α, hα⟩ from
      (IsScalarTower.algebraMap_apply (ratLocalizedAt p) ℚ _ ⟨α, hα⟩)]
    exact isIntegral_algebraMap
  ·
    set y := β • MonoidAlgebra.normElem ℚ (Multiplicative (ZMod q)) with hy
    have hyy : y * y = (β * q) • y := by
      rw [hy, smul_mul_smul_comm, MonoidAlgebra.normElem_mul_normElem, Fintype.card_multiplicative, ZMod.card,
        smul_smul, smul_smul]
      ring_nf
    refine ⟨X ^ 2 - C (⟨β * q, hβq⟩ : ratLocalizedAt p) * X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by
        refine (degree_C_mul_X_le _).trans_lt ?_
        exact_mod_cast Nat.lt_succ_self 1)
    · rw [eval₂_sub, eval₂_X_pow, eval₂_mul, eval₂_C, eval₂_X, pow_two, hyy,
        IsScalarTower.algebraMap_apply (ratLocalizedAt p) ℚ (MonoidAlgebra ℚ (Multiplicative (ZMod q))),
        ← Algebra.smul_def]
      change (β * q) • y - (((⟨β * q, hβq⟩ : ratLocalizedAt p) : ℚ)) • y = 0
      rw [sub_self]

theorem solution
    (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
    (B : Subalgebra (GaloisRep.ratLocalizedAt p) (MonoidAlgebra ℚ (Multiplicative (ZMod q))))
    (hfg : B.FG)
    (haug : ∀ b ∈ B, Coalgebra.counit (R := ℚ) b ∈ GaloisRep.ratLocalizedAt p)
    (hsat : ∀ v : MonoidAlgebra ℚ (Multiplicative (ZMod q)), ∃ n : ℕ, 0 < n ∧ (n : ℚ) • v ∈ B)
    (hadams : ∀ a : ℕ, a.Coprime q → ∀ b ∈ B,
      MonoidAlgebra.mapDomainAlgHom ℚ ℚ (powMonoidHom a) b ∈ B)
    (hinf : ¬ (Subalgebra.toSubmodule B).FG) :
    ∀ v : MonoidAlgebra ℚ (Multiplicative (ZMod q)),
      v ∈ B ↔ Coalgebra.counit (R := ℚ) v ∈ GaloisRep.ratLocalizedAt p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set s : MonoidAlgebra ℚ (Multiplicative (ZMod q)) := MonoidAlgebra.normElem ℚ (Multiplicative (ZMod q)) with hs
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero

  have hRsmul : ∀ (r : ratLocalizedAt p) (x : MonoidAlgebra ℚ (Multiplicative (ZMod q))), r • x = (r : ℚ) • x :=
    fun r x => rfl
  have hmemQ : ∀ (y : ℚ) (hy : y ∈ ratLocalizedAt p) (x : MonoidAlgebra ℚ (Multiplicative (ZMod q))),
      x ∈ B → y • x ∈ B := by
    intro y hy x hx
    have := B.smul_mem hx ⟨y, hy⟩
    rwa [hRsmul] at this

  obtain ⟨b, hbB, hb⟩ := exists_mem_not_isIntegral B hfg hinf
  have hadams' : ∀ c : (ZMod q)ˣ, ∀ b ∈ B, adamsOp q (c : ZMod q).val b ∈ B :=
    fun c b hb => hadams _ (ZMod.val_coe_unit_coprime c) b hb
  obtain ⟨c, hcB, hcinv, hcint⟩ :=
    exists_mem_forall_adamsOp_eq_not_isIntegral q B hadams' (fun c r v => by rw [hRsmul, hRsmul, map_smul]) b hbB hb
  obtain ⟨α, β, hαβ⟩ := exists_eq_algebraMap_add_smul_normElem_of_forall_adamsOp_eq q c hcinv
  have hεc : Coalgebra.counit (R := ℚ) c = α + β * q := by rw [hαβ, counit_algebraMap_add_smul_normElem]
  have hεcR : α + β * q ∈ ratLocalizedAt p := hεc ▸ haug c hcB
  have hα : α ∉ ratLocalizedAt p := not_mem_ratLocalizedAt_of_not_isIntegral p q hεcR (hαβ ▸ hcint)

  set e : MonoidAlgebra ℚ (Multiplicative (ZMod q)) := 1 - (q : ℚ)⁻¹ • s with he
  have hss : s * s = (q : ℚ) • s := by
    rw [hs, MonoidAlgebra.normElem_mul_normElem, Fintype.card_multiplicative, ZMod.card]
  have he2 : e * e = e := by
    rw [he, sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, smul_mul_smul_comm, hss, smul_smul,
      show (q : ℚ)⁻¹ * (q : ℚ)⁻¹ * (q : ℚ) = (q : ℚ)⁻¹ by field_simp, sub_self, sub_zero]
  have hepow : ∀ m : ℕ, e ^ (m + 1) = e := by
    intro m
    induction m with
    | zero => exact pow_one e
    | succ m ih => rw [pow_succ, ih, he2]
  set γ : ℚ := -(β * q) with hγ
  have hγR : γ ∉ ratLocalizedAt p := by
    intro hγR
    apply hα
    have : α = (α + β * q) + γ := by rw [hγ]; ring
    rw [this]
    exact add_mem hεcR hγR
  have hγe : γ • e ∈ B := by
    have h1 : c - algebraMap ℚ _ (Coalgebra.counit (R := ℚ) c) ∈ B := by
      refine B.sub_mem hcB ?_
      have := B.algebraMap_mem ⟨_, haug c hcB⟩
      rwa [IsScalarTower.algebraMap_apply (ratLocalizedAt p) ℚ (MonoidAlgebra ℚ (Multiplicative (ZMod q)))] at this
    have h2 : c - algebraMap ℚ _ (Coalgebra.counit (R := ℚ) c) = γ • e := by
      rw [hεc, hαβ, he, hγ, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul,
        show -(β * (q : ℚ)) * (q : ℚ)⁻¹ = -β by field_simp, add_smul, neg_smul, neg_smul, sub_neg_eq_add]
      abel
    rwa [h2] at h1

  obtain ⟨k, w, hk, hw, hwγ⟩ := exists_mul_eq_inv_pow_of_notMem (p := p) hγR
  have hpk : ((p : ℚ)⁻¹) ^ k • e ∈ B := by
    have := hmemQ w hw _ hγe
    rwa [smul_smul, hwγ] at this
  have hf : (p : ℚ)⁻¹ • e ∈ B := by
    have := hmemQ ((p : ℚ) ^ (k - 1)) (by exact_mod_cast natCast_mem_ratLocalizedAt (p := p) (p ^ (k - 1))) _ hpk
    rwa [smul_smul, show (p : ℚ) ^ (k - 1) * ((p : ℚ)⁻¹) ^ k = (p : ℚ)⁻¹ from by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      rw [Nat.succ_sub_one, pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hp0, one_pow, one_mul]] at this

  have hpn : ∀ n : ℕ, ((p : ℚ)⁻¹) ^ n • e ∈ B := by
    intro n
    cases n with
    | zero =>
      have := hmemQ (p : ℚ) (by exact_mod_cast natCast_mem_ratLocalizedAt (p := p) p) _ hf
      rw [pow_zero]
      rwa [smul_smul, mul_inv_cancel₀ hp0] at this
    | succ n =>
      have := B.pow_mem hf (n + 1)
      rwa [_root_.smul_pow, hepow] at this
  have hQe : ∀ y : ℚ, y • e ∈ B := by
    intro y
    obtain ⟨n, r, hr, rfl⟩ := exists_mem_mul_inv_pow_eq (p := p) y
    rw [← smul_smul]
    exact hmemQ r hr _ (hpn n)

  have hker : ∀ v : MonoidAlgebra ℚ (Multiplicative (ZMod q)), Coalgebra.counit (R := ℚ) v = 0 → v ∈ B := by
    intro v hv
    obtain ⟨n, hn, hnv⟩ := hsat v
    have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have hvs : v * s = Coalgebra.counit (R := ℚ) v • s := by
      rw [hs]; exact MonoidAlgebra.mul_normElem_eq_counit_smul ℚ _ v
    have hve : v * e = v := by
      rw [he, mul_sub, mul_one, mul_smul_comm, hvs, hv, zero_smul, smul_zero, sub_zero]
    have : (n : ℚ) • v * ((n : ℚ)⁻¹ • e) ∈ B := B.mul_mem hnv (hQe _)
    rwa [smul_mul_smul_comm, mul_inv_cancel₀ hn0, one_smul, hve] at this

  intro v
  refine ⟨haug v, fun hv => ?_⟩
  have h1 : algebraMap ℚ (MonoidAlgebra ℚ (Multiplicative (ZMod q))) (Coalgebra.counit (R := ℚ) v) ∈ B := by
    have := B.algebraMap_mem ⟨_, hv⟩
    rwa [IsScalarTower.algebraMap_apply (ratLocalizedAt p) ℚ (MonoidAlgebra ℚ (Multiplicative (ZMod q)))] at this
  have h2 : v - algebraMap ℚ (MonoidAlgebra ℚ (Multiplicative (ZMod q))) (Coalgebra.counit (R := ℚ) v) ∈ B :=
    hker _ (by rw [map_sub, Bialgebra.counit_algebraMap, sub_self])
  have := B.add_mem h1 h2
  rwa [add_sub_cancel] at this

end ETP_MAIN
p2m_reactivate "P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg.GaloisRep"

end S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg
end P2MW
export P2MW.S_MonoidAlgebra_mem_iff_counit_mem_ratLocalizedAt_of_mapDomain_pow_mem_of_not_fg (solution)
