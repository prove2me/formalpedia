-- Prove2me | solution 1 for ModularCurve.IgusaScheme.aeval_notMem_of_mem_minimalPrimes_span_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/528f3879-04e2-5a3b-8a17-e9fa53410ed1

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_aeval_notMem_of_mem_minimalPrimes_span_natCast

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open ModularCurve ModularCurve.IgusaScheme Polynomial

namespace IgusaGoingDown

section Base

variable (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => (↥(GaloisRep.ratLocalizedAt ℓ) : Type)

scoped instance span_int_isPrime : (Ideal.span {(ℓ : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp Fact.out)

scoped instance dvr : IsDiscreteValuationRing ℤℓ :=
  GaloisRep.isDiscreteValuationRing_ratLocalizedAt ℓ Fact.out

scoped instance isLoc : IsLocalization.AtPrime ℤℓ (Ideal.span {(ℓ : ℤ)}) :=
  GaloisRep.isLocalization_ratLocalizedAt (p := ℓ) Fact.out

def φ : ℤℓ →+* ZMod ℓ :=
  IsLocalization.lift (M := (Ideal.span {(ℓ : ℤ)}).primeCompl) (S := ℤℓ)
    (g := Int.castRingHom (ZMod ℓ)) (by
      rintro ⟨z, hz⟩
      have hz0 : (z : ZMod ℓ) ≠ 0 := by
        intro h
        apply hz
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
        exact Ideal.mem_span_singleton.mpr h
      exact isUnit_iff_ne_zero.mpr hz0)

theorem φ_intCast (z : ℤ) : φ ℓ (z : ℤℓ) = (z : ZMod ℓ) := map_intCast _ z

theorem φ_natCast_self : φ ℓ (ℓ : ℤℓ) = 0 := by rw [map_natCast, ZMod.natCast_self]

theorem prime_ell : Prime ((ℓ : ℕ) : ℤℓ) :=
  (GaloisRep.irreducible_natCast_ratLocalizedAt ℓ Fact.out).prime

theorem map_eq_zero_of_C_dvd (P : ℤ[X]) (h : C ((ℓ : ℕ) : ℤℓ) ∣ P.map (algebraMap ℤ ℤℓ)) :
    P.map (Int.castRingHom (ZMod ℓ)) = 0 := by
  rw [Polynomial.C_dvd_iff_dvd_coeff] at h
  ext i
  rw [coeff_map, coeff_zero, eq_intCast, ← φ_intCast ℓ]
  obtain ⟨c, hc⟩ := h i
  rw [coeff_map, eq_intCast] at hc
  rw [hc, map_mul, φ_natCast_self, zero_mul]

end Base

section Chart

variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => (↥(GaloisRep.ratLocalizedAt ℓ) : Type)
set_option quotPrecheck false in
local notation "F" => (↥(modularFunctionFieldFull N) : Type)

variable (y : ↥(modularFunctionFieldFull N)) (hy : Transcendental ℚ y)

set_option quotPrecheck false in
local notation "𝒪" => chartAlg N ℓ ({y} : Set F)
set_option quotPrecheck false in
local notation "Rz" => Algebra.adjoin ℤℓ ({y} : Set F)

include hy in
theorem transcendental_int : Transcendental ℤℓ y :=
  hy.restrictScalars (R := ℤℓ) (S := ℚ) Subtype.val_injective

include hy in
theorem aeval_injective : Function.Injective (aeval y : ℤℓ[X] →ₐ[ℤℓ] F) :=
  transcendental_iff_injective.mp (transcendental_int N ℓ y hy)

def polyEquiv : ℤℓ[X] ≃ₐ[ℤℓ] Rz :=
  (AlgEquiv.ofInjective (aeval y) (aeval_injective N ℓ y hy)).trans
    (Subalgebra.equivOfEq _ _ (Algebra.adjoin_singleton_eq_range_aeval ℤℓ y).symm)

theorem coe_polyEquiv (P : ℤℓ[X]) : ((polyEquiv N ℓ y hy P : Rz) : F) = aeval y P := rfl

theorem polyEquiv_C_ell : polyEquiv N ℓ y hy (C ((ℓ : ℕ) : ℤℓ)) = ((ℓ : ℕ) : Rz) := by
  apply Subtype.ext
  rw [coe_polyEquiv, aeval_C, map_natCast]
  simp

include hy in
theorem isIntegrallyClosed_adjoin : IsIntegrallyClosed Rz := by
  haveI : IsIntegrallyClosed ℤℓ := inferInstance
  exact IsIntegrallyClosed.of_equiv (polyEquiv N ℓ y hy).toRingEquiv

def inclRO : (↥(Rz) : Type) →+* (↥(𝒪) : Type) :=
  (Subalgebra.inclusion (adjoin_le_chartAlg N ℓ ({y} : Set F))).toRingHom

@[reducible] def algRO : Algebra (↥(Rz) : Type) (↥(𝒪) : Type) := (inclRO N ℓ y).toAlgebra

attribute [local instance] algRO

theorem coe_algebraMap_RO (r : Rz) :
    ((algebraMap (↥(Rz) : Type) (↥(𝒪) : Type) r : 𝒪) : F) = (r : F) :=
  rfl

theorem towerRO : IsScalarTower (↥(Rz) : Type) (↥(𝒪) : Type) F :=
  IsScalarTower.of_algebraMap_eq (R := (↥(Rz) : Type)) (S := (↥(𝒪) : Type)) (A := F) (fun _ => rfl)

attribute [local instance] towerRO

theorem isIntegralRO : Algebra.IsIntegral (↥(Rz) : Type) (↥(𝒪) : Type) :=
  ⟨fun x => (isIntegral_algHom_iff (IsScalarTower.toAlgHom (↥(Rz) : Type) (↥(𝒪) : Type) F)
    Subtype.val_injective).mp ((mem_chartAlg_iff N ℓ).mp x.2)⟩

theorem faithfulRO : FaithfulSMul (↥(Rz) : Type) (↥(𝒪) : Type) :=
  (faithfulSMul_iff_algebraMap_injective (↥(Rz) : Type) (↥(𝒪) : Type)).mpr
    (Subalgebra.inclusion_injective _)

include hy in
theorem hasGoingDownRO : Algebra.HasGoingDown (↥(Rz) : Type) (↥(𝒪) : Type) := by
  haveI := isIntegralRO N ℓ y
  haveI := faithfulRO N ℓ y
  haveI : IsIntegrallyClosed Rz := isIntegrallyClosed_adjoin N ℓ y hy
  infer_instance

abbrev qEll : Ideal Rz := Ideal.span {((ℓ : ℕ) : Rz)}

theorem qEll_eq_map :
    qEll N ℓ y = (Ideal.span {C ((ℓ : ℕ) : ℤℓ)}).map (polyEquiv N ℓ y hy) := by
  rw [Ideal.map_span, Set.image_singleton, polyEquiv_C_ell]

include hy in
theorem qEll_isPrime : (qEll N ℓ y).IsPrime := by
  rw [qEll_eq_map N ℓ y hy]
  haveI : (Ideal.span {C ((ℓ : ℕ) : ℤℓ)}).IsPrime :=
    (Ideal.span_singleton_prime (by
      intro h
      exact (prime_ell ℓ).ne_zero (Polynomial.C_eq_zero.mp h))).mpr
      ((Polynomial.prime_C_iff).mpr (prime_ell ℓ))
  exact Ideal.map_isPrime_of_equiv _

def rP (P : ℤ[X]) : Rz := polyEquiv N ℓ y hy (P.map (algebraMap ℤ ℤℓ))

theorem rP_mem_qEll_iff (P : ℤ[X]) :
    rP N ℓ y hy P ∈ qEll N ℓ y ↔ C ((ℓ : ℕ) : ℤℓ) ∣ P.map (algebraMap ℤ ℤℓ) := by
  rw [Ideal.mem_span_singleton, ← polyEquiv_C_ell N ℓ y hy, rP]
  exact map_dvd_iff (polyEquiv N ℓ y hy)

theorem algebraMap_rP (P : ℤ[X]) :
    algebraMap (↥(Rz) : Type) (↥(𝒪) : Type) (rP N ℓ y hy P) =
      Polynomial.aeval (⟨y, subset_chartAlg N ℓ _ (Set.mem_singleton y)⟩ : 𝒪) P := by
  apply Subtype.ext
  rw [coe_algebraMap_RO, rP, coe_polyEquiv, aeval_map_algebraMap]
  have := Polynomial.aeval_algHom_apply
    ((chartAlg N ℓ ({y} : Set F)).val.toRingHom.toIntAlgHom)
    (⟨y, subset_chartAlg N ℓ _ (Set.mem_singleton y)⟩ : 𝒪) P
  exact this

include hy in

theorem main (𝔭 : Ideal 𝒪) (h𝔭 : 𝔭 ∈ (Ideal.span {((ℓ : ℕ) : 𝒪)}).minimalPrimes)
    (P : ℤ[X]) (hP : P.map (Int.castRingHom (ZMod ℓ)) ≠ 0) :
    Polynomial.aeval (⟨y, subset_chartAlg N ℓ _ (Set.mem_singleton y)⟩ : 𝒪) P ∉ 𝔭 := by
  intro hmem
  haveI : 𝔭.IsPrime := h𝔭.1.1
  haveI := hasGoingDownRO N ℓ y hy
  haveI := qEll_isPrime N ℓ y hy
  have hℓ𝔭 : ((ℓ : ℕ) : 𝒪) ∈ 𝔭 := h𝔭.1.2 (Ideal.subset_span rfl)
  set 𝔮 : Ideal Rz := 𝔭.under Rz with h𝔮
  have hle : qEll N ℓ y ≤ 𝔮 := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, h𝔮, Ideal.mem_comap, map_natCast]
    exact hℓ𝔭
  have hr𝔮 : rP N ℓ y hy P ∈ 𝔮 := by
    rw [h𝔮, Ideal.mem_comap, algebraMap_rP]
    exact hmem
  have hrq : rP N ℓ y hy P ∉ qEll N ℓ y := fun h =>
    hP (map_eq_zero_of_C_dvd ℓ P ((rP_mem_qEll_iff N ℓ y hy P).mp h))
  have hlt : qEll N ℓ y < 𝔮 := lt_of_le_of_ne hle (fun h => hrq (h ▸ hr𝔮))
  obtain ⟨P', hP'lt, hP'prime, hP'over⟩ :=
    Ideal.exists_ideal_lt_liesOver_of_lt (p := qEll N ℓ y) (q := 𝔮) 𝔭 hlt
  have hℓP' : ((ℓ : ℕ) : 𝒪) ∈ P' := by
    have h1 : ((ℓ : ℕ) : Rz) ∈ qEll N ℓ y := Ideal.subset_span rfl
    have h2 := (P'.mem_of_liesOver (qEll N ℓ y) ((ℓ : ℕ) : Rz)).mp h1
    rwa [map_natCast] at h2
  have hspan : Ideal.span {((ℓ : ℕ) : 𝒪)} ≤ P' := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hℓP'
  exact (lt_irrefl 𝔭) (lt_of_le_of_lt (h𝔭.2 ⟨hP'prime, hspan⟩ hP'lt.le) hP'lt)

end Chart

end IgusaGoingDown
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_aeval_notMem_of_mem_minimalPrimes_span_natCast.IgusaGoingDown"

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_aeval_notMem_of_mem_minimalPrimes_span_natCast.IgusaGoingDown"

open ModularCurve ModularCurve.IgusaScheme in
theorem solution
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (y : ↥(modularFunctionFieldFull N)) (hy : Transcendental ℚ y)
    (𝔭 : Ideal ↥(chartAlg N ℓ ({y} : Set ↥(modularFunctionFieldFull N))))
    (h𝔭 : 𝔭 ∈ (Ideal.span
      {((ℓ : ℕ) : ↥(chartAlg N ℓ ({y} : Set ↥(modularFunctionFieldFull N))))}).minimalPrimes)
    (P : Polynomial ℤ) (hP : P.map (Int.castRingHom (ZMod ℓ)) ≠ 0) :
    Polynomial.aeval (⟨y, subset_chartAlg N ℓ _ (Set.mem_singleton y)⟩ :
        ↥(chartAlg N ℓ ({y} : Set ↥(modularFunctionFieldFull N)))) P ∉ 𝔭 :=
  IgusaGoingDown.main N ℓ y hy 𝔭 h𝔭 P hP

end S_ModularCurve_IgusaScheme_aeval_notMem_of_mem_minimalPrimes_span_natCast
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_aeval_notMem_of_mem_minimalPrimes_span_natCast (solution)
