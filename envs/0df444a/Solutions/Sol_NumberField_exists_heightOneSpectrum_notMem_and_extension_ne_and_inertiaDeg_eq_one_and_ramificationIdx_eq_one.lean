-- Prove2me | solution 1 for NumberField.exists_heightOneSpectrum_notMem_and_extension_ne_and_inertiaDeg_eq_one_and_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/19976f12-e448-5537-9d51-c19dd40617d2

import Definitions.Def_DedekindDomain_IntegralClosure
import Theorems.Thm_CommRing_infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_heightOneSpectrum_notMem_and_extension_ne_and_inertiaDeg_eq_one_and_ramificationIdx_eq_one
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "NumberField P2MW.S_NumberField_exists_heightOneSpectrum_notMem_and_extension_ne_and_inertiaDeg_eq_one_and_ramificationIdx_eq_one.NumberField IsDedekindDomain"

namespace NumberField
p2m_export "NumberField" "mk place"
namespace DegreeOnePlace
p2m_open "NumberField"

open scoped Classical

variable (K : Type) [Field K] [NumberField K]

private noncomputable def ramQ : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  (Ideal.finite_factors (I := differentIdeal (𝓞 ℚ) (𝓞 K)) differentIdeal_ne_bot).toFinset.image
    (fun 𝔓 : HeightOneSpectrum (𝓞 K) => 𝔓.under (𝓞 ℚ))

variable {K}

private theorem ramificationIdx_eq_one_of_under_notMem_ramQ (𝔓 : HeightOneSpectrum (𝓞 K))
    (h : 𝔓.under (𝓞 ℚ) ∉ ramQ K) :
    Ideal.ramificationIdx' (𝔓.under (𝓞 ℚ)).asIdeal 𝔓.asIdeal = 1 := by
  haveI : Algebra.IsUnramifiedAt (𝓞 ℚ) 𝔓.asIdeal := by
    refine (not_dvd_differentIdeal_iff (A := 𝓞 ℚ) (B := 𝓞 K)).mp ?_
    intro hdvd
    apply h
    unfold ramQ
    refine Finset.mem_image.mpr ⟨𝔓, ?_, rfl⟩
    simpa using hdvd
  haveI : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 ℚ)).asIdeal := ⟨rfl⟩
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (𝔓.under (𝓞 ℚ)).ne_bot]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 ℚ) (p := 𝔓.asIdeal)

private theorem natCast_mem_asIdeal_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((n : 𝓞 ℚ)) ∈ v.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator v ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    show ((n : ℕ) : ℤ) = Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) ((n : 𝓞 ℚ)) from (map_natCast _ n).symm]
  exact Ideal.apply_mem_of_equiv_iff.symm

private theorem natGenerator_eq_of_natCast_mem (v : HeightOneSpectrum (𝓞 ℚ)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : ((ℓ : 𝓞 ℚ)) ∈ v.asIdeal) : Rat.HeightOneSpectrum.natGenerator v = ℓ :=
  (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hℓ).mp
    ((natCast_mem_asIdeal_iff v ℓ).mp h)

private noncomputable def kerPlace {ℓ : ℕ} [Fact ℓ.Prime] (φ : 𝓞 K →+* ZMod ℓ) : HeightOneSpectrum (𝓞 K) where
  asIdeal := RingHom.ker φ
  isPrime := RingHom.ker_isPrime φ
  ne_bot h := by
    have hmem : ((ℓ : 𝓞 K)) ∈ RingHom.ker φ := by rw [RingHom.mem_ker, map_natCast, ZMod.natCast_self]
    rw [h, Ideal.mem_bot] at hmem
    exact (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero) hmem

private theorem kerPlace_asIdeal {ℓ : ℕ} [Fact ℓ.Prime] (φ : 𝓞 K →+* ZMod ℓ) :
    (kerPlace φ).asIdeal = RingHom.ker φ := rfl

private theorem inertiaDeg_kerPlace {ℓ : ℕ} [Fact ℓ.Prime] (φ : 𝓞 K →+* ZMod ℓ) :
    ((kerPlace φ).under (𝓞 ℚ)).asIdeal.inertiaDeg' (kerPlace φ).asIdeal = 1 := by
  haveI : (kerPlace φ).asIdeal.LiesOver ((kerPlace φ).under (𝓞 ℚ)).asIdeal := ⟨rfl⟩
  haveI : ((kerPlace φ).under (𝓞 ℚ)).asIdeal.IsMaximal :=
    ((kerPlace φ).under (𝓞 ℚ)).isPrime.isMaximal ((kerPlace φ).under (𝓞 ℚ)).ne_bot
  haveI : (kerPlace φ).asIdeal.IsMaximal := (kerPlace φ).isPrime.isMaximal (kerPlace φ).ne_bot
  rw [Ideal.inertiaDeg_algebraMap]
  apply Module.finrank_of_bijective_algebraMap
  refine ⟨FaithfulSMul.algebraMap_injective _ _, ?_⟩
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨Ideal.Quotient.mk _ (((φ y).val : ℕ) : 𝓞 ℚ), ?_⟩
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver, map_natCast, Ideal.Quotient.eq, kerPlace_asIdeal, RingHom.mem_ker, map_sub,
    map_natCast, ZMod.natCast_zmod_val, sub_self]

variable (K) in
private theorem main (hK : 2 ≤ Module.finrank ℚ K) (F : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    ∃ (p₀ : HeightOneSpectrum (𝓞 ℚ)) (w₀ w₂ : p₀.Extension (𝓞 K)),
      p₀ ∉ F ∧ w₀.1 ≠ w₂.1 ∧
      p₀.asIdeal.inertiaDeg' w₀.1.asIdeal = 1 ∧
      ∀ w : p₀.Extension (𝓞 K), Ideal.ramificationIdx' p₀.asIdeal w.1.asIdeal = 1 := by

  obtain ⟨ℓ, ⟨hℓ, ⟨φ⟩⟩, hℓB⟩ :=
    (CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int (𝓞 K)).exists_notMem_finset
      ((F ∪ ramQ K).image Rat.HeightOneSpectrum.natGenerator)
  haveI : Fact ℓ.Prime := ⟨hℓ⟩

  refine ⟨(kerPlace φ).under (𝓞 ℚ), ⟨kerPlace φ, rfl⟩, ?_⟩
  have hℓp : ((ℓ : 𝓞 ℚ)) ∈ ((kerPlace φ).under (𝓞 ℚ)).asIdeal := by
    change algebraMap (𝓞 ℚ) (𝓞 K) ℓ ∈ RingHom.ker φ
    rw [map_natCast, RingHom.mem_ker, map_natCast, ZMod.natCast_self]
  have hgen : Rat.HeightOneSpectrum.natGenerator ((kerPlace φ).under (𝓞 ℚ)) = ℓ :=
    natGenerator_eq_of_natCast_mem _ hℓ hℓp
  have hp₀ : (kerPlace φ).under (𝓞 ℚ) ∉ F ∪ ramQ K := fun h => hℓB (Finset.mem_image.mpr ⟨_, h, hgen⟩)
  have hp₀F : (kerPlace φ).under (𝓞 ℚ) ∉ F := fun h => hp₀ (Finset.mem_union_left _ h)
  have hp₀R : (kerPlace φ).under (𝓞 ℚ) ∉ ramQ K := fun h => hp₀ (Finset.mem_union_right _ h)

  have hram : ∀ w : ((kerPlace φ).under (𝓞 ℚ)).Extension (𝓞 K),
      Ideal.ramificationIdx' ((kerPlace φ).under (𝓞 ℚ)).asIdeal w.1.asIdeal = 1 := by
    intro w
    have h := ramificationIdx_eq_one_of_under_notMem_ramQ w.1 (by rw [w.2]; exact hp₀R)
    rwa [w.2] at h

  have hf := inertiaDeg_kerPlace φ

  haveI : ((kerPlace φ).under (𝓞 ℚ)).asIdeal.IsMaximal :=
    ((kerPlace φ).under (𝓞 ℚ)).isPrime.isMaximal ((kerPlace φ).under (𝓞 ℚ)).ne_bot
  have hsum := Ideal.sum_ramification_inertia (R := 𝓞 ℚ) (𝓞 K) ℚ K
    (p := ((kerPlace φ).under (𝓞 ℚ)).asIdeal) ((kerPlace φ).under (𝓞 ℚ)).ne_bot
  have hw₀mem : (kerPlace φ).asIdeal ∈ IsDedekindDomain.primesOverFinset ((kerPlace φ).under (𝓞 ℚ)).asIdeal (𝓞 K) :=
    (IsDedekindDomain.mem_primesOverFinset_iff ((kerPlace φ).under (𝓞 ℚ)).ne_bot _).mpr
      ⟨(kerPlace φ).isPrime, ⟨rfl⟩⟩
  obtain ⟨P, hP, hPne⟩ : ∃ P ∈ IsDedekindDomain.primesOverFinset ((kerPlace φ).under (𝓞 ℚ)).asIdeal (𝓞 K),
      P ≠ (kerPlace φ).asIdeal := by
    by_contra hcon
    have hsing : IsDedekindDomain.primesOverFinset ((kerPlace φ).under (𝓞 ℚ)).asIdeal (𝓞 K) = {(kerPlace φ).asIdeal} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hw₀mem, fun P hP => ?_⟩
      by_contra hne
      exact hcon ⟨P, hP, hne⟩
    rw [hsing, Finset.sum_singleton, hram ⟨kerPlace φ, rfl⟩, hf] at hsum
    omega
  obtain ⟨hPprime, hPover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff ((kerPlace φ).under (𝓞 ℚ)).ne_bot _).mp hP
  haveI := hPprime
  haveI := hPover
  let w₂ : HeightOneSpectrum (𝓞 K) :=
    ⟨P, hPprime, Ideal.ne_bot_of_liesOver_of_ne_bot ((kerPlace φ).under (𝓞 ℚ)).ne_bot P⟩
  have hw₂ : w₂.under (𝓞 ℚ) = (kerPlace φ).under (𝓞 ℚ) := HeightOneSpectrum.ext hPover.over.symm
  exact ⟨⟨w₂, hw₂⟩, hp₀F, fun h => hPne (congrArg HeightOneSpectrum.asIdeal h).symm, hf, hram⟩

end NumberField.DegreeOnePlace

theorem solution
    (K : Type) [Field K] [NumberField K] (hK : 2 ≤ Module.finrank ℚ K)
    (F : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))) :
    ∃ (p₀ : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (w₀ w₂ : p₀.Extension (𝓞 K)),
      p₀ ∉ F ∧ w₀.1 ≠ w₂.1 ∧
      p₀.asIdeal.inertiaDeg' w₀.1.asIdeal = 1 ∧
      ∀ w : p₀.Extension (𝓞 K), Ideal.ramificationIdx' p₀.asIdeal w.1.asIdeal = 1 :=
  NumberField.DegreeOnePlace.main K hK F

end S_NumberField_exists_heightOneSpectrum_notMem_and_extension_ne_and_inertiaDeg_eq_one_and_ramificationIdx_eq_one
end P2MW
export P2MW.S_NumberField_exists_heightOneSpectrum_notMem_and_extension_ne_and_inertiaDeg_eq_one_and_ramificationIdx_eq_one (solution)
