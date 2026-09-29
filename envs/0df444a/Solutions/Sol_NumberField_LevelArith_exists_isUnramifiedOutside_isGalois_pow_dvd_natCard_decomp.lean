-- Prove2me | solution 1 for NumberField.LevelArith.exists_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bed7edd6-0c2b-57ad-b330-362bb9798a94

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Theorems.Thm_NumberField_exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp
import Theorems.Thm_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower
import Theorems.Thm_NumberField_LevelArith_isGalois_levelField
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_sup_adjoin_simple_of_pow_mem
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

namespace N6A

theorem mem_and_inv_mem_of_pow_eq_one {K : Type*} [Field K] (A : ValuationSubring K) {u : K} {m : ℕ}
    (hm : m ≠ 0) (hu : u ^ m = 1) : u ∈ A ∧ u⁻¹ ∈ A := by
  have key : ∀ w : K, w ^ m = 1 → w ∈ A → w⁻¹ ∈ A := by
    intro w hw hwA
    have h : w⁻¹ = w ^ (m - 1) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm), hw]
    rw [h]
    exact pow_mem hwA _
  rcases A.mem_or_inv_mem u with h | h
  · exact ⟨h, key u hu h⟩
  · have hu' : u⁻¹ ^ m = 1 := by rw [inv_pow, hu, inv_one]
    have := key u⁻¹ hu' h
    rw [inv_inv] at this
    exact ⟨this, h⟩

theorem exists_le_isUnramifiedOutside_forall_pow_eq_one_mem (S : Finset Nat.Primes) {p : ℕ} (hp : p.Prime)
    (hpS : (⟨p, hp⟩ : Nat.Primes) ∈ S) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S)
    (n : ℕ) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), L ≤ F ∧ F.IsUnramifiedOutside S ∧
      ∀ z : AlgebraicClosure ℚ, z ^ (p ^ n) = 1 → z ∈ F := by
  classical
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩

  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (p ^ n)
  have hζpow : ζ ^ (p ^ n) = 1 := hζ.pow_eq_one

  have step : ∀ j : ℕ, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), L ≤ F ∧ F.IsUnramifiedOutside S ∧
      ζ ^ (p ^ (n - j)) ∈ F := by
    intro j
    induction j with
    | zero => exact ⟨L, le_rfl, hL, by rw [Nat.sub_zero, hζpow]; exact one_mem _⟩
    | succ j ih =>
      obtain ⟨F, hLF, hF, hζF⟩ := ih
      set α : AlgebraicClosure ℚ := ζ ^ (p ^ (n - (j + 1))) with hα

      have hαp : α ^ p ∈ F := by
        rw [hα, ← pow_mul]
        rcases Nat.lt_or_ge j n with hjn | hjn
        · have : p ^ (n - (j + 1)) * p = p ^ (n - j) := by
            rw [← pow_succ]
            congr 1
            omega
          rw [this]
          exact hζF
        · have h1 : n - (j + 1) = 0 := by omega
          have h2 : n - j = 0 := by omega
          rw [h2, pow_zero, pow_one] at hζF
          rw [h1, pow_zero, one_mul]
          exact pow_mem hζF _

      have hαS : ∀ A : ValuationSubring (AlgebraicClosure ℚ),
          (∀ q ∈ S, ¬ A.LiesOverPrime ((q : Nat.Primes) : ℕ)) → α ^ p ∈ A ∧ (α ^ p)⁻¹ ∈ A := by
        intro A _
        apply mem_and_inv_mem_of_pow_eq_one A (NeZero.ne (p ^ n))
        have : (α ^ p) ^ (p ^ n) = (ζ ^ (p ^ n)) ^ (p ^ (n - (j + 1)) * p) := by
          rw [hα]; ring
        rw [this, hζpow, one_pow]
      refine ⟨F ⊔ IntermediateField.adjoin ℚ {α}, hLF.trans le_sup_left,
        IntermediateField.IsUnramifiedOutside.sup_adjoin_simple_of_pow_mem S hp hpS hF hαp hαS, ?_⟩
      exact (le_sup_right : IntermediateField.adjoin ℚ {α} ≤ F ⊔ IntermediateField.adjoin ℚ {α})
        (IntermediateField.mem_adjoin_simple_self ℚ α)
  obtain ⟨F, hLF, hF, hζF⟩ := step n
  rw [Nat.sub_self, pow_zero, pow_one] at hζF
  refine ⟨F, hLF, hF, fun z hz => ?_⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hz
  exact pow_mem hζF i

end N6A

set_option maxHeartbeats 4000000 in

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L] (k : ℕ) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) (_ : F.IsUnramifiedOutside S) (_ : IsGalois ℚ ↥F),
      ∀ [FiniteDimensional ℚ ↥F] (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥(levelField L F hLF))),
        w ∈ placesOverPrimes ↥(levelField L F hLF) (S : Set Nat.Primes) →
        p ^ k ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w) := by
  classical
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

  obtain ⟨n, F', iF, iNF, iAlg, iGal, icyc, ⟨φ⟩, hinf, hcard, hdec, hpg⟩ :=
    NumberField.exists_isCyclic_algHom_cyclotomicField_pow_dvd_natCard_decomp ↥L (placesOverPrimesFinset ↥L S) p k

  haveI : Algebra.IsAlgebraic ↥L (CyclotomicField (p ^ n) ↥L) := inferInstance
  let ψ : CyclotomicField (p ^ n) ↥L →ₐ[↥L] AlgebraicClosure ℚ := IsAlgClosed.lift
  let ι : F' →ₐ[↥L] AlgebraicClosure ℚ := ψ.comp φ

  obtain ⟨F₁, hLF₁, hF₁S, hroots⟩ :=
    N6A.exists_le_isUnramifiedOutside_forall_pow_eq_one_mem S (Fact.out : p.Prime) hpS L hL n
  haveI : FiniteDimensional ℚ ↥F₁ := hF₁S.1

  have hιF₁ : ∀ x : F', ι x ∈ F₁ := by
    intro x

    have htop := ((IsCyclotomicExtension.iff_adjoin_eq_top {p ^ n} ↥L (CyclotomicField (p ^ n) ↥L)).1
      inferInstance).2
    have hmem : φ x ∈ Algebra.adjoin ↥L
        {b : CyclotomicField (p ^ n) ↥L | ∃ m ∈ ({p ^ n} : Set ℕ), m ≠ 0 ∧ b ^ m = 1} := by
      rw [htop]; exact Algebra.mem_top

    have : ι x ∈ (Algebra.adjoin ↥L
        {b : CyclotomicField (p ^ n) ↥L | ∃ m ∈ ({p ^ n} : Set ℕ), m ≠ 0 ∧ b ^ m = 1}).map ψ :=
      Subalgebra.mem_map.2 ⟨φ x, hmem, rfl⟩
    rw [AlgHom.map_adjoin] at this

    let F₁' : Subalgebra ↥L (AlgebraicClosure ℚ) := (IntermediateField.extendScalars hLF₁).toSubalgebra
    have hle : Algebra.adjoin ↥L
        (ψ '' {b : CyclotomicField (p ^ n) ↥L | ∃ m ∈ ({p ^ n} : Set ℕ), m ≠ 0 ∧ b ^ m = 1}) ≤ F₁' := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨b, ⟨m, hm, -, hb⟩, rfl⟩
      rw [Set.mem_singleton_iff] at hm
      subst hm
      refine (IntermediateField.mem_extendScalars hLF₁).2 (hroots _ ?_)
      rw [← map_pow, hb, map_one]
    exact (IntermediateField.mem_extendScalars hLF₁).1 (hle this)

  set F := IntermediateField.normalClosure ℚ F₁ (AlgebraicClosure ℚ) with hFdef
  have hF₁F : F₁ ≤ F := IntermediateField.le_normalClosure F₁
  have hLF : L ≤ F := hLF₁.trans hF₁F
  have hFS : F.IsUnramifiedOutside S := hF₁S.normalClosure
  haveI hfdF : FiniteDimensional ℚ ↥F := hFS.1
  haveI : Normal ℚ ↥F := normalClosure.normal ℚ ↥F₁ (AlgebraicClosure ℚ)
  haveI hgalF : IsGalois ℚ ↥F := ⟨⟩
  refine ⟨F, hLF, hFS, hgalF, ?_⟩
  intro _inst w hw

  have hιF : ∀ x : F', ι x ∈ levelField L F hLF := fun x =>
    (IntermediateField.mem_extendScalars hLF).2 (hF₁F (hιF₁ x))
  let ιK : F' →+* ↥(levelField L F hLF) := (ι : F' →+* AlgebraicClosure ℚ).codRestrict _ hιF
  letI : Algebra F' ↥(levelField L F hLF) := ιK.toAlgebra
  haveI : IsScalarTower ↥L F' ↥(levelField L F hLF) :=
    IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext (by
      show ((algebraMap ↥L ↥(levelField L F hLF) x : ↥(levelField L F hLF)) : AlgebraicClosure ℚ) = ι (algebraMap ↥L F' x)
      rw [AlgHom.commutes]; rfl))
  haveI : IsGalois ↥L ↥(levelField L F hLF) := NumberField.LevelArith.isGalois_levelField L F hLF
  haveI : Normal ↥L F' := iGal.to_normal
  obtain ⟨r, hr, -⟩ := NumberField.PlaceDecomp.exists_restrict_decomp_surjective_of_tower ↥L F' ↥(levelField L F hLF) w

  have hv : (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers F') w).under (NumberField.RingOfIntegers ↥L) ∈ placesOverPrimesFinset ↥L S := by
    obtain ⟨q, hqS, hq⟩ := hw
    rw [placesOverPrimesFinset, Set.Finite.mem_toFinset]
    refine ⟨q, hqS, ?_⟩
    show ((q : ℕ) : NumberField.RingOfIntegers ↥L) ∈ Ideal.comap (algebraMap (NumberField.RingOfIntegers ↥L) (NumberField.RingOfIntegers F'))
      (Ideal.comap (algebraMap (NumberField.RingOfIntegers F') (NumberField.RingOfIntegers ↥(levelField L F hLF))) w.asIdeal)
    rw [Ideal.mem_comap, map_natCast, Ideal.mem_comap, map_natCast]
    exact hq
  have h0 := hdec _ hv (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers F') w) rfl
  exact h0.trans (Subgroup.card_dvd_of_surjective r hr)

end S_NumberField_LevelArith_exists_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp
end P2MW
export P2MW.S_NumberField_LevelArith_exists_isUnramifiedOutside_isGalois_pow_dvd_natCard_decomp (solution)
