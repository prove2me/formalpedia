-- Prove2me | solution 1 for Module.free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d88fc413-b6e8-5ed4-8e72-a3d01e2318f5

import Mathlib
import Theorems.Thm_RingTheory_Sequence_IsWeaklyRegular_isZero_tor_one_quotient_ofList
import Theorems.Thm_Module_flat_of_isLocalHom_of_finite_of_isZero_tor_one_residueField
import Theorems.Thm_IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes
import Theorems.Thm_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing RingTheory.Sequence

namespace P2Free

theorem two_le_height_of_under_eq_maximalIdeal
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : ringKrullDim R = 2)
    (B : Type u) [CommRing B] [IsDomain B] [Algebra R B] [Module.Finite R B] [FaithfulSMul R B]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q.under R = maximalIdeal R) : (2 : ℕ∞) ≤ Q.height := by
  have hh : (maximalIdeal R).height = 2 := by
    have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [hdim] at this
    have this' : ((maximalIdeal R).height : WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := by rw [this]; rfl
    exact WithBot.coe_injective this'
  obtain ⟨l, hlast, hlen⟩ := Ideal.exists_ltSeries_length_eq_height (maximalIdeal R)
  haveI : Q.LiesOver l.last.asIdeal := by rw [hlast]; exact ⟨hQ.symm⟩
  obtain ⟨L, hLlen, hLlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l Q
  have h1 : (L.length : ℕ∞) ≤ Order.height L.last := Order.length_le_height_last
  rw [hLlast, ← PrimeSpectrum.height_eq_orderHeight, hLlen] at h1
  have h2 : (l.length : ℕ∞) = 2 := by rw [← hh]; exact_mod_cast hlen
  calc (2 : ℕ∞) = l.length := h2.symm
    _ ≤ Q.height := h1

theorem mem_span_of_mul_mem_span
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : ringKrullDim R = 2)
    (B : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra R B] [Module.Finite R B]
    [FaithfulSMul R B]
    (a b : R) (ha : a ≠ 0) (hab : maximalIdeal R ≤ Ideal.span {a, b})
    (m : B) (hm : algebraMap R B b * m ∈ Ideal.span {algebraMap R B a}) :
    m ∈ Ideal.span {algebraMap R B a} := by
  classical
  haveI : IsNoetherianRing B := isNoetherian_of_tower R (inferInstance : IsNoetherian R B)
  set I : Ideal B := Ideal.span {algebraMap R B a} with hI
  have haB : algebraMap R B a ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R B)).mpr ha
  by_contra hmI
  have hne : (Ideal.Quotient.mk I m) ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hkill : algebraMap R B b • (Ideal.Quotient.mk I m) = 0 := by
    change Ideal.Quotient.mk I (algebraMap R B b • m) = 0
    rw [smul_eq_mul, Ideal.Quotient.eq_zero_iff_mem]; exact hm
  have hmemU : algebraMap R B b ∈ ⋃ p ∈ associatedPrimes B (B ⧸ I), (p : Set B) := by
    rw [biUnion_associatedPrimes_eq_zero_divisors]
    exact ⟨_, hne, hkill⟩
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hmemU
  obtain ⟨Q, hQass, hbQ⟩ := hmemU
  have hQ' : IsAssociatedPrime Q (B ⧸ I) := hQass
  haveI hQp : Q.IsPrime := hQ'.isPrime

  have haQ : algebraMap R B a ∈ Q := by
    obtain ⟨-, z, hz⟩ := hQ'
    rw [hz]
    refine Ideal.le_radical ?_
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    obtain ⟨z', rfl⟩ := Ideal.Quotient.mk_surjective z
    change Ideal.Quotient.mk I (algebraMap R B a • z') = 0
    rw [smul_eq_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

  have hunder : Q.under R = maximalIdeal R := by
    apply le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
    refine hab.trans ?_
    rw [Ideal.span_le]
    rintro r (rfl | rfl)
    · exact haQ
    · simpa using hbQ

  have h1 : Q.height = 1 := IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes haB Q hQass
  have h2 := two_le_height_of_under_eq_maximalIdeal R hdim B Q hunder
  rw [h1] at h2
  exact absurd h2 (by decide)

end P2Free

open P2Free in

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsRegularLocalRing R] (hdim : ringKrullDim R ≤ 2)
    (B : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra R B] [Module.Finite R B]
    [FaithfulSMul R B] :
    Module.Free R B := by
  classical
  haveI : UniqueFactorizationMonoid R := IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two R hdim
  haveI : IsIntegrallyClosed R := inferInstance
  have hinj : Function.Injective (algebraMap R B) := FaithfulSMul.algebraMap_injective R B

  obtain ⟨s, hscard, hsspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank (IsNoetherian.noetherian (maximalIdeal R))
  have hsf : ((s.card : ℕ) : WithBot ℕ∞) = ringKrullDim R := by
    rw [hscard]; exact IsRegularLocalRing.spanFinrank_maximalIdeal
  have hcard : s.card ≤ 2 := by
    have : ((s.card : ℕ) : WithBot ℕ∞) ≤ 2 := hsf ▸ hdim
    exact_mod_cast this

  have hreg : ∀ r : R, r ≠ 0 → IsSMulRegular B r := fun r hr m m' h => by
    have h' : algebraMap R B r * m = algebraMap R B r * m' := by simpa [Algebra.smul_def] using h
    exact mul_left_cancel₀ ((map_ne_zero_iff _ hinj).mpr hr) h'

  have key : ∃ rs : List R, Ideal.ofList rs = maximalIdeal R ∧ IsWeaklyRegular B rs := by
    have hspan' : ∀ l : List R, l = s.toList → Ideal.ofList l = maximalIdeal R := by
      rintro l rfl
      rw [← hsspan]
      change Ideal.span {r | r ∈ s.toList} = Ideal.span (s : Set R)
      congr 1
      ext r; simp
    have hlen : s.toList.length ≤ 2 := by rw [Finset.length_toList]; exact hcard

    have hmin : ∀ t : Finset R, Ideal.span (t : Set R) = maximalIdeal R → s.card ≤ t.card := by
      intro t ht
      rw [hscard]
      have := Submodule.spanFinrank_span_le_ncard_of_finite (R := R) (M := R) (Finset.finite_toSet t)
      rw [Set.ncard_coe_finset] at this
      change (Ideal.span (t : Set R)).spanFinrank ≤ t.card at this
      rwa [ht] at this
    have hcardlen : s.card = s.toList.length := (Finset.length_toList s).symm
    match hl : s.toList with
    | [] => exact ⟨[], hspan' [] hl.symm, IsWeaklyRegular.nil R B⟩
    | [x] =>
      refine ⟨[x], hspan' _ hl.symm, ?_⟩
      rw [isWeaklyRegular_cons_iff]
      refine ⟨hreg x ?_, IsWeaklyRegular.nil R _⟩
      rintro rfl
      have h0 := hspan' _ hl.symm
      have hbot : Ideal.span ((∅ : Finset R) : Set R) = maximalIdeal R := by
        rw [← h0, Finset.coe_empty, Ideal.span_empty, Ideal.ofList_singleton, Ideal.span_singleton_eq_bot.mpr rfl]
      have := hmin ∅ hbot
      rw [hcardlen, hl] at this
      simp at this
    | [x, y] =>
      have hxy := hspan' _ hl.symm
      have hset : ({r | r ∈ [x, y]} : Set R) = {x, y} := by ext r; simp
      have hab : maximalIdeal R ≤ Ideal.span {x, y} := by
        rw [← hxy]; change Ideal.span {r | r ∈ [x, y]} ≤ _; rw [hset]
      have hdim2 : ringKrullDim R = 2 := by
        rw [← hsf, hcardlen, hl]; rfl
      have hx : x ≠ 0 := by
        rintro rfl
        have h1 : Ideal.span (({y} : Finset R) : Set R) = maximalIdeal R := by
          apply le_antisymm
          · rw [Ideal.span_le, Finset.coe_singleton, Set.singleton_subset_iff, SetLike.mem_coe, ← hxy]
            exact Ideal.subset_span (by simp)
          · refine hab.trans ?_
            rw [Ideal.span_le]
            rintro r (rfl | rfl)
            · exact Ideal.zero_mem _
            · exact Ideal.subset_span (by simp)
        have := hmin {y} h1
        rw [hcardlen, hl] at this
        simp at this
      refine ⟨[x, y], hxy, ?_⟩
      rw [isWeaklyRegular_cons_iff, isWeaklyRegular_cons_iff]
      refine ⟨hreg x hx, ?_, IsWeaklyRegular.nil R _⟩

      have aux : ∀ q : QuotSMulTop x B, y • q = 0 → q = 0 := by
        intro q hq
        obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
          Submodule.mem_smul_pointwise_iff_exists] at hq
        obtain ⟨c, -, hc⟩ := hq
        have hm : algebraMap R B y * m ∈ Ideal.span {algebraMap R B x} := by
          rw [← Algebra.smul_def, ← hc, Algebra.smul_def]
          exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
        have hm' := mem_span_of_mul_mem_span R hdim2 B x y hx hab m hm
        rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
        obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp hm'
        exact ⟨c', Submodule.mem_top, by rw [Algebra.smul_def, ← hc', mul_comm]⟩
      intro q q' h
      have h' : y • (q - q') = 0 := by rw [smul_sub]; exact sub_eq_zero.mpr h
      exact sub_eq_zero.mp (aux _ h')
    | _ :: _ :: _ :: _ => rw [hl] at hlen; simp at hlen
  obtain ⟨rs, hrs, hwr⟩ := key

  have htor := IsWeaklyRegular.isZero_tor_one_quotient_ofList hwr
  let e : ModuleCat.of R (R ⧸ Ideal.ofList rs) ≅ ModuleCat.of R (ResidueField R) :=
    (Ideal.quotientEquivAlgOfEq R hrs).toLinearEquiv.toModuleIso
  have htor' : IsZero (((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R (ResidueField R))).obj
      (ModuleCat.of R B)) :=
    IsZero.of_iso htor (((Tor (ModuleCat.{u} R) 1).mapIso e).app (ModuleCat.of R B)).symm
  haveI : IsLocalHom (algebraMap R R) := ⟨fun _ h => h⟩
  haveI : Module.Flat R B :=
    Module.flat_of_isLocalHom_of_finite_of_isZero_tor_one_residueField (S := R) (M := B) htor'
  exact Module.free_of_flat_of_isLocalRing

end S_Module_free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two
end P2MW
export P2MW.S_Module_free_of_isIntegrallyClosed_of_finite_of_isRegularLocalRing_of_ringKrullDim_le_two (solution)
