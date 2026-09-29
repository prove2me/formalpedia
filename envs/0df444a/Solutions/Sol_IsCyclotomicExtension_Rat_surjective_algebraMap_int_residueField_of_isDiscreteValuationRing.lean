-- Prove2me | solution 1 for IsCyclotomicExtension.Rat.surjective_algebraMap_int_residueField_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c59c8fcb-eead-5155-8b79-3e8902e28b32

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsCyclotomicExtension_Rat_surjective_algebraMap_int_residueField_of_isDiscreteValuationRing

set_option autoImplicit false

open IsLocalRing

namespace CycDVRAux

section Overring

variable {V K : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]

theorem subring_eq_top_of_inv_mem (W : Subring K) (hVW : ∀ v : V, algebraMap V K v ∈ W)
    {ϖ : V} (hϖ : Irreducible ϖ) (hinv : (algebraMap V K ϖ)⁻¹ ∈ W) : W = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  by_cases hy : y = 0
  · rw [hy]; exact W.zero_mem
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hy
  rw [Units.smul_def, Algebra.smul_def]
  refine W.mul_mem (hVW _) ?_
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [zpow_natCast, ← map_pow]; exact hVW _
  · have hn : n < 0 := lt_of_not_ge hn
    obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn.le
    rw [zpow_neg, zpow_natCast, ← inv_pow]; exact W.pow_mem hinv m

theorem exists_algebraMap_eq_of_mem_subring (W : Subring K) (hVW : ∀ v : V, algebraMap V K v ∈ W)
    (hW : W ≠ ⊤) {x : K} (hx : x ∈ W) : ∃ v : V, algebraMap V K v = x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  by_cases hx0 : x = 0
  · exact ⟨0, by rw [map_zero, hx0]⟩
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ hx0
  have hinj := IsFractionRing.injective V K
  have hπ : algebraMap V K ϖ ≠ 0 := (map_ne_zero_iff _ hinj).mpr hϖ.ne_zero
  have hu : algebraMap V K u ≠ 0 := (map_ne_zero_iff _ hinj).mpr u.ne_zero
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact ⟨u * ϖ ^ m, by rw [map_mul, map_pow, Units.smul_def, Algebra.smul_def, zpow_natCast]⟩
  · exfalso
    have hn : n < 0 := lt_of_not_ge hn
    obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hn.le
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 :=
      Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hn)
    refine hW (subring_eq_top_of_inv_mem W hVW hϖ ?_)
    have key : (algebraMap V K ϖ)⁻¹ =
        (u • algebraMap V K ϖ ^ (-((k + 1 : ℕ) : ℤ))) * algebraMap V K (↑u⁻¹ * ϖ ^ k) := by
      rw [Units.smul_def, Algebra.smul_def, map_mul, map_pow, zpow_neg, zpow_natCast, map_units_inv]
      field_simp
      ring
    rw [key]
    exact W.mul_mem hx (hVW _)

end Overring

section Lift

variable {A L : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field L] [Algebra A L]
  [IsFractionRing A L]

omit [IsDomain A] in
theorem exists_algebraMap_eq_of_isIntegral_int {x : L} (hx : IsIntegral ℤ x) :
    ∃ a : A, algebraMap A L a = x :=
  IsIntegrallyClosed.algebraMap_eq_of_integral
    (hx.map_of_comp_eq (algebraMap ℤ A) (RingHom.id L) (Subsingleton.elim _ _))

variable {B : Type*} [CommRing B] [Algebra B L] (hB : ∀ b : B, IsIntegral ℤ (algebraMap B L b))

noncomputable def liftHom : B →+* A where
  toFun b := (exists_algebraMap_eq_of_isIntegral_int (A := A) (hB b)).choose
  map_one' := IsFractionRing.injective A L (by
    rw [(exists_algebraMap_eq_of_isIntegral_int (A := A) (hB 1)).choose_spec, map_one, map_one])
  map_mul' x y := IsFractionRing.injective A L (by
    rw [(exists_algebraMap_eq_of_isIntegral_int (A := A) (hB _)).choose_spec, map_mul, map_mul,
      (exists_algebraMap_eq_of_isIntegral_int (A := A) (hB x)).choose_spec,
      (exists_algebraMap_eq_of_isIntegral_int (A := A) (hB y)).choose_spec])
  map_zero' := IsFractionRing.injective A L (by
    rw [(exists_algebraMap_eq_of_isIntegral_int (A := A) (hB 0)).choose_spec, map_zero, map_zero])
  map_add' x y := IsFractionRing.injective A L (by
    rw [(exists_algebraMap_eq_of_isIntegral_int (A := A) (hB _)).choose_spec, map_add, map_add,
      (exists_algebraMap_eq_of_isIntegral_int (A := A) (hB x)).choose_spec,
      (exists_algebraMap_eq_of_isIntegral_int (A := A) (hB y)).choose_spec])

omit [IsDomain A] in
theorem algebraMap_liftHom (b : B) : algebraMap A L (liftHom (A := A) hB b) = algebraMap B L b :=
  (exists_algebraMap_eq_of_isIntegral_int (A := A) (hB b)).choose_spec

end Lift

theorem isUnit_of_not_dvd {p : ℕ} (hp : p.Prime) {A : Type*} [CommRing A] [IsLocalRing A]
    (hAp : (p : A) ∈ maximalIdeal A) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) : IsUnit ((n : ℤ) : A) := by
  by_contra hnu
  have hmem : ((n : ℤ) : A) ∈ maximalIdeal A := (mem_maximalIdeal _).mpr hnu
  have hcop : IsCoprime n (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : Int.gcd n p ∣ p := by exact_mod_cast Int.gcd_dvd_right n p
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact h
    · exfalso; apply hn
      have := Int.gcd_dvd_left n p
      rw [h] at this
      exact_mod_cast this
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : ((u * n + v * p : ℤ) : A) = 1 := by rw [huv, Int.cast_one]
  apply (maximalIdeal.isMaximal A).ne_top
  rw [Ideal.eq_top_iff_one, ← h1]
  push_cast
  exact add_mem (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ (by exact_mod_cast hAp))

section Cyc

open NumberField

variable (p : ℕ) [hp : Fact p.Prime] (L : Type) [Field L] [NumberField L] [hL : IsCyclotomicExtension {p} ℚ L]
  (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]

noncomputable def φ : 𝓞 L →+* A :=
  liftHom (A := A) (L := L) (B := 𝓞 L) RingOfIntegers.isIntegral_coe

omit [NumberField L] in
theorem algebraMap_φ (x : 𝓞 L) : algebraMap A L (φ L A x) = (x : L) :=
  algebraMap_liftHom (A := A) _ x

noncomputable def 𝔮 : Ideal (𝓞 L) := (maximalIdeal A).comap (φ L A)

scoped instance : (𝔮 L A).IsPrime := Ideal.comap_isPrime _ _

omit [NumberField L] in
theorem isUnit_φ {s : 𝓞 L} (hs : s ∉ 𝔮 L A) : IsUnit (φ L A s) := by
  by_contra h
  exact hs ((mem_maximalIdeal _).mpr h)

scoped instance isPrime_span_p : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp.out)

theorem isMaximal_span_p : (Ideal.span {(p : ℤ)}).IsMaximal :=
  (isPrime_span_p p).isMaximal (by simpa using hp.out.ne_zero)

variable (hAp : (p : A) ∈ maximalIdeal A)
include hAp

omit hp [NumberField L] hL in
theorem p_mem_𝔮 : (p : 𝓞 L) ∈ 𝔮 L A := by
  change φ L A p ∈ maximalIdeal A
  rwa [map_natCast]

omit [NumberField L] hL in
theorem liesOver : (𝔮 L A).LiesOver (Ideal.span {(p : ℤ)}) := by
  refine ⟨(isMaximal_span_p p).eq_of_le ?_ ?_⟩
  · exact Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top inferInstance)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change algebraMap ℤ (𝓞 L) p ∈ 𝔮 L A
    rw [map_natCast]
    exact p_mem_𝔮 p L A hAp

theorem 𝔮_eq_span :
    𝔮 L A = Ideal.span {(IsCyclotomicExtension.zeta_spec p ℚ L).toInteger - 1} := by
  haveI := liesOver p L A hAp
  exact IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' p L
    (IsCyclotomicExtension.zeta_spec p ℚ L) _

omit hL in
theorem 𝔮_ne_bot : 𝔮 L A ≠ ⊥ := by
  intro h
  have := p_mem_𝔮 p L A hAp
  rw [h, Ideal.mem_bot] at this
  exact hp.out.ne_zero (by exact_mod_cast this)

theorem eq_𝔮_of_isPrime (P : Ideal (𝓞 L)) [P.IsPrime] (hP : (p : 𝓞 L) ∈ P) : P = 𝔮 L A := by
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    refine ⟨(isMaximal_span_p p).eq_of_le ?_ ?_⟩
    · exact Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top inferInstance)
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      change algebraMap ℤ (𝓞 L) p ∈ P
      rwa [map_natCast]
  rw [𝔮_eq_span p L A hAp]
  exact IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver' p L
    (IsCyclotomicExtension.zeta_spec p ℚ L) _

omit hL in

theorem exists_eq_div (a : A) :
    ∃ x s : 𝓞 L, s ∉ 𝔮 L A ∧ algebraMap A L a = (x : L) * ((s : L))⁻¹ := by
  let W : Subring L := (algebraMap A L).range
  let V := Localization.subalgebra.ofField L (𝔮 L A).primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _)
  haveI : IsDiscreteValuationRing V :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 L) (𝔮_ne_bot p L A hAp) V
  have hVW : ∀ v : V, algebraMap V L v ∈ W := by
    rintro ⟨v, x, s, hs, rfl⟩
    refine W.mul_mem ⟨φ L A x, algebraMap_φ L A x⟩ ?_
    obtain ⟨u, hu⟩ := isUnit_φ L A hs
    refine ⟨↑u⁻¹, ?_⟩
    rw [map_units_inv, hu, algebraMap_φ]
  have hW : W ≠ ⊤ := by
    intro h
    have : ((p : L))⁻¹ ∈ W := h ▸ Subring.mem_top _
    obtain ⟨a, ha⟩ := this
    have : a * p = 1 := IsFractionRing.injective A L (by
      rw [map_mul, map_natCast, ha, map_one, inv_mul_cancel₀]
      exact_mod_cast hp.out.ne_zero)
    exact (mem_maximalIdeal _).mp hAp ⟨⟨(p : A), a, by rw [mul_comm]; exact this, this⟩, rfl⟩
  obtain ⟨⟨v, x, s, hs, rfl⟩, hv⟩ :=
    exists_algebraMap_eq_of_mem_subring (V := V) (K := L) W hVW hW (x := algebraMap A L a) ⟨a, rfl⟩
  exact ⟨x, s, hs, hv.symm⟩

theorem not_dvd_absNorm {s : 𝓞 L} (hs : s ∉ 𝔮 L A) : ¬ p ∣ Ideal.absNorm (Ideal.span {s}) := by
  intro h
  obtain ⟨P, hPmax, hPunder, hPdvd⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp.out _ h
  haveI := hPmax.isPrime
  have hpP : (p : 𝓞 L) ∈ P := by
    have : (p : ℤ) ∈ P.under ℤ := hPunder ▸ Ideal.mem_span_singleton_self _
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast] at this
    exact this
  rw [eq_𝔮_of_isPrime p L A hAp P hpP] at hPdvd
  exact hs (Ideal.dvd_iff_le.mp hPdvd (Ideal.mem_span_singleton_self s))

theorem exists_int_sub_mem (z : 𝓞 L) : ∃ k : ℤ, z - k ∈ 𝔮 L A := by
  haveI := liesOver p L A hAp
  haveI := isMaximal_span_p p
  letI := Ideal.Quotient.field (Ideal.span {(p : ℤ)})
  have h1 := IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime p L (𝔮 L A)
  haveI : (𝔮 L A).IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (𝔮 L A) (Ideal.span {(p : ℤ)})
  rw [Ideal.inertiaDeg_eq_of_isMaximal (Ideal.span {(p : ℤ)}) (𝔮 L A)] at h1
  obtain ⟨-, hsurj⟩ := Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h1
  obtain ⟨c, hc⟩ := hsurj (Ideal.Quotient.mk (𝔮 L A) z)
  obtain ⟨k, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨k, ?_⟩
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver] at hc
  simpa using Ideal.Quotient.eq.mp hc.symm

end Cyc

section MainB

open NumberField

theorem surjective_algebraMap_int_residueField
    (p : ℕ) [hp : Fact p.Prime] (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ maximalIdeal A) :
    Function.Surjective (algebraMap ℤ (IsLocalRing.ResidueField A)) := by
  haveI := IsCyclotomicExtension.numberField {p} ℚ L
  intro r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  obtain ⟨x, s, hs, hx⟩ := exists_eq_div p L A hAp a
  have hs0 : (s : L) ≠ 0 := by
    have : s ≠ 0 := by rintro rfl; exact hs (zero_mem _)
    exact_mod_cast this
  have h1 : a * φ L A s = φ L A x := IsFractionRing.injective A L (by
    rw [map_mul, algebraMap_φ, algebraMap_φ, hx, inv_mul_cancel_right₀ hs0])
  obtain ⟨m, hm⟩ := exists_int_sub_mem p L A hAp x
  obtain ⟨n, hn⟩ := exists_int_sub_mem p L A hAp s
  have hres : ∀ (z : 𝓞 L) (k : ℤ), z - k ∈ 𝔮 L A →
      IsLocalRing.residue A (φ L A z) = (k : IsLocalRing.ResidueField A) := by
    intro z k hzk
    have : φ L A z - φ L A k ∈ maximalIdeal A := by
      have := hzk
      rw [𝔮, Ideal.mem_comap, map_sub] at this
      exact this
    rw [map_intCast, ← Ideal.Quotient.eq] at this
    rw [IsLocalRing.residue_def, this, map_intCast]
    rfl
  have hn' : ¬ (p : ℤ) ∣ n := by
    rintro ⟨k, rfl⟩
    apply hs
    have : s = (s - ((p * k : ℤ) : 𝓞 L)) + (p : 𝓞 L) * k := by push_cast; ring
    rw [this]
    exact add_mem hn (Ideal.mul_mem_right _ _ (p_mem_𝔮 p L A hAp))
  have hcop : IsCoprime n (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h1 : Int.gcd n p ∣ p := by exact_mod_cast Int.gcd_dvd_right n p
    rcases (Nat.dvd_prime hp.out).mp h1 with h | h
    · exact h
    · exfalso; apply hn'
      have := Int.gcd_dvd_left n p
      rw [h] at this
      exact_mod_cast this
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨m * u, ?_⟩
  have hp0 : IsLocalRing.residue A (p : A) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hAp
  have e1 : IsLocalRing.residue A a * (n : IsLocalRing.ResidueField A) = m := by
    rw [← hres s n hn, ← hres x m hm, ← map_mul, h1]
  have e2 : (n : IsLocalRing.ResidueField A) * u = 1 - v * p := by
    have : ((u * n + v * p : ℤ) : IsLocalRing.ResidueField A) = 1 := by rw [huv, Int.cast_one]
    push_cast at this
    linear_combination this
  have hp0' : (p : IsLocalRing.ResidueField A) = 0 := by
    rw [← hp0, map_natCast]
  rw [hp0', mul_zero, sub_zero] at e2
  calc algebraMap ℤ (IsLocalRing.ResidueField A) (m * u)
      = (m : IsLocalRing.ResidueField A) * u := by simp
    _ = IsLocalRing.residue A a * ((n : IsLocalRing.ResidueField A) * u) := by rw [← mul_assoc, e1]
    _ = IsLocalRing.residue A a := by rw [e2, mul_one]

end MainB

end CycDVRAux
p2m_reactivate "P2MW.S_IsCyclotomicExtension_Rat_surjective_algebraMap_int_residueField_of_isDiscreteValuationRing.CycDVRAux"

theorem solution
    (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) :
    Function.Surjective (algebraMap ℤ (IsLocalRing.ResidueField A)) :=
  CycDVRAux.surjective_algebraMap_int_residueField p L A hAp

end S_IsCyclotomicExtension_Rat_surjective_algebraMap_int_residueField_of_isDiscreteValuationRing
end P2MW
export P2MW.S_IsCyclotomicExtension_Rat_surjective_algebraMap_int_residueField_of_isDiscreteValuationRing (solution)
