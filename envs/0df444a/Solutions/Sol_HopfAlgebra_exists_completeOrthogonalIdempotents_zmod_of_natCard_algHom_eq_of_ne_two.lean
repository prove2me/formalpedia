-- Prove2me | solution 1 for HopfAlgebra.exists_completeOrthogonalIdempotents_zmod_of_natCard_algHom_eq_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c76a16a2-2c2b-5099-ae42-e78a649d59c1

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_mem_ratLocalizedAt_iff
import Theorems.Thm_HopfAlgebra_isUnit_withConv_algHom
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_HopfAlgebra_rational_separating_dense_algHom_algebraicClosure_of_forall_ringEquiv_apply_eq
import Theorems.Thm_HopfAlgebra_ringHom_ratLocalizedAt_eq_of_forall_sub_mem_span_of_natCard_algHom_eq_of_ne_two
import Theorems.Thm_RingHom_existsUnique_apply_eq_of_completeOrthogonalIdempotents_of_corner_denominators
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_completeOrthogonalIdempotents_zmod_of_natCard_algHom_eq_of_ne_two

open scoped TensorProduct

namespace P2mOddConstSplit

noncomputable section

open scoped Classical

def intAlgHom {R S : Type*} [Ring R] [Ring S] [Algebra ℤ R] [Algebra ℤ S] (g : R →+* S) :
    R →ₐ[ℤ] S :=
  { g with
    commutes' := fun r => by
      rw [Subsingleton.elim (algebraMap ℤ R) (Int.castRingHom R),
        Subsingleton.elim (algebraMap ℤ S) (Int.castRingHom S)]
      simp }

@[scoped simp] theorem intAlgHom_apply {R S : Type*} [Ring R] [Ring S] [Algebra ℤ R] [Algebra ℤ S]
    (g : R →+* S) (x : R) : intAlgHom g x = g x := rfl

section Engine

variable {K : Type} [CommRing K] [HopfAlgebra ℤ K]

abbrev L : Type := AlgebraicClosure ℚ

variable (K) in

abbrev Pt : Type := K →ₐ[ℤ] L

section Rational

variable (hrat : ∀ (ψ : Pt K) (k : K), ∃ r : ℚ, ψ k = algebraMap ℚ L r)

def ψ₀ (ψ : Pt K) : K →+* ℚ where
  toFun k := (hrat ψ k).choose
  map_one' := (algebraMap ℚ L).injective (by rw [← (hrat ψ 1).choose_spec, map_one, map_one])
  map_mul' a b := (algebraMap ℚ L).injective (by
    rw [← (hrat ψ (a * b)).choose_spec, map_mul, map_mul, ← (hrat ψ a).choose_spec,
      ← (hrat ψ b).choose_spec])
  map_zero' := (algebraMap ℚ L).injective (by rw [← (hrat ψ 0).choose_spec, map_zero, map_zero])
  map_add' a b := (algebraMap ℚ L).injective (by
    rw [← (hrat ψ (a + b)).choose_spec, map_add, map_add, ← (hrat ψ a).choose_spec,
      ← (hrat ψ b).choose_spec])

theorem algebraMap_ψ₀ (ψ : Pt K) (k : K) : algebraMap ℚ L (ψ₀ hrat ψ k) = ψ k :=
  (hrat ψ k).choose_spec.symm

theorem ψ₀_intCast (ψ : Pt K) (n : ℤ) : ψ₀ hrat ψ (n : K) = n := map_intCast _ n

theorem eq_of_ψ₀_eq {ψ ψ' : Pt K} (h : ψ₀ hrat ψ = ψ₀ hrat ψ') : ψ = ψ' := by
  refine AlgHom.ext fun k => ?_
  rw [← algebraMap_ψ₀ hrat ψ, ← algebraMap_ψ₀ hrat ψ', h]

variable (hsep : ∀ k k' : K, (∀ ψ : Pt K, ψ k = ψ k') → k = k')

include hsep in

theorem sep₀ {k k' : K} (h : ∀ ψ : Pt K, ψ₀ hrat ψ k = ψ₀ hrat ψ k') : k = k' :=
  hsep k k' fun ψ => by rw [← algebraMap_ψ₀ hrat, ← algebraMap_ψ₀ hrat, h]

variable (hdense : ∀ c : Pt K → ℤ, ∃ (k : K) (N : ℕ), 0 < N ∧
  ∀ ψ : Pt K, ψ k = ((N : ℤ) * c ψ : ℤ))

include hdense in

theorem exists_numerator (ψ : Pt K) :
    ∃ (x : K) (N : ℕ), 0 < N ∧ ∀ ψ' : Pt K, ψ₀ hrat ψ' x = if ψ' = ψ then (N : ℚ) else 0 := by
  obtain ⟨x, N, hN, hx⟩ := hdense (fun ψ' => if ψ' = ψ then 1 else 0)
  refine ⟨x, N, hN, fun ψ' => (algebraMap ℚ L).injective ?_⟩
  rw [algebraMap_ψ₀, hx]
  split_ifs <;> simp

def P (ψ : Pt K) : Ideal K := RingHom.ker (ψ₀ hrat ψ)

theorem mem_P {ψ : Pt K} {k : K} : k ∈ P hrat ψ ↔ ψ₀ hrat ψ k = 0 := RingHom.mem_ker

theorem exists_ψ₀_eq_inv_den (ψ : Pt K) (k : K) :
    ∃ k₁ : K, ψ₀ hrat ψ k₁ = ((ψ₀ hrat ψ k).den : ℚ)⁻¹ := by
  set r := ψ₀ hrat ψ k with hr
  have hcop : IsCoprime r.num (r.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact r.reduced
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨(a : K) * k + (b : K), ?_⟩
  rw [map_add, map_mul, ψ₀_intCast, ψ₀_intCast, ← hr]
  have key : ((a : ℚ) * r + b) * r.den = 1 := by
    rw [add_mul, mul_assoc, Rat.mul_den_eq_num]
    exact_mod_cast hab
  exact (inv_eq_of_mul_eq_one_left key).symm

theorem exists_ψ₀_eq_inv (ψ : Pt K) {ℓ : ℕ} {k : K} (hk : ℓ ∣ (ψ₀ hrat ψ k).den) :
    ∃ y : K, ψ₀ hrat ψ y = (ℓ : ℚ)⁻¹ := by
  obtain ⟨k₁, hk₁⟩ := exists_ψ₀_eq_inv_den hrat ψ k
  obtain ⟨d, hd⟩ := hk
  refine ⟨(d : K) * k₁, ?_⟩
  have hden : ((ψ₀ hrat ψ k).den : ℚ) ≠ 0 := by exact_mod_cast (ψ₀ hrat ψ k).den_ne_zero
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by
    rintro h
    apply hden
    rw [hd]; push_cast; rw [h, zero_mul]
  have hd0 : (d : ℚ) ≠ 0 := by
    rintro h
    apply hden
    rw [hd]; push_cast; rw [h, mul_zero]
  rw [map_mul, map_natCast, hk₁, hd]
  push_cast
  field_simp

theorem not_dvd_den_of_le (ψ : Pt K) {ℓ : ℕ} {m : Ideal K} (hm : m ≠ ⊤) (hℓm : (ℓ : K) ∈ m)
    (hP : P hrat ψ ≤ m) (k : K) : ¬ ℓ ∣ (ψ₀ hrat ψ k).den := by
  intro hdvd
  obtain ⟨y, hy⟩ := exists_ψ₀_eq_inv hrat ψ hdvd
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by
    intro h
    have h0 : ℓ = 0 := by exact_mod_cast h
    subst h0
    rw [zero_dvd_iff] at hdvd
    exact (ψ₀ hrat ψ k).den_ne_zero hdvd
  apply hm
  rw [Ideal.eq_top_iff_one]
  have h1 : (ℓ : K) * y - 1 ∈ P hrat ψ := by
    rw [mem_P, map_sub, map_mul, map_natCast, hy, mul_inv_cancel₀ hℓ0, map_one, sub_self]
  have h2 : (ℓ : K) * y ∈ m := m.mul_mem_right _ hℓm
  have := m.sub_mem h2 (hP h1)
  rwa [sub_sub_cancel] at this

def ψℓ (ψ : Pt K) (ℓ : ℕ) (hℓ : ℓ.Prime) (hint : ∀ k, ¬ ℓ ∣ (ψ₀ hrat ψ k).den) :
    K →+* GaloisRep.ratLocalizedAt ℓ :=
  (ψ₀ hrat ψ).codRestrict _ fun k => (GaloisRep.mem_ratLocalizedAt_iff hℓ _).mpr (hint k)

@[scoped simp] theorem ψℓ_apply (ψ : Pt K) (ℓ : ℕ) (hℓ : ℓ.Prime) (hint : ∀ k, ¬ ℓ ∣ (ψ₀ hrat ψ k).den)
    (k : K) : (ψℓ hrat ψ ℓ hℓ hint k : ℚ) = ψ₀ hrat ψ k := rfl

theorem exists_int_sub_mem_span (ℓ : ℕ) (hℓ : ℓ.Prime) (v : GaloisRep.ratLocalizedAt ℓ) :
    ∃ a : ℤ, v - a ∈ Ideal.span {(ℓ : GaloisRep.ratLocalizedAt ℓ)} := by
  have hv : ¬ ℓ ∣ (v : ℚ).den := (GaloisRep.mem_ratLocalizedAt_iff hℓ _).mp v.2
  have hcop : IsCoprime ((v : ℚ).den : ℤ) (ℓ : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
    exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hv))
  obtain ⟨e, f, hef⟩ := hcop
  refine ⟨(v : ℚ).num * e, ?_⟩

  have hwmem : ((v : ℚ).num * f / (v : ℚ).den : ℚ) ∈ GaloisRep.ratLocalizedAt ℓ := by
    rw [GaloisRep.mem_ratLocalizedAt_iff hℓ]
    intro hdvd
    apply hv
    have := Rat.den_dvd ((v : ℚ).num * f) ((v : ℚ).den)
    exact dvd_trans hdvd (by exact_mod_cast this)
  refine Ideal.mem_span_singleton'.mpr ⟨⟨_, hwmem⟩, Subtype.ext ?_⟩
  have hden : ((v : ℚ).den : ℚ) ≠ 0 := by exact_mod_cast (v : ℚ).den_ne_zero
  have hvv : (v : ℚ) * (v : ℚ).den = (v : ℚ).num := Rat.mul_den_eq_num _
  have hef' : (e : ℚ) * (v : ℚ).den + f * ℓ = 1 := by exact_mod_cast hef
  push_cast
  rw [div_mul_eq_mul_div, div_eq_iff hden]
  linear_combination ((v : ℚ).num : ℚ) * hef' - hvv

theorem den_eq_one_of_mul_eq_int {ℓ : ℕ} (hℓ : ℓ.Prime) (t : ℚ) (ht : ¬ ℓ ∣ t.den) (z : ℤ)
    (hz : (ℓ : ℚ) * t = z) : t.den = 1 := by
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have h1 : t = z / (ℓ : ℤ) := by
    push_cast
    rw [← hz]; field_simp
  have h2 : (t.den : ℤ) ∣ (ℓ : ℤ) := by
    rw [h1, ← Rat.divInt_eq_div]
    exact Rat.den_dvd z ℓ
  have h3 : t.den ∣ ℓ := by exact_mod_cast h2
  rcases (Nat.dvd_prime hℓ).mp h3 with h | h
  · exact h
  · exact absurd (h ▸ dvd_rfl) ht

theorem exists_ψ₀_eq_of_eq_mul (ψ : Pt K) {ℓ : ℕ} (hℓ : ℓ.Prime) (k : K)
    (w : ℚ) (hw : ¬ ℓ ∣ w.den) (hk : ψ₀ hrat ψ k = ℓ * w) :
    ∃ k' : K, ψ₀ hrat ψ k' = w := by
  set r := ψ₀ hrat ψ k with hr
  obtain ⟨k₁, hk₁⟩ := exists_ψ₀_eq_inv_den hrat ψ k
  rw [← hr] at hk₁
  set t : ℚ := w * r.den with ht
  have hℓt : (ℓ : ℚ) * t = r.num := by
    rw [ht, ← mul_assoc, ← hk]
    exact Rat.mul_den_eq_num r
  have htden : ¬ ℓ ∣ t.den := by
    intro hdvd
    apply hw
    have h1 := Rat.mul_den_dvd w (r.den : ℚ)
    have h2 : ((r.den : ℚ)).den = 1 := by simp
    rw [h2, mul_one] at h1
    exact dvd_trans hdvd h1
  have htint : t.den = 1 := den_eq_one_of_mul_eq_int hℓ t htden r.num hℓt
  have ht' : (t.num : ℚ) = t := (Rat.den_eq_one_iff t).mp htint
  refine ⟨(t.num : K) * k₁, ?_⟩
  rw [map_mul, ψ₀_intCast, hk₁, ht', ht]
  have hden : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  field_simp

variable (hR : ∀ (ℓ : ℕ), ℓ.Prime → ∀ χ χ' : K →+* GaloisRep.ratLocalizedAt ℓ,
  (∀ k, χ k - χ' k ∈ Ideal.span {(ℓ : GaloisRep.ratLocalizedAt ℓ)}) → χ = χ')

omit [HopfAlgebra ℤ K] in

theorem exists_prime_mem_of_natCast_mem {m : Ideal K} [m.IsPrime] {N : ℕ} (hN : 0 < N)
    (hNm : (N : K) ∈ m) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : K) ∈ m ∧
      m.comap (Int.castRingHom K) = Ideal.span {(ℓ : ℤ)} := by
  set m' : Ideal ℤ := m.comap (Int.castRingHom K) with hm'
  haveI : m'.IsPrime := Ideal.comap_isPrime _ _
  set g : ℤ := Submodule.IsPrincipal.generator m' with hg
  have hspan : Ideal.span {g} = m' := Ideal.span_singleton_generator m'
  have hNm' : (N : ℤ) ∈ m' := by
    rw [hm', Ideal.mem_comap]; simpa using hNm
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at hspan
    rw [← hspan] at hNm'
    have : (N : ℤ) = 0 := (Submodule.mem_bot ℤ).mp hNm'
    omega
  have hgprime : Prime g := (Ideal.span_singleton_prime hg0).mp (hspan ▸ inferInstance)
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hgprime, ?_, ?_⟩
  · have h1 : ((g.natAbs : ℕ) : ℤ) ∈ m' := by
      rw [← hspan]
      exact Ideal.mem_span_singleton.mpr (Int.dvd_natAbs.mpr dvd_rfl)
    rw [hm', Ideal.mem_comap] at h1
    simpa using h1
  · rw [← hspan]
    exact Ideal.span_singleton_eq_span_singleton.mpr (Int.associated_natAbs g)

include hR hdense in

theorem isCoprime_P (ψ ψ' : Pt K) (hne : ψ ≠ ψ') :
    IsCoprime (P hrat ψ) (P hrat ψ') := by
  classical
  by_contra hnc
  rw [Ideal.isCoprime_iff_sup_eq] at hnc
  obtain ⟨m, hmmax, hJm⟩ := Ideal.exists_le_maximal _ hnc
  have hPm : P hrat ψ ≤ m := le_trans le_sup_left hJm
  have hP'm : P hrat ψ' ≤ m := le_trans le_sup_right hJm

  obtain ⟨x, N, hN, hx⟩ := exists_numerator hrat hdense ψ'
  have hNm : (N : K) ∈ m := by
    have h1 : (N : K) - x ∈ P hrat ψ' := by
      rw [mem_P, map_sub, map_natCast, hx, if_pos rfl, sub_self]
    have h2 : x ∈ P hrat ψ := by
      rw [mem_P, hx, if_neg hne]
    have := m.add_mem (hP'm h1) (hPm h2)
    rwa [sub_add_cancel] at this

  haveI : m.IsPrime := hmmax.isPrime
  obtain ⟨ℓ, hℓ, hℓm, hcomap⟩ := exists_prime_mem_of_natCast_mem hN hNm

  have hint := not_dvd_den_of_le hrat ψ hmmax.ne_top hℓm hPm
  have hint' := not_dvd_den_of_le hrat ψ' hmmax.ne_top hℓm hP'm
  set χ := ψℓ hrat ψ ℓ hℓ hint with hχ
  set χ' := ψℓ hrat ψ' ℓ hℓ hint' with hχ'

  have happrox : ∀ (φ : Pt K) (hφint : ∀ k, ¬ ℓ ∣ (ψ₀ hrat φ k).den) (hφm : P hrat φ ≤ m)
      (k : K) (a : ℤ),
      ψℓ hrat φ ℓ hℓ hφint k - a ∈ Ideal.span {(ℓ : GaloisRep.ratLocalizedAt ℓ)} →
      k - (a : K) ∈ m := by
    intro φ hφint hφm k a ha
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp ha
    have hval : ψ₀ hrat φ (k - a) = ℓ * (w : ℚ) := by
      have := congrArg (fun z : GaloisRep.ratLocalizedAt ℓ => (z : ℚ)) hw
      beta_reduce at this
      push_cast at this
      rw [map_sub, ψ₀_intCast, ← ψℓ_apply hrat φ ℓ hℓ hφint, ← this, mul_comm]
    have hwden : ¬ ℓ ∣ (w : ℚ).den := (GaloisRep.mem_ratLocalizedAt_iff hℓ _).mp w.2
    obtain ⟨k', hk'⟩ := exists_ψ₀_eq_of_eq_mul hrat φ hℓ (k - a) (w : ℚ) hwden hval
    have h1 : k - a - (ℓ : K) * k' ∈ P hrat φ := by
      rw [mem_P, map_sub, hval, map_mul, map_natCast, hk', sub_self]
    have h2 : (ℓ : K) * k' ∈ m := m.mul_mem_right _ hℓm
    have := m.add_mem (hφm h1) h2
    rwa [sub_add_cancel] at this

  have hkey : ∀ k, χ k - χ' k ∈ Ideal.span {(ℓ : GaloisRep.ratLocalizedAt ℓ)} := by
    intro k
    obtain ⟨a, ha⟩ := exists_int_sub_mem_span ℓ hℓ (χ k)
    obtain ⟨a', ha'⟩ := exists_int_sub_mem_span ℓ hℓ (χ' k)
    have hka : k - (a : K) ∈ m := happrox ψ hint hPm k a ha
    have hka' : k - (a' : K) ∈ m := happrox ψ' hint' hP'm k a' ha'
    have haa' : ((a - a' : ℤ) : K) ∈ m := by
      have := m.sub_mem hka' hka
      rw [sub_sub_sub_cancel_left] at this
      simpa using this
    have haa'Z : (a - a' : ℤ) ∈ Ideal.span {(ℓ : ℤ)} := by
      rw [← hcomap, Ideal.mem_comap]; simpa using haa'
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp haa'Z
    have haa'L : ((a : GaloisRep.ratLocalizedAt ℓ)) - a' ∈
        Ideal.span {(ℓ : GaloisRep.ratLocalizedAt ℓ)} := by
      refine Ideal.mem_span_singleton'.mpr ⟨t, ?_⟩
      have := congrArg (fun z : ℤ => (z : GaloisRep.ratLocalizedAt ℓ)) ht
      push_cast at this
      exact this
    have : χ k - χ' k = (χ k - a) - (χ' k - a') + (a - a') := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.sub_mem _ ha ha') haa'L
  have hχχ' : χ = χ' := hR ℓ hℓ χ χ' hkey
  apply hne
  apply eq_of_ψ₀_eq hrat
  refine RingHom.ext fun k => ?_
  have := congrArg (fun f : K →+* GaloisRep.ratLocalizedAt ℓ => (f k : ℚ)) hχχ'
  simpa [hχ, hχ'] using this

variable [Finite (Pt K)]

include hR hdense in

theorem exists_epsilon :
    ∃ ε : Pt K → K, ∀ ψ ψ' : Pt K, ψ₀ hrat ψ' (ε ψ) = if ψ' = ψ then 1 else 0 := by
  have hcop : Pairwise (Function.onFun IsCoprime fun ψ : Pt K => P hrat ψ) :=
    fun ψ ψ' hne => isCoprime_P hrat hdense hR ψ ψ' hne
  have hsurj := Ideal.quotientInfToPiQuotient_surj hcop
  suffices h : ∀ ψ : Pt K, ∃ x : K, ∀ ψ', ψ₀ hrat ψ' x = if ψ' = ψ then 1 else 0 by
    choose ε hε using h
    exact ⟨ε, hε⟩
  intro ψ
  obtain ⟨xbar, hxbar⟩ := hsurj (fun ψ' => Ideal.Quotient.mk _ (if ψ' = ψ then 1 else 0))
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xbar
  refine ⟨x, fun ψ' => ?_⟩
  have h1 := congrFun hxbar ψ'
  rw [Ideal.quotientInfToPiQuotient_mk'] at h1
  have h2 : x - (if ψ' = ψ then 1 else 0) ∈ P hrat ψ' := Ideal.Quotient.eq.mp h1
  rw [mem_P, map_sub, sub_eq_zero] at h2
  rw [h2]
  split_ifs <;> simp

section Group

open WithConv

abbrev G (K : Type) [CommRing K] [HopfAlgebra ℤ K] : Type := (WithConv (Pt K))ˣ

theorem isUnit_pt (f : WithConv (Pt K)) : IsUnit f := HopfAlgebra.isUnit_withConv_algHom f

def unitsEquivPt : G K ≃ Pt K where
  toFun u := (u : WithConv (Pt K)).ofConv
  invFun ψ := (isUnit_pt (toConv ψ)).unit
  left_inv u := Units.ext (by simp)
  right_inv ψ := by simp

variable {q : ℕ} [Fact q.Prime] (hq : Nat.card (Pt K) = q)

include hq in
omit [Fact q.Prime] in
theorem natCard_G : Nat.card (G K) = q := by rw [Nat.card_congr unitsEquivPt, hq]

def σ : G K ≃* Multiplicative (ZMod q) :=
  mulEquivOfPrimeCardEq (p := q) (natCard_G hq) (by simp [Nat.card_eq_fintype_card, ZMod.card])

def pt (a : ZMod q) : Pt K := unitsEquivPt ((σ hq).symm (Multiplicative.ofAdd a))

theorem pt_bijective : Function.Bijective (pt (K := K) hq) :=
  unitsEquivPt.bijective.comp ((σ hq).symm.bijective.comp Multiplicative.ofAdd.bijective)

theorem pt_injective : Function.Injective (pt (K := K) hq) := (pt_bijective hq).1

theorem toConv_pt_add (a b : ZMod q) :
    toConv (pt hq (a + b)) = toConv (pt hq a) * toConv (pt (K := K) hq b) := by
  simp only [pt, unitsEquivPt, Equiv.coe_fn_mk, toConv_ofConv, ofAdd_add, map_mul, Units.val_mul]

theorem toConv_pt_zero : toConv (pt (K := K) hq 0) = 1 := by
  simp only [pt, unitsEquivPt, Equiv.coe_fn_mk, toConv_ofConv, ofAdd_zero, map_one, Units.val_one]

def idxPt (ψ : Pt K) : ZMod q := (Equiv.ofBijective _ (pt_bijective hq)).symm ψ

@[scoped simp] theorem pt_idxPt (ψ : Pt K) : pt hq (idxPt hq ψ) = ψ :=
  (Equiv.ofBijective _ (pt_bijective hq)).apply_symm_apply ψ

@[scoped simp] theorem idxPt_pt (a : ZMod q) : idxPt hq (pt (K := K) hq a) = a :=
  (Equiv.ofBijective _ (pt_bijective hq)).symm_apply_apply a

end Group

section Idempotents

variable {q : ℕ} [Fact q.Prime] (hq : Nat.card (Pt K) = q)
variable {ε : Pt K → K} (hε : ∀ ψ ψ' : Pt K, ψ₀ hrat ψ' (ε ψ) = if ψ' = ψ then 1 else 0)

def e (ε : Pt K → K) (a : ZMod q) : K := ε (pt hq a)

include hε in
theorem ψ₀_pt_e (a b : ZMod q) : ψ₀ hrat (pt hq b) (e hq ε a) = if b = a then 1 else 0 := by
  rw [e, hε]
  by_cases h : b = a
  · rw [if_pos h, if_pos (congrArg _ h)]
  · rw [if_neg h, if_neg (fun h' => h (pt_injective hq h'))]

include hε in
theorem ψ₀_e (ψ : Pt K) (a : ZMod q) : ψ₀ hrat ψ (e hq ε a) = if idxPt hq ψ = a then 1 else 0 := by
  conv_lhs => rw [← pt_idxPt hq ψ]
  exact ψ₀_pt_e hrat hq hε a _

include hε hsep in

theorem coi_e : CompleteOrthogonalIdempotents (e hq ε) := by
  refine ⟨⟨fun a => ?_, fun a b hab => ?_⟩, ?_⟩
  · apply sep₀ hrat hsep
    intro ψ
    rw [map_mul, ψ₀_e hrat hq hε]
    split_ifs <;> simp
  · apply sep₀ hrat hsep
    intro ψ
    rw [map_mul, ψ₀_e hrat hq hε, ψ₀_e hrat hq hε, map_zero]
    by_cases h : idxPt hq ψ = a
    · rw [if_pos h, if_neg (fun h' => hab (h.symm.trans h')), one_mul]
    · rw [if_neg h, zero_mul]
  · apply sep₀ hrat hsep
    intro ψ
    rw [map_sum, map_one, Finset.sum_eq_single (idxPt hq ψ)]
    · rw [ψ₀_e hrat hq hε, if_pos rfl]
    · intro b _ hb
      rw [ψ₀_e hrat hq hε, if_neg (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_univ _) h

include hε hsep in

theorem e_mul_eq_of_forall (a : ZMod q) (k k' : K)
    (h : ψ₀ hrat (pt hq a) k = ψ₀ hrat (pt hq a) k') : e hq ε a * k = e hq ε a * k' := by
  apply sep₀ hrat hsep
  intro ψ
  rw [map_mul, map_mul, ψ₀_e hrat hq hε]
  by_cases hψ : idxPt hq ψ = a
  · rw [if_pos hψ, one_mul, one_mul, ← pt_idxPt hq ψ, hψ, h]
  · rw [if_neg hψ, zero_mul, zero_mul]

end Idempotents

section Values

open WithConv

abbrev KL (K : Type) [CommRing K] [HopfAlgebra ℤ K] (ℓ : ℕ) : Type :=
  @TensorProduct ℤ _ (GaloisRep.ratLocalizedAt ℓ) K _ _
    (Algebra.toModule (R := ℤ) (A := GaloisRep.ratLocalizedAt ℓ))
    (Algebra.toModule (R := ℤ) (A := K))

abbrev tmulL (ℓ : ℕ) (z : GaloisRep.ratLocalizedAt ℓ) (k : K) : KL K ℓ :=
  @TensorProduct.tmul ℤ _ (GaloisRep.ratLocalizedAt ℓ) K _ _
    (Algebra.toModule (R := ℤ) (A := GaloisRep.ratLocalizedAt ℓ))
    (Algebra.toModule (R := ℤ) (A := K)) z k

theorem mem_ratLocalizedAt_of_finite (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hfin : letI : Module ℤ K := AddCommGroup.toIntModule K;
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (χ' : K →+* ℚ) (k : K) : χ' k ∈ GaloisRep.ratLocalizedAt ℓ := by
  haveI : Module.Finite (GaloisRep.ratLocalizedAt ℓ) (KL K ℓ) := by
    convert hfin <;> exact Subsingleton.elim _ _
  haveI : Algebra.IsIntegral (GaloisRep.ratLocalizedAt ℓ) (KL K ℓ) := inferInstance
  let θ : KL K ℓ →ₐ[GaloisRep.ratLocalizedAt ℓ] ℚ :=
    Algebra.TensorProduct.lift (Algebra.ofId _ ℚ) (intAlgHom χ') (fun _ _ => Commute.all _ _)
  have hint : IsIntegral (GaloisRep.ratLocalizedAt ℓ) (χ' k) := by
    have h1 : IsIntegral (GaloisRep.ratLocalizedAt ℓ) (tmulL ℓ 1 k) :=
      Algebra.IsIntegral.isIntegral _
    have h2 := h1.map θ
    have hθ : θ (tmulL ℓ 1 k) = χ' k := by
      change Algebra.TensorProduct.lift _ _ _ (tmulL ℓ 1 k) = _
      rw [tmulL, Algebra.TensorProduct.lift_tmul]
      simp
    rwa [hθ] at h2
  haveI := GaloisRep.isDiscreteValuationRing_ratLocalizedAt ℓ hℓ
  haveI := GaloisRep.isFractionRing_ratLocalizedAt ℓ
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  rw [← hy]
  exact y.2

variable {p : ℕ} [Fact p.Prime]
variable (hff : letI : Module ℤ K := AddCommGroup.toIntModule K;
  ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
    Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))

include hff in

theorem exists_den_eq_pow (ψ : Pt K) (k : K) : ∃ n : ℕ, (ψ₀ hrat ψ k).den = p ^ n := by
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd (ψ₀ hrat ψ k).den_ne_zero ?_⟩
  intro d hd hdvd
  by_contra hdp
  have hmem := mem_ratLocalizedAt_of_finite d hd (hff d hd hdp) (ψ₀ hrat ψ) k
  exact (GaloisRep.mem_ratLocalizedAt_iff hd _).mp hmem hdvd

def IsInt (ψ : Pt K) : Prop := ∀ k, ∃ m : ℤ, ψ₀ hrat ψ k = m

variable {q : ℕ} [Fact q.Prime] (hq : Nat.card (Pt K) = q)

def χQ (ψ : Pt K) : WithConv (K →ₐ[ℤ] ℚ) := toConv (intAlgHom (ψ₀ hrat ψ))

@[scoped simp] theorem χQ_apply (ψ : Pt K) (k : K) : χQ hrat ψ k = ψ₀ hrat ψ k := rfl

def ιL : ℚ →ₐ[ℤ] L := intAlgHom (algebraMap ℚ L)

theorem ιL_comp_χQ (ψ : Pt K) : ιL.comp (χQ hrat ψ).ofConv = ψ := by
  refine AlgHom.ext fun k => ?_
  exact algebraMap_ψ₀ hrat ψ k

theorem ψ₀_pt_add (a b : ZMod q) (k : K) :
    ψ₀ hrat (pt hq (a + b)) k = (χQ hrat (pt hq a) * χQ hrat (pt hq b)) k := by
  apply (algebraMap ℚ L).injective
  rw [algebraMap_ψ₀]
  have h := AlgHom.comp_convMul_distrib ιL (χQ hrat (pt hq a)) (χQ hrat (pt hq b))
  rw [ιL_comp_χQ, ιL_comp_χQ, ← toConv_pt_add] at h
  have := congrArg (fun f : Pt K => f k) h
  exact this.symm

theorem ψ₀_pt_zero (k : K) :
    ψ₀ hrat (pt hq (0 : ZMod q)) k = (Bialgebra.counitAlgHom ℤ K k : ℚ) := by
  apply (algebraMap ℚ L).injective
  rw [algebraMap_ψ₀]
  have h : pt hq (0 : ZMod q) = ofConv (1 : WithConv (Pt K)) := by
    rw [← toConv_pt_zero hq, ofConv_toConv]
  rw [h, AlgHom.convOne_apply]
  simp

theorem isInt_zero : IsInt hrat (pt hq (0 : ZMod q)) := fun k =>
  ⟨Bialgebra.counitAlgHom ℤ K k, ψ₀_pt_zero hrat hq k⟩

abbrev KK (K : Type) [CommRing K] [HopfAlgebra ℤ K] : Type :=
  @TensorProduct ℤ _ K K _ _ (Algebra.toModule (R := ℤ) (A := K)) (Algebra.toModule (R := ℤ) (A := K))

abbrev tmulKK (k k' : K) : KK K :=
  @TensorProduct.tmul ℤ _ K K _ _ (Algebra.toModule (R := ℤ) (A := K))
    (Algebra.toModule (R := ℤ) (A := K)) k k'

scoped instance (priority := high) instIsScalarTowerIntIntHopf :
    @IsScalarTower ℤ ℤ K _ Algebra.toSMul Algebra.toSMul :=
  @IsScalarTower.left ℤ K _
    (@Module.toDistribMulAction ℤ K _ _ (Algebra.toModule (R := ℤ) (A := K))).toMulAction

def pairChar (ψ ψ' : Pt K) : KK K →ₐ[ℤ] ℚ :=
  Algebra.TensorProduct.lift (χQ hrat ψ).ofConv (χQ hrat ψ').ofConv (fun _ _ => Commute.all _ _)

theorem pairChar_tmul (ψ ψ' : Pt K) (k k' : K) :
    pairChar hrat ψ ψ' (tmulKK k k') = ψ₀ hrat ψ k * ψ₀ hrat ψ' k' := by
  simp [pairChar, tmulKK]

theorem convMul_χQ_apply (ψ ψ' : Pt K) (k : K) :
    (χQ hrat ψ * χQ hrat ψ') k = pairChar hrat ψ ψ' (Coalgebra.comul (R := ℤ) k) :=
  AlgHom.convMul_apply _ _ k

theorem exists_int_pairChar {ψ ψ' : Pt K} (hψ : IsInt hrat ψ) (hψ' : IsInt hrat ψ') (z : KK K) :
    ∃ m : ℤ, pairChar hrat ψ ψ' z = m := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul k k' =>
    obtain ⟨m, hm⟩ := hψ k
    obtain ⟨m', hm'⟩ := hψ' k'
    exact ⟨m * m', by rw [pairChar_tmul, hm, hm']; push_cast; ring⟩
  | add x y hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨m', hm'⟩ := hy
    exact ⟨m + m', by rw [map_add, hm, hm']; push_cast; ring⟩

theorem isInt_add {a b : ZMod q} (ha : IsInt hrat (pt hq a)) (hb : IsInt hrat (pt hq b)) :
    IsInt hrat (pt hq (a + b)) := by
  intro k
  obtain ⟨m, hm⟩ := exists_int_pairChar hrat ha hb (Coalgebra.comul (R := ℤ) k)
  exact ⟨m, by rw [ψ₀_pt_add, convMul_χQ_apply, hm]⟩

include hff in

theorem isInt_dichotomy :
    (∀ a : ZMod q, IsInt hrat (pt hq a)) ∨ (∀ a : ZMod q, a ≠ 0 → ¬ IsInt hrat (pt hq a)) := by
  by_cases h : ∃ a : ZMod q, a ≠ 0 ∧ IsInt hrat (pt hq a)
  · left
    obtain ⟨a, ha0, ha⟩ := h
    have hmul : ∀ n : ℕ, IsInt hrat (pt hq ((n : ZMod q) * a)) := by
      intro n
      induction n with
      | zero => simpa using isInt_zero hrat hq
      | succ n ih =>
        have : ((n + 1 : ℕ) : ZMod q) * a = (n : ZMod q) * a + a := by push_cast; ring
        rw [this]
        exact isInt_add hrat hq ih ha
    intro b
    have hb : b = ((b * a⁻¹).val : ZMod q) * a := by
      rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ ha0, mul_one]
    rw [hb]
    exact hmul _
  · right
    push Not at h
    exact h

include hff in

theorem exists_ψ₀_eq_inv_p {ψ : Pt K} (hψ : ¬ IsInt hrat ψ) : ∃ y : K, ψ₀ hrat ψ y = (p : ℚ)⁻¹ := by
  unfold IsInt at hψ
  push Not at hψ
  obtain ⟨k, hk⟩ := hψ
  obtain ⟨n, hn⟩ := exists_den_eq_pow hrat hff ψ k
  apply exists_ψ₀_eq_inv hrat ψ (k := k)
  rw [hn]
  cases n with
  | zero =>
    exfalso
    apply hk (ψ₀ hrat ψ k).num
    rw [pow_zero] at hn
    exact ((Rat.den_eq_one_iff _).mp hn).symm
  | succ n => exact dvd_pow_self p (Nat.succ_ne_zero n)

end Values

section Corner

open WithConv

variable {q : ℕ} [Fact q.Prime] (hq : Nat.card (Pt K) = q)
variable {ε : Pt K → K} (hε : ∀ ψ ψ' : Pt K, ψ₀ hrat ψ' (ε ψ) = if ψ' = ψ then 1 else 0)

theorem tmulKK_mul (x y x' y' : K) : tmulKK x y * tmulKK x' y' = tmulKK (x * x') (y * y') :=
  @Algebra.TensorProduct.tmul_mul_tmul ℤ K K _ _ (Algebra.toModule) _ _ _ (Algebra.toModule) _ _ x x' y y'

theorem intCast_KK (z : ℤ) : ((z : KK K)) = tmulKK (z : K) 1 :=
  @Algebra.TensorProduct.intCast_def ℤ K K _ _ (Algebra.toModule) _ (Algebra.toModule) z

theorem intCast_KK' (z : ℤ) : ((z : KK K)) = tmulKK 1 (z : K) :=
  @Algebra.TensorProduct.intCast_def' ℤ K _ _ (Bialgebra.toAlgebra) K _ (Bialgebra.toAlgebra) z

theorem tmulKK_intCast_mul (m m' : ℤ) (x y : K) :
    tmulKK ((m : K) * x) ((m' : K) * y) = ((m * m' : ℤ) : KK K) * tmulKK x y := by
  rw [Int.cast_mul, intCast_KK, intCast_KK', tmulKK_mul, tmulKK_mul, one_mul, mul_one]

theorem sum_tmulKK {α : Type*} (s : Finset α) (f : α → K) (y : K) :
    tmulKK (∑ a ∈ s, f a) y = ∑ a ∈ s, tmulKK (f a) y :=
  @TensorProduct.sum_tmul ℤ _ K K _ _ (Algebra.toModule) (Algebra.toModule) α s f y

theorem tmulKK_sum {α : Type*} (x : K) (s : Finset α) (f : α → K) :
    tmulKK x (∑ a ∈ s, f a) = ∑ a ∈ s, tmulKK x (f a) :=
  @TensorProduct.tmul_sum ℤ _ K K _ _ (Algebra.toModule) (Algebra.toModule) x α s f

structure CornerData (w : ZMod q → K) (d : ZMod q → ℕ) : Prop where
  pos : ∀ a, 0 < d a
  val : ∀ a b, ψ₀ hrat (pt hq b) (w a) = if b = a then ((d a : ℚ))⁻¹ else 0
  dense : ∀ (a : ZMod q) (k : K), ∃ (n : ℕ) (m : ℤ), ψ₀ hrat (pt hq a) k = m / (d a : ℚ) ^ n

variable {w : ZMod q → K} {d : ZMod q → ℕ} (hc : CornerData hrat hq w d)

def g (hq : Nat.card (Pt K) = q) (ε : Pt K → K) (w : ZMod q → K) (a : ZMod q) (n : ℕ) : K :=
  e hq ε a * w a ^ n

include hc hε in
theorem ψ₀_g (a b : ZMod q) (n : ℕ) :
    ψ₀ hrat (pt hq b) (g hq ε w a n) = if b = a then (((d a : ℚ)) ^ n)⁻¹ else 0 := by
  rw [g, map_mul, map_pow, ψ₀_pt_e hrat hq hε, hc.val]
  split_ifs <;> simp [inv_pow]

include hc hε hsep in
theorem pow_mul_g (a : ZMod q) (n j : ℕ) :
    ((d a : K)) ^ j * g hq ε w a (n + j) = g hq ε w a n := by
  apply sep₀ hrat hsep
  intro ψ
  rw [← pt_idxPt hq ψ, map_mul, map_pow, map_natCast, ψ₀_g hrat hq hε hc,
    ψ₀_g hrat hq hε hc]
  have hd : ((d a : ℚ)) ≠ 0 := by exact_mod_cast (hc.pos a).ne'
  split_ifs
  · rw [pow_add, mul_inv]
    field_simp
  · rw [mul_zero]

include hc hε hsep in

theorem exists_corner_rep (k : K) :
    ∃ n : ℕ, ∀ a : ZMod q, ∃ m : ℤ, e hq ε a * k = (m : K) * g hq ε w a n := by

  have hper : ∀ a : ZMod q, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ m : ℤ, e hq ε a * k = (m : K) * g hq ε w a n := by
    intro a
    obtain ⟨n₀, m, hm⟩ := hc.dense a k
    refine ⟨n₀, fun n hn => ⟨m * (d a : ℤ) ^ (n - n₀), ?_⟩⟩
    apply sep₀ hrat hsep
    intro ψ
    rw [← pt_idxPt hq ψ, map_mul, map_mul, ψ₀_pt_e hrat hq hε, ψ₀_g hrat hq hε hc]
    have hd : ((d a : ℚ)) ≠ 0 := by exact_mod_cast (hc.pos a).ne'
    split_ifs with h
    · rw [h, hm, one_mul, ψ₀_intCast]
      push_cast
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
      rw [Nat.add_sub_cancel_left, pow_add]
      field_simp
    · rw [zero_mul, mul_zero]
  choose n₀ hn₀ using hper
  refine ⟨∑ a, n₀ a, fun a => hn₀ a _ ?_⟩
  exact Finset.single_le_sum (fun a _ => Nat.zero_le (n₀ a)) (Finset.mem_univ a)

include hε hsep in
theorem sum_e_mul (k : K) : ∑ a, e hq ε a * k = k := by
  rw [← Finset.sum_mul, (coi_e hrat hsep hq hε).complete, one_mul]

def IsRep (z : KK K) : Prop :=
  ∃ (n : ℕ) (C : ZMod q → ZMod q → ℤ),
    z = ∑ a, ∑ b, ((C a b : ℤ) : KK K) * tmulKK (g hq ε w a n) (g hq ε w b n)

include hc hε hsep in
theorem isRep_lift {z : KK K} {n : ℕ} {C : ZMod q → ZMod q → ℤ}
    (hz : z = ∑ a, ∑ b, ((C a b : ℤ) : KK K) * tmulKK (g hq ε w a n) (g hq ε w b n)) (j : ℕ) :
    z = ∑ a, ∑ b, (((C a b * ((d a : ℤ) ^ j * (d b : ℤ) ^ j) : ℤ)) : KK K) *
      tmulKK (g hq ε w a (n + j)) (g hq ε w b (n + j)) := by
  rw [hz]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← pow_mul_g hrat hsep hq hε hc a n j, ← pow_mul_g hrat hsep hq hε hc b n j]
  rw [show ((d a : K)) ^ j = (((d a : ℤ) ^ j : ℤ) : K) by push_cast; rfl,
    show ((d b : K)) ^ j = (((d b : ℤ) ^ j : ℤ) : K) by push_cast; rfl, tmulKK_intCast_mul,
    ← mul_assoc, ← Int.cast_mul]

include hc hε hsep in

theorem isRep (z : KK K) : IsRep hq (ε := ε) (w := w) z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul k k' =>
    obtain ⟨n₁, h₁⟩ := exists_corner_rep hrat hsep hq hε hc k
    obtain ⟨n₂, h₂⟩ := exists_corner_rep hrat hsep hq hε hc k'
    choose m₁ hm₁ using h₁
    choose m₂ hm₂ using h₂

    refine ⟨n₁ + n₂, fun a b => m₁ a * (d a : ℤ) ^ n₂ * (m₂ b * (d b : ℤ) ^ n₁), ?_⟩
    have hk : k = ∑ a, ((m₁ a * (d a : ℤ) ^ n₂ : ℤ) : K) * g hq ε w a (n₁ + n₂) := by
      conv_lhs => rw [← sum_e_mul hrat hsep hq hε k]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hm₁, ← pow_mul_g hrat hsep hq hε hc a n₁ n₂]
      push_cast; ring
    have hk' : k' = ∑ b, ((m₂ b * (d b : ℤ) ^ n₁ : ℤ) : K) * g hq ε w b (n₁ + n₂) := by
      conv_lhs => rw [← sum_e_mul hrat hsep hq hε k']
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hm₂, ← pow_mul_g hrat hsep hq hε hc b n₂ n₁, Nat.add_comm n₂ n₁]
      push_cast; ring
    change tmulKK k k' = _
    rw [hk, sum_tmulKK]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hk', tmulKK_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [tmulKK_intCast_mul]
  | add x y hx hy =>
    obtain ⟨n₁, C₁, h₁⟩ := hx
    obtain ⟨n₂, C₂, h₂⟩ := hy
    have h₁' := isRep_lift hrat hsep hq hε hc h₁ n₂
    have h₂' := isRep_lift hrat hsep hq hε hc h₂ n₁
    rw [Nat.add_comm n₂ n₁] at h₂'
    refine ⟨n₁ + n₂, fun a b => C₁ a b * ((d a : ℤ) ^ n₂ * (d b : ℤ) ^ n₂) +
      C₂ a b * ((d a : ℤ) ^ n₁ * (d b : ℤ) ^ n₁), ?_⟩
    rw [h₁', h₂', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Int.cast_add, add_mul]

include hc hε in
theorem pairChar_tmulKK_g (a b a' b' : ZMod q) (n : ℕ) :
    pairChar hrat (pt hq a) (pt hq b) (tmulKK (g hq ε w a' n) (g hq ε w b' n)) =
      if a = a' ∧ b = b' then ((((d a' : ℚ)) ^ n)⁻¹ * (((d b' : ℚ)) ^ n)⁻¹) else 0 := by
  rw [pairChar_tmul, ψ₀_g hrat hq hε hc, ψ₀_g hrat hq hε hc]
  by_cases ha : a = a' <;> by_cases hb : b = b' <;> simp [ha, hb]

include hc hε hsep in

theorem eq_zero_of_pairChar_eq_zero (z : KK K)
    (hz : ∀ a b : ZMod q, pairChar hrat (pt hq a) (pt hq b) z = 0) : z = 0 := by
  obtain ⟨n, C, hC⟩ := isRep hrat hsep hq hε hc z
  have hC0 : ∀ a b, C a b = 0 := by
    intro a b
    have h := hz a b
    rw [hC, map_sum] at h
    simp_rw [map_sum, map_mul, map_intCast, pairChar_tmulKK_g hrat hq hε hc] at h
    rw [Finset.sum_eq_single a, Finset.sum_eq_single b] at h
    · rw [if_pos ⟨rfl, rfl⟩] at h
      have hd : ∀ c, (((d c : ℚ)) ^ n)⁻¹ ≠ 0 := fun c =>
        inv_ne_zero (pow_ne_zero _ (by exact_mod_cast (hc.pos c).ne'))
      have := mul_eq_zero.mp h
      rcases this with h1 | h2
      · exact_mod_cast h1
      · exact absurd h2 (mul_ne_zero (hd a) (hd b))
    · intro b' _ hb'; simp [Ne.symm hb']
    · intro h'; exact absurd (Finset.mem_univ _) h'
    · intro a' _ ha';
      apply Finset.sum_eq_zero; intro b' _; simp [Ne.symm ha']
    · intro h'; exact absurd (Finset.mem_univ _) h'
  rw [hC]
  apply Finset.sum_eq_zero; intro a _
  apply Finset.sum_eq_zero; intro b _
  rw [hC0, Int.cast_zero, zero_mul]

include hc hε hsep in

theorem comul_e (c : ZMod q) :
    (Coalgebra.comul (R := ℤ) (e hq ε c) : KK K) = ∑ a, tmulKK (e hq ε a) (e hq ε (c - a)) := by
  rw [← sub_eq_zero]
  apply eq_zero_of_pairChar_eq_zero hrat hsep hq hε hc
  intro a b
  rw [map_sub, map_sum, ← convMul_χQ_apply, ← ψ₀_pt_add, ψ₀_pt_e hrat hq hε]
  simp_rw [pairChar_tmul, ψ₀_pt_e hrat hq hε]
  rw [Finset.sum_eq_single a]
  · by_cases h : a + b = c
    · rw [if_pos h, if_pos rfl, if_pos (by rw [← h]; ring), mul_one, sub_self]
    · rw [if_neg h, if_pos rfl, if_neg (by intro h'; apply h; rw [h']; ring), mul_zero, sub_self]
  · intro a' _ ha'; rw [if_neg (Ne.symm ha'), zero_mul]
  · intro h'; exact absurd (Finset.mem_univ _) h'

include hc hε hsep in

theorem convMul_apply_e (T : Type) [CommRing T] (φ χ : K →ₐ[ℤ] T) (c : ZMod q) :
    (toConv φ * toConv χ) (e hq ε c) = ∑ a, φ (e hq ε a) * χ (e hq ε (c - a)) := by
  rw [AlgHom.convMul_apply, comul_e hrat hsep hq hε hc, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact @Algebra.TensorProduct.lift_tmul ℤ ℤ K K T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

include hε in

theorem counit_e (a : ZMod q) :
    Bialgebra.counitAlgHom ℤ K (e hq ε a) = if a = 0 then 1 else 0 := by
  have h := ψ₀_pt_zero hrat hq (e hq ε a)
  rw [ψ₀_pt_e hrat hq hε] at h
  have h' : ((Bialgebra.counitAlgHom ℤ K (e hq ε a) : ℤ) : ℚ) = ((if a = 0 then 1 else 0 : ℤ) : ℚ) := by
    rw [← h]
    by_cases ha : a = 0
    · rw [if_pos ha, if_pos ha.symm]; simp
    · rw [if_neg ha, if_neg (Ne.symm ha)]; simp
  exact_mod_cast h'

include hε in

theorem convOne_apply_e (T : Type) [CommRing T] (a : ZMod q) :
    (1 : WithConv (K →ₐ[ℤ] T)) (e hq ε a) = if a = 0 then 1 else 0 := by
  rw [AlgHom.convOne_apply, ← Bialgebra.counitAlgHom_apply, counit_e hrat hq hε]
  split_ifs <;> simp

end Corner

section Assembly

open WithConv

variable {p : ℕ} [Fact p.Prime]
variable (hff : letI : Module ℤ K := AddCommGroup.toIntModule K;
  ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
    Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
variable {q : ℕ} [Fact q.Prime] (hq : Nat.card (Pt K) = q)
variable {ε : Pt K → K} (hε : ∀ ψ ψ' : Pt K, ψ₀ hrat ψ' (ε ψ) = if ψ' = ψ then 1 else 0)

include hε in

theorem cornerData_const (hint : ∀ a : ZMod q, IsInt hrat (pt hq a)) :
    CornerData hrat hq (e hq ε) (fun _ => 1) where
  pos _ := Nat.one_pos
  val a b := by rw [ψ₀_pt_e hrat hq hε]; push_cast; simp
  dense a k := by
    obtain ⟨m, hm⟩ := hint a k
    exact ⟨0, m, by rw [hm]; simp⟩

include hε hff hsep in

theorem exists_cornerData_flat (hnint : ∀ a : ZMod q, a ≠ 0 → ¬ IsInt hrat (pt hq a)) :
    ∃ w : ZMod q → K, CornerData hrat hq w (fun a => if a = 0 then 1 else p) ∧ w 0 = e hq ε 0 ∧
      ∀ a, a ≠ 0 → w a = e hq ε a * w a := by
  have hy : ∀ a : ZMod q, ∃ y : K, a ≠ 0 → ψ₀ hrat (pt hq a) y = (p : ℚ)⁻¹ := by
    intro a
    by_cases ha : a = 0
    · exact ⟨0, fun h => absurd ha h⟩
    · obtain ⟨y, hy⟩ := exists_ψ₀_eq_inv_p hrat hff (hnint a ha)
      exact ⟨y, fun _ => hy⟩
  choose y hy using hy
  refine ⟨fun a => if a = 0 then e hq ε 0 else e hq ε a * y a, ⟨?_, ?_, ?_⟩, by simp, ?_⟩
  · intro a; split_ifs; exacts [Nat.one_pos, (Fact.out : p.Prime).pos]
  · intro a b
    by_cases ha : a = 0
    · subst ha
      simp only [if_true]
      rw [ψ₀_pt_e hrat hq hε]; push_cast; simp
    · simp only [if_neg ha]
      rw [map_mul, ψ₀_pt_e hrat hq hε]
      by_cases hb : b = a
      · subst hb; rw [if_pos rfl, if_pos rfl, one_mul, hy b ha]
      · rw [if_neg hb, if_neg hb, zero_mul]
  · intro a k
    by_cases ha : a = 0
    · subst ha
      obtain ⟨m, hm⟩ := isInt_zero hrat hq k
      exact ⟨0, m, by rw [hm]; simp⟩
    · obtain ⟨n, hn⟩ := exists_den_eq_pow hrat hff (pt hq a) k
      refine ⟨n, (ψ₀ hrat (pt hq a) k).num, ?_⟩
      rw [if_neg ha]
      conv_lhs => rw [← Rat.num_div_den (ψ₀ hrat (pt hq a) k), hn]
      push_cast
      rfl
  · intro a ha
    simp only [if_neg ha]
    rw [← mul_assoc, (coi_e hrat hsep hq hε).idem a]

theorem existsUnique_algHom_of_ringHom {T : Type} [CommRing T] {P : (K →+* T) → Prop}
    (h : ∃! φ : K →+* T, P φ) : ∃! φ : K →ₐ[ℤ] T, P (φ : K →+* T) := by
  obtain ⟨φ, hφ, huniq⟩ := h
  refine ⟨intAlgHom φ, hφ, fun ψ hψ => ?_⟩
  have := huniq (ψ : K →+* T) hψ
  refine AlgHom.ext fun k => ?_
  change (ψ : K →+* T) k = φ k
  rw [this]

include hε hsep in

theorem existsUnique_point {w : ZMod q → K} {d : ZMod q → ℕ} (hc : CornerData hrat hq w d)
    (T : Type) [CommRing T] (b : ZMod q → T) (hb : CompleteOrthogonalIdempotents b)
    (hbd : ∀ a, ∃ v : T, v * ((d a : T) * b a) = b a) :
    ∃! φ : K →ₐ[ℤ] T, ∀ a, φ (e hq ε a) = b a := by
  have h := RingHom.existsUnique_apply_eq_of_completeOrthogonalIdempotents_of_corner_denominators
    K (ZMod q) (e hq ε) (coi_e hrat hsep hq hε) (fun a => ψ₀ hrat (pt hq a))
    (fun a b => ψ₀_pt_e hrat hq hε a b)
    (fun k k' hkk' => sep₀ hrat hsep fun ψ => by rw [← pt_idxPt hq ψ]; exact hkk' _)
    d hc.pos hc.dense
    (fun a => ⟨w a, by rw [hc.val, if_pos rfl]⟩) T b hb hbd
  exact existsUnique_algHom_of_ringHom h

end Assembly

end Rational

end Engine

end

end P2mOddConstSplit
p2m_reactivate "P2MW.S_HopfAlgebra_exists_completeOrthogonalIdempotents_zmod_of_natCard_algHom_eq_of_ne_two.P2mOddConstSplit"

open P2mOddConstSplit WithConv in
theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K) (_ : Algebra.FiniteType ℤ K)
    (_ : Module.Flat ℤ K)
    (hff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p →
      Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) K))
    (hgenq : Nat.card (K →ₐ[ℤ] AlgebraicClosure ℚ) = q)
    (hgal : ∀ (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (ψ : K →ₐ[ℤ] AlgebraicClosure ℚ)
      (k : K), σ (ψ k) = ψ k) :
    ∃ e : ZMod q → K,
      CompleteOrthogonalIdempotents e ∧
      (∀ (T : Type) [CommRing T] (φ ψ : K →ₐ[ℤ] T) (c : ZMod q),
        (WithConv.toConv φ * WithConv.toConv ψ) (e c) = ∑ a, φ (e a) * ψ (e (c - a))) ∧
      (∀ (T : Type) [CommRing T] (a : ZMod q),
        (1 : WithConv (K →ₐ[ℤ] T)) (e a) = if a = 0 then 1 else 0) ∧
      ((∀ (T : Type) [CommRing T] (b : ZMod q → T), CompleteOrthogonalIdempotents b →
          ∃! φ : K →ₐ[ℤ] T, ∀ a, φ (e a) = b a) ∨
       ((∀ a, a ≠ 0 → ∃ u : K, u * (p * e a) = e a) ∧
        (∀ (T : Type) [CommRing T] (b : ZMod q → T), CompleteOrthogonalIdempotents b →
          (∀ a, a ≠ 0 → ∃ v : T, v * (p * b a) = b a) →
          ∃! φ : K →ₐ[ℤ] T, ∀ a, φ (e a) = b a))) := by

  haveI : Finite (Pt K) := Nat.finite_of_card_ne_zero (by rw [hgenq]; exact (Fact.out : q.Prime).ne_zero)

  have hℓ₀ : ∃ ℓ₀ : ℕ, ℓ₀.Prime ∧ ℓ₀ ≠ p := by
    by_cases hp : p = 2
    · exact ⟨3, Nat.prime_three, by omega⟩
    · exact ⟨2, Nat.prime_two, Ne.symm hp⟩
  obtain ⟨ℓ₀, hℓ₀p, hℓ₀ne⟩ := hℓ₀

  obtain ⟨hrat, hsep, hdense⟩ :=
    HopfAlgebra.rational_separating_dense_algHom_algebraicClosure_of_forall_ringEquiv_apply_eq
      K ℓ₀ (hff ℓ₀ hℓ₀p hℓ₀ne) hgal

  have hR : ∀ (ℓ : ℕ), ℓ.Prime → ∀ χ χ' : K →+* GaloisRep.ratLocalizedAt ℓ,
      (∀ k, χ k - χ' k ∈ Ideal.span {(ℓ : GaloisRep.ratLocalizedAt ℓ)}) → χ = χ' :=
    fun ℓ hℓ χ χ' h =>
      HopfAlgebra.ringHom_ratLocalizedAt_eq_of_forall_sub_mem_span_of_natCard_algHom_eq_of_ne_two
        p q hq2 K ‹_› ‹_› ‹_› ‹_› hff hgenq hgal ℓ hℓ χ χ' h

  obtain ⟨ε, hε⟩ := exists_epsilon hrat hdense hR
  refine ⟨e hgenq ε, coi_e hrat hsep hgenq hε, ?_⟩

  rcases isInt_dichotomy hrat (p := p) hff hgenq with hint | hnint
  · have hc := cornerData_const hrat hgenq hε hint
    refine ⟨fun T _ φ ψ c => convMul_apply_e hrat hsep hgenq hε hc T φ ψ c,
      fun T _ a => convOne_apply_e hrat hgenq hε T a, Or.inl fun T _ b hb => ?_⟩
    exact existsUnique_point hrat hsep hgenq hε hc T b hb (fun a => ⟨b a, by push_cast; rw [one_mul, hb.idem a]⟩)
  · obtain ⟨w, hc, hw0, hwa⟩ := exists_cornerData_flat hrat hsep (p := p) hff hgenq hε hnint
    refine ⟨fun T _ φ ψ c => convMul_apply_e hrat hsep hgenq hε hc T φ ψ c,
      fun T _ a => convOne_apply_e hrat hgenq hε T a, Or.inr ⟨fun a ha => ⟨w a, ?_⟩, fun T _ b hb hbp => ?_⟩⟩
    ·
      apply sep₀ hrat hsep
      intro ψ
      rw [← pt_idxPt hgenq ψ, map_mul, map_mul, map_natCast, hc.val, ψ₀_pt_e hrat hgenq hε]
      simp only [if_neg ha]
      split_ifs
      · have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
        field_simp
      · rw [zero_mul]
    · refine existsUnique_point hrat hsep hgenq hε hc T b hb (fun a => ?_)
      by_cases ha : a = 0
      · subst ha; exact ⟨b 0, by simp; exact hb.idem 0⟩
      · obtain ⟨v, hv⟩ := hbp a ha
        exact ⟨v, by simp only [if_neg ha]; exact hv⟩

end S_HopfAlgebra_exists_completeOrthogonalIdempotents_zmod_of_natCard_algHom_eq_of_ne_two
end P2MW
export P2MW.S_HopfAlgebra_exists_completeOrthogonalIdempotents_zmod_of_natCard_algHom_eq_of_ne_two (solution)
