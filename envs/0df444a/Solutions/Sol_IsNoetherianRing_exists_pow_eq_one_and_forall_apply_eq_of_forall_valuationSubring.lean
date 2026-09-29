-- Prove2me | solution 1 for IsNoetherianRing.exists_pow_eq_one_and_forall_apply_eq_of_forall_valuationSubring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/dfc6059d-8520-512f-a6ad-14301db128c4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsNoetherianRing_exists_pow_eq_one_and_forall_apply_eq_of_forall_valuationSubring

set_option autoImplicit false

universe u

namespace P2M
namespace MuSpread

open Polynomial

theorem eq_of_pow_eq_one_of_sub_mem_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A] {n : ℕ}
    (hn : IsUnit ((n : ℕ) : A)) {u x : A} (hu : u ^ n = 1) (hx : x ^ n = 1)
    (h : u - x ∈ IsLocalRing.maximalIdeal A) : u = x := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [Nat.cast_zero, isUnit_zero_iff] at hn
    exact zero_ne_one hn
  have hxu : IsUnit x := IsUnit.of_pow_eq_one hx hn0
  obtain ⟨xu, rfl⟩ := hxu
  set w : A := u * ((xu⁻¹ : Aˣ) : A) with hw
  have hw1 : w ^ n = 1 := by
    rw [hw, mul_pow, hu, one_mul, ← Units.val_pow_eq_pow_val, ← Units.val_one]
    congr 1
    rw [inv_pow, inv_eq_one, ← Units.val_inj, Units.val_pow_eq_pow_val, hx, Units.val_one]
  have hwm : w - 1 ∈ IsLocalRing.maximalIdeal A := by
    have : w - 1 = (u - (xu : A)) * ((xu⁻¹ : Aˣ) : A) := by
      rw [hw, sub_mul, Units.mul_inv]
    rw [this]
    exact Ideal.mul_mem_right _ _ h

  have hgeom : IsUnit (∑ i ∈ Finset.range n, w ^ i) := by
    by_contra hnu
    have hmem : (∑ i ∈ Finset.range n, w ^ i) ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hdiff : (∑ i ∈ Finset.range n, w ^ i) - (n : A) ∈ IsLocalRing.maximalIdeal A := by
      have : (∑ i ∈ Finset.range n, w ^ i) - (n : A) = ∑ i ∈ Finset.range n, (w ^ i - 1) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      rw [this]
      refine Ideal.sum_mem _ fun i _ => ?_
      obtain ⟨z, hz⟩ := sub_dvd_pow_sub_pow w 1 i
      rw [one_pow] at hz
      rw [hz]
      exact Ideal.mul_mem_right _ _ hwm
    have hnmem : (n : A) ∈ IsLocalRing.maximalIdeal A := by
      have := Ideal.sub_mem _ hmem hdiff
      rwa [sub_sub_cancel] at this
    exact (IsLocalRing.mem_maximalIdeal _).mp hnmem hn
  have hzero : (w - 1) * ∑ i ∈ Finset.range n, w ^ i = 0 := by
    rw [mul_comm, geom_sum_mul, hw1, sub_self]
  have hw1' : w - 1 = 0 := by
    obtain ⟨g, hg⟩ := hgeom
    rw [← hg] at hzero
    exact (Units.mul_left_eq_zero g).mp hzero
  rw [sub_eq_zero] at hw1'
  have : u = w * (xu : A) := by rw [hw, mul_assoc, Units.inv_mul, mul_one]
  rw [this, hw1', one_mul]

theorem exists_pow_eq_one_of_isNilpotent {R : Type*} [CommRing R] {n : ℕ} (hn : IsUnit ((n : ℕ) : R))
    (ε₀ : R) (hδ : IsNilpotent (ε₀ ^ n - 1)) :
    ∃ ε : R, ε ^ n = 1 ∧ IsNilpotent (ε - ε₀) := by

  suffices key : ∀ (k : ℕ) (x : R), (x ^ n - 1) ^ (2 ^ k) = 0 → IsNilpotent (x - ε₀) →
      ∃ ε : R, ε ^ n = 1 ∧ IsNilpotent (ε - ε₀) by
    obtain ⟨m, hm⟩ := hδ
    have h2 : (ε₀ ^ n - 1) ^ (2 ^ m) = 0 := by
      have hle : m ≤ 2 ^ m := (Nat.lt_two_pow_self).le
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      rw [hd, pow_add, hm, zero_mul]
    exact key m ε₀ h2 (by rw [sub_self]; exact IsNilpotent.zero)
  intro k
  induction k with
  | zero =>
    intro x hx hx0
    refine ⟨x, ?_, hx0⟩
    rwa [pow_zero, pow_one, sub_eq_zero] at hx
  | succ k ih =>
    intro x hx hx0
    by_cases hn0 : n = 0
    ·
      subst hn0
      rw [Nat.cast_zero, isUnit_zero_iff] at hn
      haveI hsub : Subsingleton R := subsingleton_of_zero_eq_one hn
      exact ⟨x, Subsingleton.elim _ _, hx0⟩

    set δ : R := x ^ n - 1 with hδdef
    have hδnil : IsNilpotent δ := ⟨2 ^ (k + 1), hx⟩
    have hxn : IsUnit (x ^ n) := by
      have : x ^ n = 1 + δ := by rw [hδdef, add_sub_cancel]
      rw [this]
      exact hδnil.isUnit_one_add
    have hxu : IsUnit x := isUnit_pow_iff hn0 |>.mp hxn

    have hder : IsUnit ((n : R) * x ^ (n - 1)) := hn.mul (hxu.pow _)
    obtain ⟨d, hd⟩ := hder
    set y : R := -(δ * ((d⁻¹ : Rˣ) : R)) with hy
    obtain ⟨z, hz⟩ := Polynomial.binomExpansion (X ^ n - 1 : R[X]) x y
    have hexp : (x + y) ^ n - 1 = δ + (n : R) * x ^ (n - 1) * y + z * y ^ 2 := by
      have h1 : ((X ^ n - 1 : R[X])).eval (x + y) = (x + y) ^ n - 1 := by simp
      have h2 : ((X ^ n - 1 : R[X])).eval x = δ := by simp [hδdef]
      have h3 : (derivative (X ^ n - 1 : R[X])).eval x = (n : R) * x ^ (n - 1) := by
        simp [derivative_X_pow]
      rw [← h1, hz, h2, h3]
    have hcancel : δ + (n : R) * x ^ (n - 1) * y = 0 := by
      rw [hy, ← hd, mul_neg, ← mul_assoc, mul_comm (d : R) δ, mul_assoc, Units.mul_inv, mul_one,
        add_neg_cancel]
    have hnew : (x + y) ^ n - 1 = z * ((d⁻¹ : Rˣ) : R) ^ 2 * δ ^ 2 := by
      rw [hexp, hcancel, zero_add, hy, neg_sq, mul_pow]; ring
    have hnew0 : ((x + y) ^ n - 1) ^ (2 ^ k) = 0 := by
      rw [hnew, mul_pow, ← pow_mul, show 2 * 2 ^ k = 2 ^ (k + 1) by ring, hx, mul_zero]
    have hy0 : IsNilpotent y := by
      rw [hy]
      exact (Commute.all _ _).isNilpotent_mul_right hδnil |>.neg
    obtain ⟨ε, hε, hεx⟩ := ih (x + y) hnew0 (by
      have : x + y - ε₀ = (x - ε₀) + y := by ring
      rw [this]
      exact (Commute.all _ _).isNilpotent_add hx0 hy0)
    exact ⟨ε, hε, hεx⟩

section PowerSums

variable {Ω : Type*} [Field Ω] [DecidableEq Ω]

theorem sum_range_pow_pow_eq {n : ℕ} {ζ : Ω} (hζ : IsPrimitiveRoot ζ n) (m : ℕ) :
    ∑ i ∈ Finset.range n, (ζ ^ i) ^ m = if ζ ^ m = 1 then (n : Ω) else 0 := by
  have hre : ∀ i, (ζ ^ i) ^ m = (ζ ^ m) ^ i := fun i => by rw [← pow_mul, ← pow_mul, mul_comm]
  simp_rw [hre]
  split_ifs with h
  · simp [h]
  · have hmul : (∑ i ∈ Finset.range n, (ζ ^ m) ^ i) * (ζ ^ m - 1) = 0 := by
      rw [geom_sum_mul, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self]
    exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr h)

theorem sum_range_mul_eval_eq {n : ℕ} {ζ : Ω} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n) (p : Polynomial Ω)
    (hp : p.natDegree < n) :
    ∑ i ∈ Finset.range n, ζ ^ i * p.eval (ζ ^ i) = (n : Ω) * p.coeff (n - 1) := by
  have hp' : ∀ x : Ω, p.eval x = ∑ j ∈ Finset.range n, p.coeff j * x ^ j := fun x => by
    rw [Polynomial.eval_eq_sum_range' hp]
  simp_rw [hp', Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ j ∈ Finset.range n,
      ∑ i ∈ Finset.range n, ζ ^ i * (p.coeff j * (ζ ^ i) ^ j) =
        p.coeff j * if ζ ^ (j + 1) = 1 then (n : Ω) else 0 := by
    intro j _
    rw [← sum_range_pow_pow_eq hζ (j + 1), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [Finset.sum_congr rfl hterm]

  rw [Finset.sum_eq_single (n - 1)]
  · rw [Nat.sub_add_cancel hn, hζ.pow_eq_one, if_pos rfl, mul_comm]
  · intro j hj hjn
    rw [Finset.mem_range] at hj
    have hlt : j + 1 < n := by omega
    have hne : ζ ^ (j + 1) ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (Nat.succ_ne_zero j) hlt
    rw [if_neg hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.sub_lt hn Nat.one_pos)) h

end PowerSums

section Geometric

def toValuationSubring {R : Type*} [CommRing R] {K : Type*} [Field K] (φ : R →+* K)
    (A : ValuationSubring K) (h : ∀ x, φ x ∈ A) : R →+* A where
  toFun x := ⟨φ x, h x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[scoped simp] theorem toValuationSubring_apply {R : Type*} [CommRing R] {K : Type*} [Field K] (φ : R →+* K)
    (A : ValuationSubring K) (h : ∀ x, φ x ∈ A) (x : R) :
    ((toValuationSubring φ A h x : A) : K) = φ x := rfl

theorem algebraMap_comp_toValuationSubring {R : Type*} [CommRing R] {K : Type*} [Field K] (φ : R →+* K)
    (A : ValuationSubring K) (h : ∀ x, φ x ∈ A) :
    (algebraMap A K).comp (toValuationSubring φ A h) = φ :=
  RingHom.ext fun _ => rfl

variable {R : Type u} [CommRing R]

theorem apply_comp_eq_of_hv
    (c : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω], (R →+* Ω) → Ω)
    (hv : ∀ (K : Type u) [Field K] [IsAlgClosed K] (𝒪 : ValuationSubring K)
      (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ρ : R →+* 𝒪) (ψ : 𝒪 →+* Ω),
      ∃ u : 𝒪, c K ((algebraMap 𝒪 K).comp ρ) = algebraMap 𝒪 K u ∧ c Ω (ψ.comp ρ) = ψ u)
    {Ω Ω' : Type u} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω'] (φ : R →+* Ω) (σ : Ω →+* Ω') :
    c Ω' (σ.comp φ) = σ (c Ω φ) := by
  let A : ValuationSubring Ω := ⊤
  let ρ : R →+* A := toValuationSubring φ A (fun x => ValuationSubring.mem_top _)
  let ψ : A →+* Ω' := σ.comp (algebraMap A Ω)
  obtain ⟨u, hu, hu'⟩ := hv Ω A Ω' ρ ψ
  have h1 : (algebraMap A Ω).comp ρ = φ := algebraMap_comp_toValuationSubring φ A _
  have h2 : ψ.comp ρ = σ.comp φ := by rw [RingHom.comp_assoc, h1]
  rw [h1] at hu
  rw [h2] at hu'
  rw [hu', hu]
  rfl

theorem iff_of_ker_eq {C : Type u} [CommRing C]
    (P : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω], (C →+* Ω) → Prop)
    (hP : ∀ (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω'] (χ : C →+* Ω)
      (σ : Ω →+* Ω'), P Ω χ ↔ P Ω' (σ.comp χ))
    {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsAlgClosed Ω₁] [Field Ω₂] [IsAlgClosed Ω₂] (χ₁ : C →+* Ω₁) (χ₂ : C →+* Ω₂)
    (h : RingHom.ker χ₁ = RingHom.ker χ₂) : P Ω₁ χ₁ ↔ P Ω₂ χ₂ := by
  let 𝔔 : Ideal C := RingHom.ker χ₁
  haveI : 𝔔.IsPrime := RingHom.ker_isPrime χ₁
  let D := C ⧸ 𝔔
  let q : C →+* D := Ideal.Quotient.mk 𝔔
  let k := FractionRing D
  let Kb := AlgebraicClosure k

  let χ₁' : D →+* Ω₁ := Ideal.Quotient.lift 𝔔 χ₁ fun a ha => ha
  let χ₂' : D →+* Ω₂ := Ideal.Quotient.lift 𝔔 χ₂ fun a ha => by
    have ha' : a ∈ RingHom.ker χ₂ := h ▸ ha
    exact ha'
  have hinj₁ : Function.Injective χ₁' := (Ideal.injective_lift_iff _).mpr rfl
  have hinj₂ : Function.Injective χ₂' := (Ideal.injective_lift_iff _).mpr h.symm
  let ι₁ : k →+* Ω₁ := IsFractionRing.lift hinj₁
  let ι₂ : k →+* Ω₂ := IsFractionRing.lift hinj₂
  let χb : C →+* Kb := (algebraMap k Kb).comp ((algebraMap D k).comp q)

  have key : ∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (χ' : D →+* Ω) (hχ' : Function.Injective χ')
      (χ : C →+* Ω), (∀ x, χ x = χ' (q x)) → (P Ω χ ↔ P Kb χb) := by
    intro Ω _ _ χ' hχ' χ hχ
    let ι : k →+* Ω := IsFractionRing.lift hχ'
    letI : Algebra k Ω := ι.toAlgebra
    let σ : Kb →ₐ[k] Ω := IsAlgClosed.lift
    have hσ : σ.toRingHom.comp χb = χ := by
      ext x
      change σ (algebraMap k Kb (algebraMap D k (q x))) = χ x
      rw [AlgHom.commutes, RingHom.algebraMap_toAlgebra, IsFractionRing.lift_algebraMap, hχ]
    rw [hP Kb Ω χb σ.toRingHom, hσ]
  have e₁ := key χ₁' hinj₁ χ₁ (fun x => (Ideal.Quotient.lift_mk 𝔔 χ₁ _).symm)
  have e₂ := key χ₂' hinj₂ χ₂ (fun x => (Ideal.Quotient.lift_mk 𝔔 χ₂ _).symm)
  exact e₁.trans e₂.symm

end Geometric

theorem isClosed_of_forall_le_iff {C : Type u} [CommRing C] [IsNoetherianRing C] (S : Set (PrimeSpectrum C))
    (hS : ∀ x y : PrimeSpectrum C, x.asIdeal ≤ y.asIdeal → (x ∈ S ↔ y ∈ S)) : IsClosed S := by
  classical
  let M : Set (Ideal C) := (⊥ : Ideal C).minimalPrimes
  have hM : M.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing C ⊥
  let T : Set (PrimeSpectrum C) := {x | x.asIdeal ∈ M ∧ x ∈ S}
  have hT : T.Finite := by
    refine (hM.preimage (f := PrimeSpectrum.asIdeal) ?_).subset ?_
    · exact fun x _ y _ hxy => PrimeSpectrum.ext hxy
    · intro x hx; exact hx.1
  have hST : S = ⋃ x ∈ T, PrimeSpectrum.zeroLocus (x.asIdeal : Set C) := by
    ext y
    simp only [Set.mem_iUnion, PrimeSpectrum.mem_zeroLocus, exists_prop]
    constructor
    · intro hy
      obtain ⟨p, hpM, hpy⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal C)) (J := y.asIdeal) bot_le
      refine ⟨⟨p, hpM.1.1⟩, ⟨hpM, (hS ⟨p, hpM.1.1⟩ y hpy).mpr hy⟩, hpy⟩
    · rintro ⟨x, hxT, hxy⟩
      exact (hS x y hxy).mp hxT.2
  rw [hST]
  exact hT.isClosed_biUnion fun x _ => PrimeSpectrum.isClosed_zeroLocus _

theorem isClopen_of_forall_le_iff {C : Type u} [CommRing C] [IsNoetherianRing C] (S : Set (PrimeSpectrum C))
    (hS : ∀ x y : PrimeSpectrum C, x.asIdeal ≤ y.asIdeal → (x ∈ S ↔ y ∈ S)) : IsClopen S := by
  refine ⟨isClosed_of_forall_le_iff S hS, ?_⟩
  rw [← isClosed_compl_iff]
  exact isClosed_of_forall_le_iff Sᶜ fun x y hxy => not_congr (hS x y hxy)

section Cover

variable {C : Type u} [CommRing C]

theorem ker_comp_of_injective' {A B D : Type*} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D)
    (hg : Function.Injective g) : RingHom.ker (g.comp f) = RingHom.ker f := by
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, RingHom.comp_apply, map_eq_zero_iff g hg]

theorem eq_ite_of_isIdempotentElem {Ω : Type*} [Field Ω] {x : Ω} (hx : IsIdempotentElem x) (p : Prop) [Decidable p]
    (h : x ≠ 0 ↔ p) : x = if p then 1 else 0 := by
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hx with h0 | h1
  · rw [if_neg (fun hp => (h.mpr hp) h0), h0]
  · rw [if_pos (h.mp (h1 ▸ one_ne_zero)), h1]

def goodLocus (r : C) (cC : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω], (C →+* Ω) → Ω) : Set (PrimeSpectrum C) :=
  {𝔔 | ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (χ : C →+* Ω), RingHom.ker χ = 𝔔.asIdeal → cC Ω χ = χ r}

variable (r : C) (cC : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω], (C →+* Ω) → Ω)
  (hvC : ∀ (K : Type u) [Field K] [IsAlgClosed K] (𝒪 : ValuationSubring K)
      (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ρ : C →+* 𝒪) (ψ : 𝒪 →+* Ω),
      ∃ u : 𝒪, cC K ((algebraMap 𝒪 K).comp ρ) = algebraMap 𝒪 K u ∧ cC Ω (ψ.comp ρ) = ψ u)

include hvC in
theorem mem_goodLocus_iff (𝔔 : PrimeSpectrum C) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (χ : C →+* Ω)
    (hχ : RingHom.ker χ = 𝔔.asIdeal) : 𝔔 ∈ goodLocus r cC ↔ cC Ω χ = χ r := by
  have hP : ∀ (Ω Ω' : Type u) [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω'] (χ : C →+* Ω)
      (σ : Ω →+* Ω'), (cC Ω χ = χ r) ↔ (cC Ω' (σ.comp χ) = (σ.comp χ) r) := by
    intro Ω Ω' _ _ _ _ χ σ
    rw [apply_comp_eq_of_hv cC hvC χ σ, RingHom.comp_apply]
    exact (σ.injective.eq_iff).symm
  refine ⟨fun h => h Ω χ hχ, fun h Ω' _ _ χ' hχ' => ?_⟩
  exact (iff_of_ker_eq (fun Ω _ _ χ => cC Ω χ = χ r) hP χ χ' (hχ.trans hχ'.symm)).mp h

abbrev QD (𝔔 : PrimeSpectrum C) : Type u := C ⧸ 𝔔.asIdeal

abbrev FD (𝔔 : PrimeSpectrum C) : Type u := FractionRing (QD 𝔔)

abbrev KD (𝔔 : PrimeSpectrum C) : Type u := AlgebraicClosure (FD 𝔔)

abbrev Q1 (𝔔 𝔔' : PrimeSpectrum C) : Ideal (QD 𝔔) := Ideal.map (Ideal.Quotient.mk 𝔔.asIdeal) 𝔔'.asIdeal

abbrev LD (𝔔 𝔔' : PrimeSpectrum C) (h : (Q1 𝔔 𝔔').IsPrime) : Type u := @Localization.AtPrime _ _ (Q1 𝔔 𝔔') h

abbrev RD {K : Type u} [Field K] (A : ValuationSubring K) : Type u := AlgebraicClosure (IsLocalRing.ResidueField A)

include hvC in

theorem mem_goodLocus_iff_of_le {n : ℕ} (hnC : IsUnit ((n : ℕ) : C)) (hr : r ^ n = 1)
    (hcC : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (χ : C →+* Ω), cC Ω χ ^ n = 1)
    (𝔔 𝔔' : PrimeSpectrum C) (hle : 𝔔.asIdeal ≤ 𝔔'.asIdeal) :
    𝔔 ∈ goodLocus r cC ↔ 𝔔' ∈ goodLocus r cC := by
  classical
  let q : C →+* QD 𝔔 := Ideal.Quotient.mk 𝔔.asIdeal
  haveI h𝔔₁ : (Q1 𝔔 𝔔').IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hle)
  have hcomap : Ideal.comap q (Q1 𝔔 𝔔') = 𝔔'.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, sup_eq_left]
    exact le_trans (le_of_eq (Ideal.mk_ker : RingHom.ker q = 𝔔.asIdeal)) hle
  let g : QD 𝔔 →+* KD 𝔔 := (algebraMap (FD 𝔔) (KD 𝔔)).comp (algebraMap (QD 𝔔) (FD 𝔔))
  have hg : Function.Injective g :=
    (algebraMap (FD 𝔔) (KD 𝔔)).injective.comp (IsFractionRing.injective (QD 𝔔) (FD 𝔔))
  have hgu : ∀ y : (Q1 𝔔 𝔔').primeCompl, IsUnit (g y) := by
    intro y
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    have hy0 : (y : QD 𝔔) = 0 := hg (by rw [h0, map_zero])
    exact y.2 (hy0 ▸ (Q1 𝔔 𝔔').zero_mem)
  let fL : LD 𝔔 𝔔' h𝔔₁ →+* KD 𝔔 := IsLocalization.lift (M := (Q1 𝔔 𝔔').primeCompl) hgu
  have hfL : ∀ d : QD 𝔔, fL (algebraMap (QD 𝔔) (LD 𝔔 𝔔' h𝔔₁) d) = g d := fun d => IsLocalization.lift_eq hgu d
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing fL
  let fA : LD 𝔔 𝔔' h𝔔₁ →+* A.toSubring := fL.codRestrict A.toSubring hA
  haveI : IsLocalHom fA := hloc
  let ρC : C →+* A := toValuationSubring (fL.comp ((algebraMap (QD 𝔔) (LD 𝔔 𝔔' h𝔔₁)).comp q)) A (fun x => hA _)
  have hinjA : Function.Injective (algebraMap A (KD 𝔔)) := IsFractionRing.injective A (KD 𝔔)
  have hρC : ∀ x, algebraMap A (KD 𝔔) (ρC x) = g (q x) := fun x => by
    change fL (algebraMap (QD 𝔔) (LD 𝔔 𝔔' h𝔔₁) (q x)) = g (q x)
    exact hfL _
  have hρC_unit : ∀ x, IsUnit (ρC x) ↔ IsUnit (algebraMap (QD 𝔔) (LD 𝔔 𝔔' h𝔔₁) (q x)) := fun x => by
    have : IsUnit (ρC x) ↔ IsUnit (fA (algebraMap (QD 𝔔) (LD 𝔔 𝔔' h𝔔₁) (q x))) := Iff.rfl
    rw [this, isUnit_map_iff fA]
  let ψ : A →+* RD A := (algebraMap (IsLocalRing.ResidueField A) (RD A)).comp (IsLocalRing.residue A)

  have hK1 : RingHom.ker ((algebraMap A (KD 𝔔)).comp ρC) = 𝔔.asIdeal := by
    ext x
    rw [RingHom.mem_ker, RingHom.comp_apply, hρC, map_eq_zero_iff g hg, Ideal.Quotient.eq_zero_iff_mem]
  have hK2 : RingHom.ker (ψ.comp ρC) = 𝔔'.asIdeal := by
    ext x
    have h1 : x ∈ RingHom.ker (ψ.comp ρC) ↔ ρC x ∈ IsLocalRing.maximalIdeal A := by
      rw [RingHom.mem_ker, RingHom.comp_apply]
      change algebraMap _ (RD A) (IsLocalRing.residue A (ρC x)) = 0 ↔ _
      rw [map_eq_zero_iff _ (algebraMap (IsLocalRing.ResidueField A) (RD A)).injective,
        IsLocalRing.residue_eq_zero_iff]
    have h2 : ρC x ∈ IsLocalRing.maximalIdeal A ↔ ¬ IsUnit (algebraMap (QD 𝔔) (LD 𝔔 𝔔' h𝔔₁) (q x)) := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hρC_unit]
    have h3 : IsUnit (algebraMap (QD 𝔔) (LD 𝔔 𝔔' h𝔔₁) (q x)) ↔ q x ∈ (Q1 𝔔 𝔔').primeCompl :=
      IsLocalization.AtPrime.isUnit_to_map_iff (LD 𝔔 𝔔' h𝔔₁) (Q1 𝔔 𝔔') (q x)
    rw [h1, h2, h3, ← hcomap, Ideal.mem_comap]
    exact not_not

  obtain ⟨u, hu1, hu2⟩ := hvC (KD 𝔔) A (RD A) ρC ψ
  let x₀ : A := ρC r
  have hx₀n : x₀ ^ n = 1 := by
    change ρC r ^ n = 1
    rw [← map_pow, hr, map_one]
  have hnA : IsUnit ((n : ℕ) : A) := by simpa using hnC.map ρC
  have hun : u ^ n = 1 := by
    apply hinjA
    rw [map_pow, ← hu1, map_one]
    exact hcC (KD 𝔔) _
  have e1 : 𝔔 ∈ goodLocus r cC ↔ u = x₀ := by
    rw [mem_goodLocus_iff r cC hvC 𝔔 ((algebraMap A (KD 𝔔)).comp ρC) hK1, hu1, RingHom.comp_apply]
    exact hinjA.eq_iff
  have e2 : 𝔔' ∈ goodLocus r cC ↔ u = x₀ := by
    rw [mem_goodLocus_iff r cC hvC 𝔔' (ψ.comp ρC) hK2, hu2, RingHom.comp_apply]
    change ψ u = ψ x₀ ↔ u = x₀
    constructor
    · intro h
      apply eq_of_pow_eq_one_of_sub_mem_maximalIdeal hnA hun hx₀n
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact (algebraMap (IsLocalRing.ResidueField A) (RD A)).injective h
    · rintro rfl; rfl
  exact e1.trans e2.symm

include hvC in

theorem exists_idempotent_goodLocus [IsNoetherianRing C] {n : ℕ} (hnC : IsUnit ((n : ℕ) : C)) (hr : r ^ n = 1)
    (hcC : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (χ : C →+* Ω), cC Ω χ ^ n = 1) :
    ∃ e : C, IsIdempotentElem e ∧ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [DecidableEq Ω] (χ : C →+* Ω),
      χ e = if cC Ω χ = χ r then 1 else 0 := by
  have hZ : IsClopen (goodLocus r cC) :=
    isClopen_of_forall_le_iff _ (mem_goodLocus_iff_of_le r cC hvC hnC hr hcC)
  obtain ⟨e, he, hZe⟩ := PrimeSpectrum.isClopen_iff.mp hZ
  refine ⟨e, he, fun Ω _ _ _ χ => ?_⟩
  haveI := RingHom.ker_isPrime χ
  let 𝔔 : PrimeSpectrum C := ⟨RingHom.ker χ, inferInstance⟩
  apply eq_ite_of_isIdempotentElem (he.map χ)
  rw [← mem_goodLocus_iff r cC hvC 𝔔 χ rfl, hZe]
  change χ e ≠ 0 ↔ 𝔔 ∈ PrimeSpectrum.basicOpen e
  rw [PrimeSpectrum.mem_basicOpen]
  rfl

end Cover

section Main

noncomputable def cycPoly (R : Type u) [CommRing R] (n : ℕ) : R[X] := X ^ n - 1

variable {R : Type u} [CommRing R]

theorem cycPoly_monic [Nontrivial R] {n : ℕ} (hn : n ≠ 0) : (cycPoly R n).Monic := by
  simpa only [cycPoly, map_one] using Polynomial.monic_X_pow_sub_C (1 : R) hn

theorem cycPoly_natDegree [Nontrivial R] (n : ℕ) : (cycPoly R n).natDegree = n := by
  simpa only [cycPoly, map_one] using Polynomial.natDegree_X_pow_sub_C (n := n) (r := (1 : R))

theorem main (hR : IsNoetherianRing R) (n : ℕ) (hn : IsUnit ((n : ℕ) : R))
    (c : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω], (R →+* Ω) → Ω)
    (hc : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω), c Ω φ ^ n = 1)
    (hv : ∀ (K : Type u) [Field K] [IsAlgClosed K] (𝒪 : ValuationSubring K)
      (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ρ : R →+* 𝒪) (ψ : 𝒪 →+* Ω),
      ∃ u : 𝒪, c K ((algebraMap 𝒪 K).comp ρ) = algebraMap 𝒪 K u ∧ c Ω (ψ.comp ρ) = ψ u) :
    ∃ ε : R, ε ^ n = 1 ∧ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω), c Ω φ = φ ε := by
  classical

  rcases subsingleton_or_nontrivial R with hR0 | hR0
  · refine ⟨1, Subsingleton.elim _ _, fun Ω _ _ φ => ?_⟩
    have h10 : (1 : Ω) = 0 := by rw [← map_one φ, Subsingleton.elim (1 : R) 0, map_zero]
    exact absurd h10 one_ne_zero

  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · rw [Nat.cast_zero, isUnit_zero_iff] at hn
    exact absurd hn zero_ne_one
  have hn0' : n ≠ 0 := hn0.ne'

  have hf : (cycPoly R n).Monic := cycPoly_monic hn0'
  have hfdeg : (cycPoly R n).natDegree = n := cycPoly_natDegree n
  have hf1 : cycPoly R n ≠ 1 := by
    intro h
    have := congrArg Polynomial.natDegree h
    rw [hfdeg, natDegree_one] at this
    exact hn0' this
  let j : R →+* AdjoinRoot (cycPoly R n) := AdjoinRoot.of (cycPoly R n)
  let r : AdjoinRoot (cycPoly R n) := AdjoinRoot.root (cycPoly R n)
  have hr : r ^ n = 1 := by
    have h0 := AdjoinRoot.eval₂_root (cycPoly R n)
    unfold cycPoly at h0
    rw [eval₂_sub, eval₂_X_pow, eval₂_one, sub_eq_zero] at h0
    exact h0
  have hnC : IsUnit ((n : ℕ) : AdjoinRoot (cycPoly R n)) := by simpa using hn.map j
  let cC : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω], (AdjoinRoot (cycPoly R n) →+* Ω) → Ω :=
    fun Ω _ _ χ => c Ω (χ.comp j)
  have hcC : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (χ : AdjoinRoot (cycPoly R n) →+* Ω), cC Ω χ ^ n = 1 :=
    fun Ω _ _ χ => hc Ω _
  have hvC : ∀ (K : Type u) [Field K] [IsAlgClosed K] (𝒪 : ValuationSubring K)
      (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ρ : AdjoinRoot (cycPoly R n) →+* 𝒪) (ψ : 𝒪 →+* Ω),
      ∃ u : 𝒪, cC K ((algebraMap 𝒪 K).comp ρ) = algebraMap 𝒪 K u ∧ cC Ω (ψ.comp ρ) = ψ u :=
    fun K _ _ 𝒪 Ω _ _ ρ ψ => hv K 𝒪 Ω (ρ.comp j) ψ
  obtain ⟨e, he, hread⟩ := exists_idempotent_goodLocus r cC hvC hnC hr hcC

  let et : R[X] := AdjoinRoot.modByMonicHom hf e
  have het : AdjoinRoot.mk (cycPoly R n) et = e := AdjoinRoot.mk_leftInverse hf e
  have hetdeg : et.natDegree < n := by
    obtain ⟨g, hg⟩ := AdjoinRoot.mk_surjective (g := cycPoly R n) e
    have : et = g %ₘ cycPoly R n := by
      change AdjoinRoot.modByMonicHom hf e = _
      rw [← hg]
      exact AdjoinRoot.modByMonicHom_mk hf g
    rw [this]
    exact lt_of_lt_of_eq (Polynomial.natDegree_modByMonic_lt g hf hf1) hfdeg
  let ε₀ : R := (n : R) * et.coeff (n - 1)
  have hε₀ : ∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω), φ ε₀ = c Ω φ := by
    intro Ω _ _ φ
    haveI : NeZero ((n : ℕ) : Ω) := ⟨by simpa using (hn.map φ).ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω n

    have hroot : ∀ i : ℕ, Polynomial.eval₂ φ (ζ ^ i) (cycPoly R n) = 0 := fun i => by
      show Polynomial.eval₂ φ (ζ ^ i) (X ^ n - 1) = 0
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one, ← pow_mul, mul_comm, pow_mul,
        hζ.pow_eq_one, one_pow, sub_self]
    let χ : ℕ → (AdjoinRoot (cycPoly R n) →+* Ω) := fun i => AdjoinRoot.lift φ (ζ ^ i) (hroot i)
    have hχj : ∀ i, (χ i).comp j = φ := fun i => RingHom.ext fun x => AdjoinRoot.lift_of (hroot i)
    have hχr : ∀ i, χ i r = ζ ^ i := fun i => AdjoinRoot.lift_root (hroot i)
    have hχe : ∀ i, χ i e = (et.map φ).eval (ζ ^ i) := fun i => by
      rw [← het, AdjoinRoot.lift_mk, Polynomial.eval₂_eq_eval_map]

    have hdeg' : (et.map φ).natDegree < n := lt_of_le_of_lt (Polynomial.natDegree_map_le) hetdeg
    have hsum := sum_range_mul_eval_eq hζ hn0 (et.map φ) hdeg'
    rw [Polynomial.coeff_map] at hsum
    change φ ((n : R) * et.coeff (n - 1)) = c Ω φ
    rw [map_mul, map_natCast, ← hsum]
    have hterm : ∀ i ∈ Finset.range n,
        ζ ^ i * (et.map φ).eval (ζ ^ i) = if ζ ^ i = c Ω φ then c Ω φ else 0 := by
      intro i _
      have hi := hread Ω (χ i)
      rw [hχr] at hi
      have hi' : (et.map φ).eval (ζ ^ i) = if c Ω φ = ζ ^ i then 1 else 0 := by
        rw [← hχe, hi]
        change (if c Ω ((χ i).comp j) = ζ ^ i then (1 : Ω) else 0) = _
        rw [hχj]
      rw [hi']
      by_cases h : ζ ^ i = c Ω φ
      · rw [if_pos h.symm, if_pos h, mul_one, h]
      · rw [if_neg (Ne.symm h), if_neg h, mul_zero]
    rw [Finset.sum_congr rfl hterm]
    haveI : NeZero n := ⟨hn0'⟩
    obtain ⟨i₀, hi₀, hi₀'⟩ := hζ.eq_pow_of_pow_eq_one (hc Ω φ)
    rw [Finset.sum_eq_single i₀, if_pos hi₀']
    · intro i hi hne
      rw [if_neg]
      intro h
      exact hne (hζ.pow_inj (Finset.mem_range.mp hi) hi₀ (h.trans hi₀'.symm))
    · intro h
      exact absurd (Finset.mem_range.mpr hi₀) h

  have hnil : IsNilpotent (ε₀ ^ n - 1) := by
    rw [nilpotent_iff_mem_prime]
    intro J hJ
    let Ω := AlgebraicClosure (FractionRing (R ⧸ J))
    let φ : R →+* Ω :=
      (algebraMap (FractionRing (R ⧸ J)) Ω).comp ((algebraMap (R ⧸ J) _).comp (Ideal.Quotient.mk J))
    have hker : RingHom.ker φ = J := by
      change RingHom.ker ((algebraMap (FractionRing (R ⧸ J)) Ω).comp
        ((algebraMap (R ⧸ J) _).comp (Ideal.Quotient.mk J))) = J
      rw [ker_comp_of_injective' _ _ (RingHom.injective _),
        ker_comp_of_injective' _ _ (IsFractionRing.injective (R ⧸ J) (FractionRing (R ⧸ J))), Ideal.mk_ker]
    rw [← hker, RingHom.mem_ker, map_sub, map_pow, hε₀ φ, hc, map_one, sub_self]
  obtain ⟨ε, hε, hεε₀⟩ := exists_pow_eq_one_of_isNilpotent hn ε₀ hnil
  refine ⟨ε, hε, fun Ω _ _ φ => ?_⟩
  have h0 : φ (ε - ε₀) = 0 := (hεε₀.map φ).eq_zero
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, hε₀ φ]

end Main

end P2M.MuSpread
p2m_reactivate "P2MW.S_IsNoetherianRing_exists_pow_eq_one_and_forall_apply_eq_of_forall_valuationSubring.P2M P2MW.S_IsNoetherianRing_exists_pow_eq_one_and_forall_apply_eq_of_forall_valuationSubring.P2M.MuSpread"
p2m_reactivate "P2MW.S_IsNoetherianRing_exists_pow_eq_one_and_forall_apply_eq_of_forall_valuationSubring.P2M"

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ) (hn : IsUnit ((n : ℕ) : R))
    (c : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω], (R →+* Ω) → Ω)
    (hc : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω), c Ω φ ^ n = 1)
    (hv : ∀ (K : Type u) [Field K] [IsAlgClosed K] (𝒪 : ValuationSubring K)
      (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (ρ : R →+* 𝒪) (ψ : 𝒪 →+* Ω),
      ∃ u : 𝒪, c K ((algebraMap 𝒪 K).comp ρ) = algebraMap 𝒪 K u ∧ c Ω (ψ.comp ρ) = ψ u) :
    ∃ ε : R, ε ^ n = 1 ∧ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (φ : R →+* Ω), c Ω φ = φ ε :=
  P2M.MuSpread.main ‹IsNoetherianRing R› n hn c hc hv

end S_IsNoetherianRing_exists_pow_eq_one_and_forall_apply_eq_of_forall_valuationSubring
end P2MW
export P2MW.S_IsNoetherianRing_exists_pow_eq_one_and_forall_apply_eq_of_forall_valuationSubring (solution)
