-- Prove2me | solution 1 for Int.natCast_dvd_of_forall_frobeniusLift_pow_fixed_apply_zpow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/4340298e-6109-5a3d-89be-729bb048a7ba

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Int_natCast_dvd_of_forall_frobeniusLift_pow_fixed_apply_zpow_eq

set_option autoImplicit false

open Polynomial

namespace F12Sol

theorem root_unique {R : Type*} [CommRing R] [IsDomain R] (I : Ideal R) (hI : I ≠ ⊤) (N : ℕ) (hN : (N : R) ∈ I)
    {a b : R} (ha : a ^ N = a) (hb : b ^ N = b) (hab : a - b ∈ I) : a = b := by
  classical
  have hgeom := geom_sum₂_mul a b N
  rw [ha, hb] at hgeom
  set g := ∑ i ∈ Finset.range N, a ^ i * b ^ (N - 1 - i) with hg
  have h1 : (g - 1) * (a - b) = 0 := by rw [sub_mul, one_mul, hgeom, sub_self]
  rcases mul_eq_zero.mp h1 with h2 | h2
  ·
    exfalso
    apply hI
    rw [Ideal.eq_top_iff_one]
    have hgI : g ∈ I := by

      have hba : Ideal.Quotient.mk I b = Ideal.Quotient.mk I a := by
        rw [Ideal.Quotient.eq]; rw [← Ideal.neg_mem_iff, neg_sub]; exact hab
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      rw [hg, map_sum]
      have : ∀ i ∈ Finset.range N, Ideal.Quotient.mk I (a ^ i * b ^ (N - 1 - i)) = Ideal.Quotient.mk I a ^ (N - 1) := by
        intro i hi
        rw [map_mul, map_pow, map_pow, hba, ← pow_add, Nat.add_sub_cancel' (Nat.le_sub_one_of_lt (Finset.mem_range.mp hi))]
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem.mpr hN, zero_mul]
    have : (1 : R) = g - (g - 1) := by ring
    rw [this, h2, sub_zero]
    exact hgI
  · exact sub_eq_zero.mp h2

theorem zpow_apply_of_apply_eq {𝒪 : Type*} [CommRing 𝒪] {R : Type*} [CommRing R] [Algebra 𝒪 R] (g : R ≃ₐ[𝒪] R) {x : R}
    (hx : g x = x) (m : ℤ) : (g ^ m) x = x := by
  have hnat : ∀ k : ℕ, (g ^ k) x = x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [zpow_natCast]; exact hnat k
  · rw [zpow_neg, zpow_natCast, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
    exact (hnat k).symm

end F12Sol

theorem solution
    {r : ℕ} [Fact r.Prime]
    {𝒪 : Type} [CommRing 𝒪] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hr : ((r : ℕ) : Onr) ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (k : Type) [Field k] (ψ : Onr →+* k) (hψ : ψ (algebraMap 𝒪 Onr π) = 0)
    (d : ℕ) (hd : 0 < d) (v : ℤ)
    (h : ∀ y : Onr, (Fr ^ (d : ℤ)) y = y → ψ ((Fr ^ (-v)) y) = ψ y) :
    (d : ℤ) ∣ v := by
  classical
  set I : Ideal Onr := Ideal.span {algebraMap 𝒪 Onr π} with hIdef
  haveI : I.IsMaximal := hOnr_max
  haveI : IsAdicComplete I Onr := hOnr_complete
  letI : Field (Onr ⧸ I) := Ideal.Quotient.field I
  have hI : I ≠ ⊤ := Ideal.IsMaximal.ne_top hOnr_max
  have hr1 : 1 < r := (Fact.out : r.Prime).one_lt

  have hrκ : ((r : ℕ) : Onr ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]; exact hr
  haveI : CharP (Onr ⧸ I) r := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hrκ

  have hφ : ∀ x : Onr, Ideal.Quotient.mk I (Fr x) = Ideal.Quotient.mk I x ^ r := fun x => by
    rw [← map_pow, Ideal.Quotient.eq]; exact hFr x
  have hφn : ∀ (j : ℕ) (x : Onr), Ideal.Quotient.mk I ((Fr ^ j) x) = Ideal.Quotient.mk I x ^ (r ^ j) := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih => intro x; rw [pow_succ, AlgEquiv.mul_apply, ih, hφ, ← pow_mul, ← pow_succ']

  have hker : I = RingHom.ker ψ := by
    refine hOnr_max.eq_of_le (RingHom.ker_ne_top ψ) ?_
    rw [hIdef, Ideal.span_le, Set.singleton_subset_iff]
    exact hψ
  have hinj : ∀ x y : Onr, ψ x = ψ y → Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := by
    intro x y hxy
    rw [Ideal.Quotient.eq, hker, RingHom.mem_ker, map_sub, hxy, sub_self]

  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  set n : ℕ := ((-v) % (d : ℤ)).toNat with hndef
  have hn_nonneg : 0 ≤ (-v) % (d : ℤ) := Int.emod_nonneg _ hd0
  have hncast : (n : ℤ) = (-v) % (d : ℤ) := by rw [hndef, Int.toNat_of_nonneg hn_nonneg]
  have hnlt : n < d := by
    have := Int.emod_lt_of_pos (-v) (by exact_mod_cast hd : (0 : ℤ) < d)
    omega
  have hdecomp : -v = (n : ℤ) + (d : ℤ) * ((-v) / (d : ℤ)) := by rw [hncast]; exact (Int.emod_add_mul_ediv _ _).symm
  by_cases hn0 : n = 0
  ·
    rw [hn0, Int.natCast_zero, zero_add] at hdecomp
    have : (d : ℤ) ∣ -v := ⟨_, hdecomp⟩
    exact (Int.dvd_neg).mp this
  exfalso
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0

  haveI : IsAlgClosed (Onr ⧸ I) := by
    refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
    have hl : p ∈ Polynomial.lifts (Ideal.Quotient.mk I) :=
      (Polynomial.mem_lifts _).mpr (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective p)
    obtain ⟨P, hPmap, hPdeg, hPmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hp
    obtain ⟨x, hx⟩ := hOnr_closed P hPmonic (by rw [hPdeg]; exact hirr.natDegree_pos)
    refine ⟨Ideal.Quotient.mk I x, ?_⟩
    rw [← hPmap, Polynomial.eval_map, Polynomial.eval₂_at_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact hx

  set N : ℕ := r ^ d with hNdef
  have hN1 : 1 < N := Nat.one_lt_pow hd.ne' hr1
  have hrn1 : 1 < r ^ n := Nat.one_lt_pow hnpos.ne' hr1
  obtain ⟨abar, habar, habar'⟩ : ∃ abar : Onr ⧸ I, abar ^ N = abar ∧ abar ^ (r ^ n) ≠ abar := by
    by_contra hall
    push Not at hall

    have hS : (X ^ N - X : (Onr ⧸ I)[X]).roots.card = N := by
      have h1 := Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits (X ^ N - X : (Onr ⧸ I)[X]))
      rw [FiniteField.X_pow_card_sub_X_natDegree_eq (Onr ⧸ I) hN1] at h1
      exact h1
    have hSnd : (X ^ N - X : (Onr ⧸ I)[X]).roots.Nodup :=
      Polynomial.nodup_roots (galois_poly_separable r N (dvd_pow_self r hd.ne'))
    have hT : (X ^ (r ^ n) - X : (Onr ⧸ I)[X]).roots.card ≤ r ^ n := by
      have := Polynomial.card_roots' (X ^ (r ^ n) - X : (Onr ⧸ I)[X])
      rwa [FiniteField.X_pow_card_sub_X_natDegree_eq (Onr ⧸ I) hrn1] at this
    have hsub : (X ^ N - X : (Onr ⧸ I)[X]).roots ≤ (X ^ (r ^ n) - X : (Onr ⧸ I)[X]).roots := by
      rw [Multiset.le_iff_subset hSnd]
      intro a ha
      rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero (Onr ⧸ I) hN1), Polynomial.IsRoot,
        eval_sub, eval_pow, eval_X, sub_eq_zero] at ha
      rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero (Onr ⧸ I) hrn1), Polynomial.IsRoot,
        eval_sub, eval_pow, eval_X, sub_eq_zero]
      exact hall a ha
    have := Multiset.card_le_card hsub
    rw [hS] at this
    have : r ^ d ≤ r ^ n := this.trans hT
    exact absurd (Nat.pow_lt_pow_right hr1 hnlt) (not_lt.mpr this)

  obtain ⟨a₀, ha₀⟩ := Ideal.Quotient.mk_surjective abar
  set f : Onr[X] := X ^ N - X with hfdef
  have hfmonic : f.Monic := Polynomial.monic_X_pow_sub (by rw [degree_X]; exact_mod_cast hN1)
  have hfeval : ∀ x : Onr, f.eval x = x ^ N - x := fun x => by simp [hfdef]
  have hNI : ((N : ℕ) : Onr) ∈ I := by
    rw [hNdef, Nat.cast_pow]; exact Ideal.pow_mem_of_mem I hr d hd
  have heval₀ : f.eval a₀ ∈ I := by
    rw [hfeval, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, ha₀, habar, sub_self]
  have hNκ : ((N : ℕ) : Onr ⧸ I) = 0 := by rw [hNdef, Nat.cast_pow, hrκ, zero_pow hd.ne']
  have hderiv : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀)) := by
    have : f.derivative.eval a₀ = (N : Onr) * a₀ ^ (N - 1) - 1 := by
      simp [hfdef, derivative_X_pow]
    rw [this, map_sub, map_mul, map_natCast, map_one, hNκ, zero_mul, zero_sub]
    exact isUnit_one.neg
  obtain ⟨ω, hωroot, hωa₀⟩ := HenselianRing.is_henselian (I := I) f hfmonic a₀ heval₀ hderiv
  have hωN : ω ^ N = ω := by
    have := hωroot; rw [Polynomial.IsRoot, hfeval, sub_eq_zero] at this; exact this
  have hωbar : Ideal.Quotient.mk I ω = abar := by rw [← ha₀, Ideal.Quotient.eq]; exact hωa₀

  have hfix : (Fr ^ d) ω = ω := by
    apply F12Sol.root_unique I hI N hNI _ hωN
    · rw [← Ideal.Quotient.eq, hφn, hωbar, ← hNdef, habar]
    · rw [← map_pow, hωN]
  have hfixz : (Fr ^ (d : ℤ)) ω = ω := by rw [zpow_natCast]; exact hfix

  have hh := h ω hfixz
  have hzv : (Fr ^ (-v)) ω = (Fr ^ n) ω := by
    rw [hdecomp, zpow_add, zpow_mul, zpow_natCast, AlgEquiv.mul_apply,
      F12Sol.zpow_apply_of_apply_eq (Fr ^ (d : ℤ)) hfixz]
  rw [hzv] at hh
  have := hinj _ _ hh
  rw [hφn, hωbar] at this
  exact habar' this

end S_Int_natCast_dvd_of_forall_frobeniusLift_pow_fixed_apply_zpow_eq
end P2MW
export P2MW.S_Int_natCast_dvd_of_forall_frobeniusLift_pow_fixed_apply_zpow_eq (solution)
