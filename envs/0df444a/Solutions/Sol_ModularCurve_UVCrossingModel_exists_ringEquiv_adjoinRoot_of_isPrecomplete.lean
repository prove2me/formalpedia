-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_ringEquiv_adjoinRoot_of_isPrecomplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/82818130-723f-5f9a-bae0-94ac2d8ab867

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingChart
import Theorems.Thm_ModularCurve_UVCrossingModel_chartHom_X
import Theorems.Thm_ModularCurve_UVCrossingModel_chartHom_C
import Theorems.Thm_ModularCurve_UVCrossingModel_U_quadratic
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_mem_fixedSubring_eq_add_mul_U
import Theorems.Thm_ModularCurve_UVCrossingModel_range_chartHom_eq_fixedSubring
import Theorems.Thm_ModularCurve_UVCrossingModel_chartHom_injective
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_uvSwapEquiv_eq_and_mk_eq_of_mem_fixedSubring
import Theorems.Thm_MvPowerSeries_exists_rename_swap_eq_add_mul_X
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Theorems.Thm_ModularCurve_UVCrossingModel_isLocalRing_of_not_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adjoinRoot_of_isPrecomplete

set_option autoImplicit false

namespace MvPowerSeries
p2m_export "MvPowerSeries" "eval₂_C coeff rename_X C X coeff_mul_monomial constantCoeff constantCoeff_C monomial rename constantCoeff_X ext eval₂_X eval₂ exists_rename_swap_eq_add_mul_X"
p2m_open "MvPowerSeries"

open Finsupp

variable {W : Type*} [CommRing W]

private noncomputable abbrev ij (i j : ℕ) : Fin 2 →₀ ℕ := single 0 i + single 1 j

private theorem ij_eq (d : Fin 2 →₀ ℕ) : d = ij (d 0) (d 1) := by
  ext k
  fin_cases k <;> simp [ij]

private theorem coeff_mul_X_zero_sub_X_one (h : MvPowerSeries (Fin 2) W) (i j : ℕ) :
    coeff (ij i j) (h * (X 0 - X 1)) =
      (if 1 ≤ i then coeff (ij (i - 1) j) h else 0) - (if 1 ≤ j then coeff (ij i (j - 1)) h else 0) := by
  rw [mul_sub, map_sub]
  have hX0 : (X 0 : MvPowerSeries (Fin 2) W) = monomial (single 0 1) 1 := rfl
  have hX1 : (X 1 : MvPowerSeries (Fin 2) W) = monomial (single 1 1) 1 := rfl
  congr 1
  · rw [hX0, coeff_mul_monomial, mul_one]
    by_cases hi : 1 ≤ i
    · have heq : ij i j - single 0 1 = ij (i - 1) j := by
        ext k; fin_cases k <;> simp [ij]
      rw [if_pos, if_pos hi, heq]
      intro k; fin_cases k <;> simp [ij, hi]
    · rw [if_neg, if_neg hi]
      intro hle; apply hi; simpa [ij] using hle 0
  · rw [hX1, coeff_mul_monomial, mul_one]
    by_cases hj : 1 ≤ j
    · have heq : ij i j - single 1 1 = ij i (j - 1) := by
        ext k; fin_cases k <;> simp [ij]
      rw [if_pos, if_pos hj, heq]
      intro k; fin_cases k <;> simp [ij, hj]
    · rw [if_neg, if_neg hj]
      intro hle; apply hj; simpa [ij] using hle 1

theorem eq_zero_of_mul_X_zero_sub_X_one_eq_zero (h : MvPowerSeries (Fin 2) W)
    (hh : h * (X 0 - X 1) = 0) : h = 0 := by
  have key : ∀ j i : ℕ, coeff (ij i j) h = 0 := by
    intro j
    induction j with
    | zero =>
      intro i
      have := congrArg (coeff (ij (i + 1) 0)) hh
      rw [coeff_mul_X_zero_sub_X_one, map_zero] at this
      simpa using this
    | succ j ih =>
      intro i
      have := congrArg (coeff (ij (i + 1) (j + 1))) hh
      rw [coeff_mul_X_zero_sub_X_one, map_zero] at this
      simp only [le_add_iff_nonneg_left, zero_le, if_true, Nat.add_sub_cancel] at this
      rw [ih (i + 1), sub_zero] at this
      exact this
  ext d
  obtain ⟨i, j, rfl⟩ : ∃ i j, d = ij i j := ⟨d 0, d 1, ij_eq d⟩
  rw [map_zero]
  exact key j i

theorem X_zero_sub_X_one_mem_nonZeroDivisors :
    (X 0 - X 1 : MvPowerSeries (Fin 2) W) ∈ nonZeroDivisors (MvPowerSeries (Fin 2) W) := by
  rw [mem_nonZeroDivisors_iff_right]
  intro h hh
  exact eq_zero_of_mul_X_zero_sub_X_one_eq_zero h hh

theorem eq_of_rename_swap_add_mul_X_eq {A B A' B' : MvPowerSeries (Fin 2) W}
    (hA : rename (⇑(Equiv.swap (0 : Fin 2) 1)) A = A) (hB : rename (⇑(Equiv.swap (0 : Fin 2) 1)) B = B)
    (hA' : rename (⇑(Equiv.swap (0 : Fin 2) 1)) A' = A') (hB' : rename (⇑(Equiv.swap (0 : Fin 2) 1)) B' = B')
    (h : A + B * X 0 = A' + B' * X 0) : A = A' ∧ B = B' := by
  have h1 : (A - A') + (B - B') * X 0 = 0 := by linear_combination h
  have h2 := congrArg (rename (⇑(Equiv.swap (0 : Fin 2) 1))) h1
  rw [map_add, map_mul, map_sub, map_sub, hA, hA', hB, hB', rename_X, Equiv.swap_apply_left,
    map_zero] at h2
  have h3 : (B - B') * (X 0 - X 1) = 0 := by linear_combination h1 - h2
  have hB0 := eq_zero_of_mul_X_zero_sub_X_one_eq_zero _ h3
  have hBB : B = B' := sub_eq_zero.mp hB0
  refine ⟨?_, hBB⟩
  rw [hBB, sub_self, zero_mul, add_zero] at h1
  exact sub_eq_zero.mp h1

end MvPowerSeries

set_option autoImplicit false

open Polynomial

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution {W : Type*} [CommRing W]
    [IsNoetherianRing W] [IsLocalRing W] [IsDomain W]
    (c : W) (hc0 : c ≠ 0) (hcu : ¬IsUnit c) [IsPrecomplete (Ideal.span {c}) W] :
    ∃ e : UVCrossingModel W c ≃+*
        AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (PowerSeries.X : PowerSeries W) * Polynomial.X +
          Polynomial.C (PowerSeries.C c)),
      e (U c) = AdjoinRoot.root _ ∧
      ∀ f : PowerSeries W, e (chartHom c f) = AdjoinRoot.of _ f := by
  set f : (PowerSeries W)[X] := Polynomial.X ^ 2 - Polynomial.C (PowerSeries.X : PowerSeries W) * Polynomial.X +
          Polynomial.C (PowerSeries.C c) with hf

  have heval : Polynomial.eval₂ (chartHom c) (U c) f = 0 := by
    simp only [hf, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, chartHom_X, chartHom_C]
    exact U_quadratic c
  let φ : AdjoinRoot f →+* UVCrossingModel W c := AdjoinRoot.lift (chartHom c) (U c) heval
  have hφroot : φ (AdjoinRoot.root f) = U c := AdjoinRoot.lift_root heval
  have hφof : ∀ g, φ (AdjoinRoot.of f g) = chartHom c g := fun g => AdjoinRoot.lift_of heval

  have hreg : ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C c) ∈
      nonZeroDivisors (MvPowerSeries (Fin 2) W) := by
    apply mem_nonZeroDivisors_of_ne_zero
    intro h; apply hc0
    have := congrArg MvPowerSeries.constantCoeff h
    simpa using this
  have hsepW : ∀ x : W, (∀ n : ℕ, c ^ n ∣ x) → x = 0 := by
    intro x hx
    have hbot := Ideal.iInf_pow_eq_bot_of_isDomain (Ideal.span {c})
      (by rw [Ne, Ideal.span_singleton_eq_top]; exact hcu)
    have : x ∈ ⨅ n : ℕ, Ideal.span {c} ^ n := by
      rw [Ideal.mem_iInf]; intro n
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]; exact hx n
    rw [hbot] at this
    exact this
  haveI : IsNoetherianRing (UVCrossingModel W c) := isNoetherianRing c
  haveI : IsLocalRing (UVCrossingModel W c) := isLocalRing_of_not_isUnit hcu
  have hsepR : ∀ x : UVCrossingModel W c, (∀ B : ℕ, x ∈ Ideal.span {const c c} ^ B) → x = 0 := by
    intro x hx
    have hne : Ideal.span {const c c} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      intro hu

      obtain ⟨y, hy⟩ := hu.exists_right_inv
      obtain ⟨G, rfl⟩ := mk_surjective c y
      change mk c (MvPowerSeries.C c) * mk c G = 1 at hy
      rw [← map_mul, ← map_one (mk c), show mk c = Ideal.Quotient.mk (uvCrossingIdeal W c) from rfl,
        Ideal.Quotient.eq] at hy
      change MvPowerSeries.C c * G - 1 ∈ Ideal.span {_} at hy
      rw [Ideal.mem_span_singleton] at hy
      obtain ⟨H, hH⟩ := hy
      have h0 := congrArg MvPowerSeries.constantCoeff hH
      simp only [map_sub, map_mul, map_one, MvPowerSeries.constantCoeff_C, MvPowerSeries.constantCoeff_X,
        zero_mul, mul_zero, zero_sub] at h0
      apply hcu
      apply isUnit_of_dvd_one
      exact ⟨MvPowerSeries.constantCoeff G + MvPowerSeries.constantCoeff H, by linear_combination (-1 : W) * h0⟩
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {const c c}) hne
    have : x ∈ ⨅ n : ℕ, Ideal.span {const c c} ^ n := by
      rw [Ideal.mem_iInf]; exact hx
    rw [hbot] at this
    exact this
  have hrange := range_chartHom_eq_fixedSubring hreg hsepR
  have hinj := chartHom_injective (mem_nonZeroDivisors_of_ne_zero hc0) hsepW

  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_mem_fixedSubring_eq_add_mul_U c x
    rw [← hrange, RingHom.mem_range] at ha hb
    obtain ⟨ga, rfl⟩ := ha
    obtain ⟨gb, rfl⟩ := hb
    exact ⟨AdjoinRoot.of f ga + AdjoinRoot.of f gb * AdjoinRoot.root f, by
      rw [map_add, map_mul, hφof, hφof, hφroot]⟩

  have huniq : ∀ ga gb : PowerSeries W, chartHom c ga + chartHom c gb * U c = 0 → ga = 0 ∧ gb = 0 := by
    intro ga gb h
    have ha : chartHom c ga ∈ fixedSubring c := hrange ▸ ⟨ga, rfl⟩
    have hb : chartHom c gb ∈ fixedSubring c := hrange ▸ ⟨gb, rfl⟩
    obtain ⟨A, hA, hAe⟩ := exists_uvSwapEquiv_eq_and_mk_eq_of_mem_fixedSubring hreg ha
    obtain ⟨B, hB, hBe⟩ := exists_uvSwapEquiv_eq_and_mk_eq_of_mem_fixedSubring hreg hb
    set q : MvPowerSeries (Fin 2) W := MvPowerSeries.X 0 * MvPowerSeries.X 1 - MvPowerSeries.C c with hqdef
    have hmem : A + B * MvPowerSeries.X 0 ∈ uvCrossingIdeal W c := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      change mk c (A + B * MvPowerSeries.X 0) = 0
      rw [map_add, map_mul, hAe, hBe]
      exact h
    change A + B * MvPowerSeries.X 0 ∈ Ideal.span {q} at hmem
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨H, hH⟩ := hmem
    obtain ⟨P, Q, hP, hQ, rfl⟩ := MvPowerSeries.exists_rename_swap_eq_add_mul_X H
    have hq : MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) q = q := uvSwapEquiv_crossing c
    have hA' : MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) A = A := hA
    have hB' : MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) B = B := hB
    have hqP : MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) (q * P) = q * P := by
      rw [map_mul, hq, hP]
    have hqQ : MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) (q * Q) = q * Q := by
      rw [map_mul, hq, hQ]
    obtain ⟨hAq, hBq⟩ := MvPowerSeries.eq_of_rename_swap_add_mul_X_eq hA' hB' hqP hqQ
      (by rw [hH]; ring)
    have hA0 : chartHom c ga = 0 := by
      rw [← hAe, hAq]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
    have hB0 : chartHom c gb = 0 := by
      rw [← hBe, hBq]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
    exact ⟨hinj (by rw [hA0, map_zero]), hinj (by rw [hB0, map_zero])⟩

  have hmonic : f.Monic := by
    have : f = Polynomial.X ^ 2 + Polynomial.C (-(PowerSeries.X : PowerSeries W)) * Polynomial.X +
      Polynomial.C (PowerSeries.C c) := by rw [hf, Polynomial.C_neg]; ring
    rw [this]; monicity!
  have hdegf : f.natDegree = 2 := by
    have : f = Polynomial.X ^ 2 + Polynomial.C (-(PowerSeries.X : PowerSeries W)) * Polynomial.X +
      Polynomial.C (PowerSeries.C c) := by rw [hf, Polynomial.C_neg]; ring
    rw [this]; compute_degree!
  have hinjφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    have hpmod : AdjoinRoot.mk f p = AdjoinRoot.mk f (p %ₘ f) := by
      rw [AdjoinRoot.mk_eq_mk]
      refine ⟨p /ₘ f, ?_⟩
      have := Polynomial.modByMonic_add_div p f
      linear_combination -this
    have hf1 : f ≠ 1 := by
      intro h1; rw [h1, Polynomial.natDegree_one] at hdegf; exact absurd hdegf (by norm_num)
    have hdeg : (p %ₘ f).natDegree ≤ 1 := by
      have := Polynomial.natDegree_modByMonic_lt p hmonic hf1
      rw [hdegf] at this
      omega
    set r := p %ₘ f with hr
    have hrexp : r = Polynomial.C (r.coeff 1) * Polynomial.X + Polynomial.C (r.coeff 0) :=
      Polynomial.eq_X_add_C_of_natDegree_le_one hdeg
    rw [hpmod] at hz ⊢
    have hz' : chartHom c (r.coeff 0) + chartHom c (r.coeff 1) * U c = 0 := by
      rw [hrexp, map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_add, map_mul,
        hφof, hφof, hφroot] at hz
      linear_combination hz
    obtain ⟨h0, h1⟩ := huniq _ _ hz'
    rw [hrexp, h0, h1]
    simp
  let e' := RingEquiv.ofBijective φ ⟨hinjφ, hsurj⟩
  refine ⟨e'.symm, ?_, ?_⟩
  · rw [RingEquiv.symm_apply_eq]; exact hφroot.symm
  · intro g; rw [RingEquiv.symm_apply_eq]; exact (hφof g).symm

end S_ModularCurve_UVCrossingModel_exists_ringEquiv_adjoinRoot_of_isPrecomplete
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_ringEquiv_adjoinRoot_of_isPrecomplete (solution)
