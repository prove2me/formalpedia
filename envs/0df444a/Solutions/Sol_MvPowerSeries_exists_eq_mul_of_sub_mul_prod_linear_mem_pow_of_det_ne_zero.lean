-- Prove2me | solution 1 for MvPowerSeries.exists_eq_mul_of_sub_mul_prod_linear_mem_pow_of_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/29912fdc-32f3-5d1c-b25c-b316fa9cd7ad

import Mathlib
import Theorems.Thm_MvPowerSeries_exists_algEquiv_apply_X_eq
import Theorems.Thm_MvPowerSeries_span_singleton_isPrime_of_sub_linear_mem_sq
import Theorems.Thm_MvPowerSeries_exists_eq_X_sub_subst_mul_of_subst_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_exists_eq_mul_of_sub_mul_prod_linear_mem_pow_of_det_ne_zero

set_option autoImplicit false

universe u v

open MvPowerSeries

namespace OneBranchGC7

variable {κ : Type u} [Field κ]

def killX1 (p : MvPowerSeries (Fin 2) κ) : MvPowerSeries (Fin 2) κ :=
  fun m => if m 1 = 0 then coeff m p else 0

theorem coeff_killX1 (p : MvPowerSeries (Fin 2) κ) (m : Fin 2 →₀ ℕ) :
    coeff m (killX1 p) = if m 1 = 0 then coeff m p else 0 := rfl

theorem X1_dvd_sub_killX1 (p : MvPowerSeries (Fin 2) κ) : (X 1 : MvPowerSeries (Fin 2) κ) ∣ p - killX1 p := by
  rw [X_dvd_iff]
  intro m hm
  rw [map_sub, coeff_killX1, if_pos hm, sub_self]

theorem killX1_killX1 (p : MvPowerSeries (Fin 2) κ) : killX1 (killX1 p) = killX1 p := by
  ext m; rw [coeff_killX1, coeff_killX1]; split_ifs <;> rfl

theorem constantCoeff_killX1 (p : MvPowerSeries (Fin 2) κ) : constantCoeff (killX1 p) = constantCoeff p := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_killX1, if_pos (by simp), coeff_zero_eq_constantCoeff_apply]

theorem mem_span_X_of_constantCoeff_eq_zero (p : MvPowerSeries (Fin 2) κ) (hp : constantCoeff p = 0) :
    p ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1} := by
  have h1 : p - killX1 p ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1} := by
    obtain ⟨t, ht⟩ := X1_dvd_sub_killX1 p
    rw [ht]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  have h2 : killX1 p ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1} := by
    have : (X 0 : MvPowerSeries (Fin 2) κ) ∣ killX1 p := by
      rw [X_dvd_iff]
      intro m hm0
      rw [coeff_killX1]
      split_ifs with hm1
      · have : m = 0 := by ext i; fin_cases i <;> simp [hm0, hm1]
        rw [this, coeff_zero_eq_constantCoeff_apply, hp]
      · rfl
    obtain ⟨t, ht⟩ := this
    rw [ht]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  simpa using Ideal.add_mem _ h1 h2

theorem map_pow_le {E : MvPowerSeries (Fin 2) κ →ₐ[κ] MvPowerSeries (Fin 2) κ}
    (h0 : constantCoeff (E (X 0)) = 0) (h1 : constantCoeff (E (X 1)) = 0) (k : ℕ) :
    ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ k).map E ≤
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ k := by
  rw [Ideal.map_pow]
  apply Ideal.pow_right_mono
  rw [Ideal.map_span, Ideal.span_le]
  rintro x ⟨y, hy, rfl⟩
  rcases hy with rfl | rfl
  · exact mem_span_X_of_constantCoeff_eq_zero _ h0
  · exact mem_span_X_of_constantCoeff_eq_zero _ h1

theorem le_order_of_mem_pow (m : ℕ) (g : MvPowerSeries (Fin 2) κ)
    (hg : g ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1} ^ m) : (m : ℕ∞) ≤ g.order := by
  induction m generalizing g with
  | zero => simp
  | succ m ih =>
    rw [pow_succ] at hg
    refine Submodule.mul_induction_on hg (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · have h1 : (m : ℕ∞) ≤ a.order := ih a ha
      have h2 : (1 : ℕ∞) ≤ b.order := by
        rw [one_le_order_iff_constCoeff_eq_zero]
        obtain ⟨c₀, c₁, rfl⟩ := Ideal.mem_span_pair.mp hb
        simp
      calc ((m + 1 : ℕ) : ℕ∞) = m + 1 := by push_cast; rfl
        _ ≤ a.order + b.order := add_le_add h1 h2
        _ ≤ (a * b).order := le_order_mul
    · exact le_trans (le_min ha hb) min_order_le_add

theorem mem_pow_of_le_order (m : ℕ) : ∀ (g : MvPowerSeries (Fin 2) κ), (m : ℕ∞) ≤ g.order →
    g ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1} ^ m := by
  induction m with
  | zero => intro g _; simp
  | succ m ih =>
    intro g hg
    have hg1 : (1 : ℕ∞) ≤ g.order := le_trans (by exact_mod_cast Nat.le_add_left 1 m) hg

    obtain ⟨t, ht⟩ := X1_dvd_sub_killX1 g
    have hk0 : constantCoeff (killX1 g) = 0 := by
      rw [constantCoeff_killX1]; exact one_le_order_iff_constCoeff_eq_zero.mp hg1
    have hX0dvd : (X 0 : MvPowerSeries (Fin 2) κ) ∣ killX1 g := by
      rw [X_dvd_iff]
      intro n hn0
      rw [coeff_killX1]
      split_ifs with hn1
      · have : n = 0 := by ext i; fin_cases i <;> simp [hn0, hn1]
        rw [this, coeff_zero_eq_constantCoeff_apply, ← constantCoeff_killX1, hk0]
      · rfl
    obtain ⟨s, hs⟩ := hX0dvd

    have hord_sub : (↑(m + 1) : ℕ∞) ≤ (g - killX1 g).order := by
      refine le_trans hg (MvPowerSeries.le_order fun d hd => ?_)
      rw [map_sub, coeff_killX1]
      split_ifs
      · rw [sub_self]
      · rw [coeff_of_lt_order hd, sub_zero]
    have hord_kill : (↑(m + 1) : ℕ∞) ≤ (killX1 g).order := by
      refine le_trans hg (MvPowerSeries.le_order fun d hd => ?_)
      rw [coeff_killX1]
      split_ifs
      · exact coeff_of_lt_order hd
      · rfl
    have hX : ∀ k : Fin 2, (X k : MvPowerSeries (Fin 2) κ).order = 1 := by
      intro k
      rw [X_def, order_monomial_of_ne_zero one_ne_zero]
      simp
    have ht' : (m : ℕ∞) ≤ t.order := by
      have := hord_sub
      rw [ht, order_mul, hX] at this
      have hm : ((m + 1 : ℕ) : ℕ∞) = 1 + m := by push_cast; ring
      rw [hm] at this
      exact (ENat.add_le_add_iff_left ENat.one_ne_top).mp this
    have hs' : (m : ℕ∞) ≤ s.order := by
      have := hord_kill
      rw [hs, order_mul, hX] at this
      have hm : ((m + 1 : ℕ) : ℕ∞) = 1 + m := by push_cast; ring
      rw [hm] at this
      exact (ENat.add_le_add_iff_left ENat.one_ne_top).mp this
    have hg' : g = X 1 * t + X 0 * s := by rw [← ht, ← hs]; ring
    rw [hg', pow_succ']
    refine Ideal.add_mem _ (Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (ih t ht'))
      (Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (ih s hs'))

theorem apply_eq_self_of_killX1 (E : MvPowerSeries (Fin 2) κ →ₐ[κ] MvPowerSeries (Fin 2) κ)
    (hE : E (X 0) = X 0) (p : MvPowerSeries (Fin 2) κ) (hp : killX1 p = p) : E p = p := by
  classical
  ext m
  set k := m 0 + 1 with hk

  set pk : MvPowerSeries (Fin 2) κ := ∑ j ∈ Finset.range k, C (coeff (Finsupp.single 0 j) p) * X 0 ^ j with hpk
  have hcoeff_pk : ∀ n : Fin 2 →₀ ℕ, coeff n pk =
      ∑ j ∈ Finset.range k, if n = Finsupp.single 0 j then coeff (Finsupp.single 0 j) p else 0 := by
    intro n
    rw [hpk, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coeff_C_mul, coeff_X_pow]
    split_ifs <;> simp
  have hdiv : (X 0 : MvPowerSeries (Fin 2) κ) ^ k ∣ p - pk := by
    rw [X_pow_dvd_iff]
    intro n hn
    rw [map_sub, hcoeff_pk]
    by_cases hn1 : n 1 = 0
    · have hn' : n = Finsupp.single 0 (n 0) := by ext i; fin_cases i <;> simp [hn1]
      rw [Finset.sum_eq_single (n 0)]
      · rw [if_pos hn', ← hn', sub_self]
      · intro j _ hj
        rw [if_neg]
        intro h
        apply hj
        have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
        simpa using this.symm
      · intro h
        exact absurd (Finset.mem_range.mpr hn) h
    · have : coeff n p = 0 := by rw [← hp, coeff_killX1, if_neg hn1]
      rw [this, Finset.sum_eq_zero, sub_zero]
      intro j _
      rw [if_neg]
      intro h
      apply hn1
      rw [h]; simp
  obtain ⟨s, hs⟩ := hdiv
  have hp' : p = pk + X 0 ^ k * s := by rw [← hs]; ring
  have hEpk : E pk = pk := by
    rw [hpk, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, hE, c_eq_algebraMap, AlgHom.commutes]
  have hE' : E p - p = X 0 ^ k * (E s - s) := by
    conv_lhs => rw [hp', map_add, hEpk, map_mul, map_pow, hE]
    ring
  have : coeff m (E p - p) = 0 := by
    rw [hE']
    exact (X_pow_dvd_iff.mp (dvd_mul_right _ _)) m (by omega)
  rwa [map_sub, sub_eq_zero] at this

theorem degree_two (d : Fin 2 →₀ ℕ) : d.degree = d 0 + d 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

theorem eq_of_degree_lt_two (d : Fin 2 →₀ ℕ) (hd : d.degree < 2) :
    d = 0 ∨ d = Finsupp.single 0 1 ∨ d = Finsupp.single 1 1 := by
  rw [degree_two] at hd
  rcases Nat.eq_zero_or_pos (d 0) with h0 | h0
  · rcases Nat.eq_zero_or_pos (d 1) with h1 | h1
    · left; ext i; fin_cases i <;> simp [h0, h1]
    · right; right; ext i; fin_cases i <;> simp [h0]; omega
  · right; left; ext i; fin_cases i <;> simp; all_goals omega

theorem mem_sq_of_coeff (p : MvPowerSeries (Fin 2) κ) (h0 : constantCoeff p = 0)
    (h1 : coeff (Finsupp.single 0 1) p = 0) (h2 : coeff (Finsupp.single 1 1) p = 0) :
    p ∈ Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1} ^ 2 := by
  apply mem_pow_of_le_order
  refine MvPowerSeries.le_order fun d hd => ?_
  rcases eq_of_degree_lt_two d (by exact_mod_cast hd) with rfl | rfl | rfl
  · rwa [coeff_zero_eq_constantCoeff_apply]
  · exact h1
  · exact h2

theorem coeff_single_one_X_mul (s : Fin 2) (p : MvPowerSeries (Fin 2) κ) :
    coeff (Finsupp.single s 1) (X s * p) = constantCoeff p := by
  classical
  rw [X_def, coeff_monomial_mul, if_pos le_rfl, one_mul, tsub_self, coeff_zero_eq_constantCoeff_apply]

theorem coeff_single_one_X_mul_of_ne (s t : Fin 2) (hst : s ≠ t) (p : MvPowerSeries (Fin 2) κ) :
    coeff (Finsupp.single s 1) (X t * p) = 0 := by
  classical
  rw [X_def, coeff_monomial_mul, if_neg]
  intro h
  have := h t
  simp [Finsupp.single_apply, hst.symm] at this

theorem coeff_lin (d c : κ) :
    constantCoeff (C d * X 0 + C c * X 1 : MvPowerSeries (Fin 2) κ) = 0 ∧
    coeff (Finsupp.single 0 1) (C d * X 0 + C c * X 1 : MvPowerSeries (Fin 2) κ) = d ∧
    coeff (Finsupp.single 1 1) (C d * X 0 + C c * X 1 : MvPowerSeries (Fin 2) κ) = c := by
  classical
  refine ⟨by simp [constantCoeff_X], ?_, ?_⟩
  · rw [map_add, coeff_C_mul, coeff_C_mul, coeff_index_single_X, coeff_index_single_X,
      if_pos rfl, if_neg (by decide), mul_one, mul_zero, add_zero]
  · rw [map_add, coeff_C_mul, coeff_C_mul, coeff_index_single_X, coeff_index_single_X,
      if_neg (by decide), if_pos rfl, mul_one, mul_zero, zero_add]

theorem core {ι : Type v} [Fintype ι] (A B : ι → κ) (hA : ∀ i, A i ≠ 0) (f : MvPowerSeries (Fin 2) κ)
    (hf : f - X 1 * ∏ i, (C (A i) * X 0 + C (B i) * X 1) ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ (Fintype.card ι + 2)) :
    ∃ (L f₁ : MvPowerSeries (Fin 2) κ),
      L - X 1 ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2 ∧
      f₁ - ∏ i, (C (A i) * X 0 + C (B i) * X 1) ∈
        (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ (Fintype.card ι + 1) ∧
      f = L * f₁ := by
  classical
  set n := Fintype.card ι with hn
  set G : MvPowerSeries (Fin 2) κ := ∏ i, (C (A i) * X 0 + C (B i) * X 1) with hG
  set r := f - X 1 * G with hr
  have hfr : f = X 1 * G + r := by rw [hr]; ring

  have hβs : HasSubst (![X 0, X 0 * X 1] : Fin 2 → MvPowerSeries (Fin 2) κ) :=
    hasSubst_of_constantCoeff_zero (by intro s; fin_cases s <;> simp [constantCoeff_X])
  set β : MvPowerSeries (Fin 2) κ →ₐ[κ] MvPowerSeries (Fin 2) κ := substAlgHom hβs with hβ
  have hβ0 : β (X 0) = X 0 := by rw [hβ, substAlgHom_apply, subst_X hβs]; rfl
  have hβ1 : β (X 1) = X 0 * X 1 := by rw [hβ, substAlgHom_apply, subst_X hβs]; rfl
  have hβC : ∀ c : κ, β (C c) = C c := fun c => by rw [c_eq_algebraMap, AlgHom.commutes]
  have hβpow : ∀ (k : ℕ) (p : MvPowerSeries (Fin 2) κ),
      p ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ k → ∃ p', β p = X 0 ^ k * p' := by
    intro k p hp
    have hle : ((Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ k).map β ≤ Ideal.span {X 0 ^ k} := by
      rw [Ideal.map_pow, Ideal.map_span, ← Ideal.span_singleton_pow]
      apply Ideal.pow_right_mono
      rw [Ideal.span_le]
      rintro x ⟨y, hy, rfl⟩
      rcases hy with rfl | rfl
      · rw [hβ0]; exact Ideal.mem_span_singleton_self _
      · rw [hβ1]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    obtain ⟨p', hp'⟩ := Ideal.mem_span_singleton'.mp (hle (Ideal.mem_map_of_mem β hp))
    exact ⟨p', by rw [← hp', mul_comm]⟩
  obtain ⟨r', hr'⟩ := hβpow (n + 2) r hf
  set P : MvPowerSeries (Fin 2) κ := ∏ i, (C (A i) + C (B i) * X 1) with hP
  have hβG : β G = X 0 ^ n * P := by
    rw [hG, map_prod]
    have : ∀ i, β (C (A i) * X 0 + C (B i) * X 1) = X 0 * (C (A i) + C (B i) * X 1) := by
      intro i; rw [map_add, map_mul, map_mul, hβC, hβC, hβ0, hβ1]; ring
    simp_rw [this]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  set g : MvPowerSeries (Fin 2) κ := X 1 * P + X 0 * r' with hg
  have hβf : β f = X 0 ^ (n + 1) * g := by
    rw [hfr, map_add, map_mul, hβ1, hβG, hr', hg]; ring

  have hP0 : constantCoeff P = ∏ i, A i := by
    rw [hP, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [constantCoeff_X]
  have hc : (∏ i, A i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hA i
  have hg0 : constantCoeff g = 0 := by rw [hg]; simp [constantCoeff_X]
  have hg1 : coeff (Finsupp.single 1 1) g = ∏ i, A i := by
    rw [hg, map_add, coeff_single_one_X_mul, hP0, coeff_single_one_X_mul_of_ne 1 0 (by decide), add_zero]
  set d := coeff (Finsupp.single 0 1) g with hd
  have hglin : g - (C d * X 0 + C (∏ i, A i) * X 1) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2 := by
    obtain ⟨l0, l1, l2⟩ := coeff_lin d (∏ i, A i)
    apply mem_sq_of_coeff
    · rw [map_sub, hg0, l0, sub_self]
    · rw [map_sub, ← hd, l1, sub_self]
    · rw [map_sub, hg1, l2, sub_self]

  obtain ⟨E, hE⟩ := MvPowerSeries.exists_algEquiv_apply_X_eq ![X 0, g]
    (by intro i; fin_cases i <;> simp [constantCoeff_X, hg0])
    (by
      rw [Matrix.det_fin_two]
      simp [Matrix.of_apply, coeff_index_single_X, hg1, hc])
  have hE0 : E (X 0) = X 0 := hE 0
  have hE1 : E (X 1) = g := hE 1

  set ψ := E.symm (X 1) with hψ
  set φ₂ := killX1 ψ with hφ₂
  have hψ0 : constantCoeff ψ = 0 := by
    by_contra h
    have hu : IsUnit ψ := isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr h)
    have : IsUnit (X 1 : MvPowerSeries (Fin 2) κ) := by simpa [hψ] using hu.map E
    rw [isUnit_iff_constantCoeff, constantCoeff_X] at this
    exact not_isUnit_zero this
  have hφ₂0 : constantCoeff φ₂ = 0 := by rw [hφ₂, constantCoeff_killX1]; exact hψ0
  have hφ₂k : killX1 φ₂ = φ₂ := killX1_killX1 ψ
  have hφ₂1 : coeff (Finsupp.single 1 1) φ₂ = 0 := by
    rw [hφ₂, coeff_killX1, if_neg]; simp

  have hmem : X 1 - φ₂ ∈ Ideal.span {g} := by
    obtain ⟨t, ht⟩ := X1_dvd_sub_killX1 ψ
    have h1 : E ψ = X 1 := by rw [hψ]; exact E.apply_symm_apply _
    have h2 : E φ₂ = φ₂ := apply_eq_self_of_killX1 E.toAlgHom hE0 φ₂ hφ₂k
    have := congrArg E ht
    rw [map_sub, map_mul, hE1, h1, ← hφ₂, h2] at this
    exact Ideal.mem_span_singleton'.mpr ⟨E t, by rw [this, mul_comm]⟩

  obtain ⟨hgprime, hgnm, -, -⟩ :=
    MvPowerSeries.span_singleton_isPrime_of_sub_linear_mem_sq d (∏ i, A i) (Or.inr hc) g hglin
  set d' := coeff (Finsupp.single 0 1) φ₂ with hd'
  have hℓlin : (X 1 - φ₂) - (C (-d') * X 0 + C 1 * X 1) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2 := by
    obtain ⟨l0, l1, l2⟩ := coeff_lin (-d') (1 : κ)
    apply mem_sq_of_coeff
    · rw [map_sub, map_sub, l0, constantCoeff_X, hφ₂0]; ring
    · rw [map_sub, map_sub, l1, ← hd', coeff_index_single_X, if_neg (by decide)]; ring
    · rw [map_sub, map_sub, l2, hφ₂1, coeff_index_single_self_X]; ring
  obtain ⟨-, -, hℓuniq, -⟩ :=
    MvPowerSeries.span_singleton_isPrime_of_sub_linear_mem_sq (-d') 1 (Or.inr one_ne_zero) (X 1 - φ₂) hℓlin
  have hspan : Ideal.span {g} = Ideal.span {X 1 - φ₂} := hℓuniq _ hgprime hmem hgnm
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp (hspan ▸ Ideal.mem_span_singleton_self g : g ∈ Ideal.span {X 1 - φ₂})

  have hζs : HasSubst (![X 0, 0] : Fin 2 → MvPowerSeries (Fin 2) κ) :=
    hasSubst_of_constantCoeff_zero (by intro s; fin_cases s <;> simp [constantCoeff_X])
  have hζφ₂ : MvPowerSeries.subst ![X 0, 0] φ₂ = φ₂ := by
    have := apply_eq_self_of_killX1 (substAlgHom hζs) (by rw [substAlgHom_apply, subst_X hζs]; rfl) φ₂ hφ₂k
    rwa [substAlgHom_apply] at this
  have hPX0 : ∀ s : Fin 2, MvPowerSeries.constantCoeff ((![PowerSeries.X, 0] : Fin 2 → PowerSeries κ) s) = 0 := by
    intro s; fin_cases s
    · show MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries κ) = 0
      exact PowerSeries.constantCoeff_X
    · show MvPowerSeries.constantCoeff (0 : PowerSeries κ) = 0
      exact map_zero _
  have hτs : HasSubst (![PowerSeries.X, 0] : Fin 2 → PowerSeries κ) := hasSubst_of_constantCoeff_zero hPX0
  set φ : PowerSeries κ := MvPowerSeries.subst ![PowerSeries.X, 0] φ₂ with hφ
  have hι : PowerSeries.HasSubst (X 0 : MvPowerSeries (Fin 2) κ) := PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_X 0)
  have hφX0 : PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) κ) φ = φ₂ := by
    rw [hφ, PowerSeries.subst_def, subst_comp_subst_apply hτs hι.const, ← hζφ₂]
    congr 1
    funext s; fin_cases s
    · show subst (fun _ => (X 0 : MvPowerSeries (Fin 2) κ)) (PowerSeries.X : PowerSeries κ) = X 0
      rw [← PowerSeries.subst_def, PowerSeries.subst_X hι]
    · show subst (fun _ => (X 0 : MvPowerSeries (Fin 2) κ)) (0 : PowerSeries κ) = 0
      rw [← coe_substAlgHom hι.const, map_zero]
  have hφ0 : PowerSeries.constantCoeff φ = 0 := by
    rw [hφ]
    exact constantCoeff_subst_eq_zero hτs hPX0 hφ₂0

  set Φ : PowerSeries κ := PowerSeries.X * φ with hΦ
  have hΦ0 : PowerSeries.constantCoeff Φ = 0 := by rw [hΦ, map_mul, PowerSeries.constantCoeff_X, zero_mul]
  have hσs : HasSubst (![PowerSeries.X, φ] : Fin 2 → PowerSeries κ) :=
    hasSubst_of_constantCoeff_zero (by
      intro s; fin_cases s
      · show MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries κ) = 0
        exact PowerSeries.constantCoeff_X
      · show MvPowerSeries.constantCoeff φ = 0
        exact hφ0)
  have hσφ₂ : MvPowerSeries.subst ![PowerSeries.X, φ] φ₂ = φ := by
    conv_lhs => rw [← hφX0, PowerSeries.subst_def]
    rw [subst_comp_subst_apply hι.const hσs]
    have : (fun _ : Unit => subst ![PowerSeries.X, φ] (X 0 : MvPowerSeries (Fin 2) κ)) =
        fun _ : Unit => (PowerSeries.X : PowerSeries κ) := by
      funext; rw [subst_X hσs]; rfl
    rw [this]
    exact congrFun subst_self φ
  have hroot : MvPowerSeries.subst ![(PowerSeries.X : PowerSeries κ), Φ] f = 0 := by
    have hcomp : MvPowerSeries.subst ![(PowerSeries.X : PowerSeries κ), Φ] f =
        MvPowerSeries.subst ![PowerSeries.X, φ] (β f) := by
      rw [hβ, substAlgHom_apply, subst_comp_subst_apply hβs hσs]
      congr 1
      funext s; fin_cases s
      · show (PowerSeries.X : PowerSeries κ) = subst ![PowerSeries.X, φ] (X 0 : MvPowerSeries (Fin 2) κ)
        rw [subst_X hσs]; rfl
      · show Φ = subst ![PowerSeries.X, φ] (X 0 * X 1 : MvPowerSeries (Fin 2) κ)
        rw [← coe_substAlgHom hσs, map_mul, coe_substAlgHom, subst_X hσs, subst_X hσs]; rfl
    rw [hcomp, hβf, ← hu, ← coe_substAlgHom hσs, map_mul, map_mul, map_sub, coe_substAlgHom, hσφ₂,
      subst_X hσs]
    simp

  obtain ⟨M, hM⟩ := MvPowerSeries.exists_eq_X_sub_subst_mul_of_subst_eq_zero f Φ hΦ0 hroot
  have hLeq : PowerSeries.subst (X 0 : MvPowerSeries (Fin 2) κ) Φ = X 0 * φ₂ := by
    rw [hΦ, ← PowerSeries.coe_substAlgHom hι, map_mul, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X hι, hφX0]
  rw [hLeq] at hM
  refine ⟨X 1 - X 0 * φ₂, M, ?_, ?_, hM⟩
  ·
    rw [sub_sub_cancel_left, Ideal.neg_mem_iff, pow_two]
    exact Ideal.mul_mem_mul (Ideal.subset_span (by simp)) (mem_span_X_of_constantCoeff_eq_zero _ hφ₂0)
  ·
    apply mem_pow_of_le_order
    have hL1 : ((X 1 : MvPowerSeries (Fin 2) κ) - X 0 * φ₂).order = 1 := by
      apply le_antisymm
      · have h := order_le (f := (X 1 : MvPowerSeries (Fin 2) κ) - X 0 * φ₂) (d := Finsupp.single (1 : Fin 2) 1)
          (by
            rw [map_sub, coeff_index_single_self_X, coeff_single_one_X_mul_of_ne 1 0 (by decide), sub_zero]
            exact one_ne_zero)
        rwa [Finsupp.degree_single, Nat.cast_one] at h
      · rw [one_le_order_iff_constCoeff_eq_zero]; simp [constantCoeff_X]
    have hkey : (X 1 - X 0 * φ₂) * (M - G) = r + X 0 * φ₂ * G := by
      rw [mul_sub, ← hM, hfr]; ring
    have hordr : ((n + 2 : ℕ) : ℕ∞) ≤ r.order := le_order_of_mem_pow _ _ hf
    have hGmem : G ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ n := by
      have : G ∈ ∏ _i : ι, Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1} := by
        rw [hG]
        refine Ideal.prod_mem_prod fun i _ => ?_
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
          (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
      rwa [Finset.prod_const, Finset.card_univ] at this
    have hordG : (n : ℕ∞) ≤ G.order := le_order_of_mem_pow _ _ hGmem
    have hordφ : (1 : ℕ∞) ≤ φ₂.order := one_le_order_iff_constCoeff_eq_zero.mpr hφ₂0
    have hordX : ((X 0 : MvPowerSeries (Fin 2) κ)).order = 1 := by
      rw [X_def, order_monomial_of_ne_zero one_ne_zero]; simp
    have hrhs : ((n + 2 : ℕ) : ℕ∞) ≤ (r + X 0 * φ₂ * G).order := by
      refine le_trans (le_min hordr ?_) min_order_le_add
      have e1 : (X 0 : MvPowerSeries (Fin 2) κ).order + φ₂.order + G.order ≤ (X 0 * φ₂ * G).order :=
        le_trans (add_le_add le_order_mul le_rfl) le_order_mul
      have e2 : (1 : ℕ∞) + 1 + (n : ℕ∞) ≤ (X 0 : MvPowerSeries (Fin 2) κ).order + φ₂.order + G.order := by
        rw [hordX]; exact add_le_add (add_le_add le_rfl hordφ) hordG
      have e3 : ((n + 2 : ℕ) : ℕ∞) = (1 : ℕ∞) + 1 + (n : ℕ∞) := by push_cast; ring
      rw [e3]; exact le_trans e2 e1
    rw [← hkey, order_mul, hL1] at hrhs
    have h12 : ((n + 2 : ℕ) : ℕ∞) = 1 + ((n + 1 : ℕ) : ℕ∞) := by push_cast; ring
    rw [h12] at hrhs
    exact (ENat.add_le_add_iff_left ENat.one_ne_top).mp hrhs

theorem constantCoeff_algEquiv_X (E : MvPowerSeries (Fin 2) κ ≃ₐ[κ] MvPowerSeries (Fin 2) κ) (k : Fin 2) :
    constantCoeff (E (X k)) = 0 := by
  by_contra h
  have hu : IsUnit (E (X k)) := isUnit_iff_constantCoeff.mpr (isUnit_iff_ne_zero.mpr h)
  have : IsUnit (X k : MvPowerSeries (Fin 2) κ) := by simpa using hu.map E.symm
  rw [isUnit_iff_constantCoeff, constantCoeff_X] at this
  exact not_isUnit_zero this

theorem algEquiv_mem_pow (E : MvPowerSeries (Fin 2) κ ≃ₐ[κ] MvPowerSeries (Fin 2) κ) (k : ℕ)
    {p : MvPowerSeries (Fin 2) κ} (hp : p ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ k) :
    E p ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ k := by
  have := map_pow_le (E := E.toAlgHom) (constantCoeff_algEquiv_X E 0) (constantCoeff_algEquiv_X E 1) k
  exact this (Ideal.mem_map_of_mem E.toAlgHom hp)

theorem transport {ι : Type v} [Fintype ι] (a b : κ) (A B A' B' : ι → κ) (hA' : ∀ i, A' i ≠ 0)
    (E : MvPowerSeries (Fin 2) κ ≃ₐ[κ] MvPowerSeries (Fin 2) κ)
    (hE1 : E (X 1) = C a * X 0 + C b * X 1)
    (hElin : ∀ i, E (C (A' i) * X 0 + C (B' i) * X 1) = C (A i) * X 0 + C (B i) * X 1)
    (f : MvPowerSeries (Fin 2) κ)
    (hf : f - (C a * X 0 + C b * X 1) * ∏ i, (C (A i) * X 0 + C (B i) * X 1) ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ (Fintype.card ι + 2)) :
    ∃ (L f₁ : MvPowerSeries (Fin 2) κ),
      L - (C a * X 0 + C b * X 1) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2 ∧
      f₁ - ∏ i, (C (A i) * X 0 + C (B i) * X 1) ∈
        (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ (Fintype.card ι + 1) ∧
      f = L * f₁ := by
  classical
  have hs1 : E.symm (C a * X 0 + C b * X 1) = X 1 := by rw [← hE1]; exact E.symm_apply_apply _
  have hslin : ∀ i, E.symm (C (A i) * X 0 + C (B i) * X 1) = C (A' i) * X 0 + C (B' i) * X 1 := by
    intro i; rw [← hElin i]; exact E.symm_apply_apply _
  have hf' : E.symm f - X 1 * ∏ i, (C (A' i) * X 0 + C (B' i) * X 1) ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ (Fintype.card ι + 2) := by
    have := algEquiv_mem_pow E.symm _ hf
    rw [map_sub, map_mul, hs1, map_prod] at this
    simp_rw [hslin] at this
    exact this
  obtain ⟨L', f₁', hL', hf₁', hff'⟩ := core A' B' hA' (E.symm f) hf'
  refine ⟨E L', E f₁', ?_, ?_, ?_⟩
  · have := algEquiv_mem_pow E 2 hL'
    rwa [map_sub, hE1] at this
  · have := algEquiv_mem_pow E _ hf₁'
    rw [map_sub, map_prod] at this
    simp_rw [hElin] at this
    exact this
  · rw [← map_mul, ← hff']; exact (E.apply_symm_apply f).symm

end OneBranchGC7

open OneBranchGC7 in
theorem solution
    {κ : Type u} [Field κ] {ι : Type v} [Fintype ι]
    (a b : κ) (hab : a ≠ 0 ∨ b ≠ 0)
    (A B : ι → κ) (hsimple : ∀ i, a * B i - A i * b ≠ 0)
    (f : MvPowerSeries (Fin 2) κ)
    (hf : f - (C a * X 0 + C b * X 1) * ∏ i, (C (A i) * X 0 + C (B i) * X 1) ∈
      (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ (Fintype.card ι + 2)) :
    ∃ (L f₁ : MvPowerSeries (Fin 2) κ),
      L - (C a * X 0 + C b * X 1) ∈ (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ 2 ∧
      f₁ - ∏ i, (C (A i) * X 0 + C (B i) * X 1) ∈
        (Ideal.span {(X 0 : MvPowerSeries (Fin 2) κ), X 1}) ^ (Fintype.card ι + 1) ∧
      f = L * f₁ := by
  classical
  obtain ⟨l0, l1, l2⟩ := coeff_lin a b
  by_cases hb : b = 0
  ·
    have ha : a ≠ 0 := hab.resolve_right (not_not.mpr hb)
    obtain ⟨E, hE⟩ := MvPowerSeries.exists_algEquiv_apply_X_eq ![X 1, C a * X 0 + C b * X 1]
      (by intro i; fin_cases i <;> simp [constantCoeff_X, l0])
      (by
        rw [Matrix.det_fin_two]
        simp [Matrix.of_apply, coeff_index_single_X, l1, l2, hb, ha])
    have hE0 : E (X 0) = X 1 := hE 0
    have hE1 : E (X 1) = C a * X 0 + C b * X 1 := hE 1
    have hEC : ∀ c : κ, E (C c) = C c := fun c => by rw [c_eq_algebraMap, AlgEquiv.commutes]
    refine transport a b A B (fun i => B i) (fun i => A i / a) ?_ E hE1 ?_ f hf
    · intro i; have := hsimple i; rw [hb, mul_zero, sub_zero] at this; exact (mul_ne_zero_iff.mp this).2
    · intro i
      rw [map_add, map_mul, map_mul, hEC, hEC, hE0, hE1, hb]
      simp only [map_zero, zero_mul, add_zero]
      have key : C (A i / a) * (C a * (X 0 : MvPowerSeries (Fin 2) κ)) = C (A i) * X 0 := by
        rw [← mul_assoc, ← map_mul, div_mul_cancel₀ _ ha]
      rw [key]; ring
  · obtain ⟨E, hE⟩ := MvPowerSeries.exists_algEquiv_apply_X_eq ![X 0, C a * X 0 + C b * X 1]
      (by intro i; fin_cases i <;> simp [constantCoeff_X, l0])
      (by
        rw [Matrix.det_fin_two]
        simp [Matrix.of_apply, coeff_index_single_X, l1, l2, hb])
    have hE0 : E (X 0) = X 0 := hE 0
    have hE1 : E (X 1) = C a * X 0 + C b * X 1 := hE 1
    have hEC : ∀ c : κ, E (C c) = C c := fun c => by rw [c_eq_algebraMap, AlgEquiv.commutes]
    refine transport a b A B (fun i => A i - a * B i / b) (fun i => B i / b) ?_ E hE1 ?_ f hf
    · intro i h
      have h' : A i - a * B i / b = 0 := h
      apply hsimple i
      have : (A i - a * B i / b) * b = 0 := by rw [h', zero_mul]
      rw [sub_mul, div_mul_cancel₀ _ hb] at this
      linear_combination (-1 : κ) * this
    · intro i
      rw [map_add, map_mul, map_mul, hEC, hEC, hE0, hE1]
      show C (A i - a * B i / b) * (X 0 : MvPowerSeries (Fin 2) κ) + C (B i / b) * (C a * X 0 + C b * X 1) =
        C (A i) * X 0 + C (B i) * X 1
      have k1 : (C (B i / b) : MvPowerSeries (Fin 2) κ) * C b = C (B i) := by
        rw [← map_mul, div_mul_cancel₀ _ hb]
      have k2 : (C (A i - a * B i / b) : MvPowerSeries (Fin 2) κ) + C (B i / b) * C a = C (A i) := by
        rw [← map_mul, ← map_add]; congr 1; field_simp; ring
      have : C (A i - a * B i / b) * (X 0 : MvPowerSeries (Fin 2) κ) + C (B i / b) * (C a * X 0 + C b * X 1) =
          (C (A i - a * B i / b) + C (B i / b) * C a) * X 0 + (C (B i / b) * C b) * X 1 := by ring
      rw [this, k1, k2]

end S_MvPowerSeries_exists_eq_mul_of_sub_mul_prod_linear_mem_pow_of_det_ne_zero
end P2MW
export P2MW.S_MvPowerSeries_exists_eq_mul_of_sub_mul_prod_linear_mem_pow_of_det_ne_zero (solution)
