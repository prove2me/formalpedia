-- Prove2me | solution 1 for MvPowerSeries.exists_forall_coeff_mul_eq_pow_mul_and_residue_eq_coeff_mul_of_weightedInitialForm_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/1465a42c-4a76-5de7-b110-769090e00ffd

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_exists_forall_coeff_mul_eq_pow_mul_and_residue_eq_coeff_mul_of_weightedInitialForm_ne_zero

set_option autoImplicit false

noncomputable section

open MvPowerSeries

universe u v

namespace WIF

attribute [local instance] Classical.propDecidable

variable {σ : Type u} {O : Type v} [CommRing O]

def F (I : Ideal O) (m n : ℕ) : Ideal (MvPowerSeries σ O) where
  carrier := {G | ∀ e : σ →₀ ℕ, coeff e G ∈ I ^ (n - m * e.degree)}
  add_mem' {f g} hf hg e := by
    rw [map_add]
    exact Ideal.add_mem _ (hf e) (hg e)
  zero_mem' e := by
    rw [map_zero]
    exact Ideal.zero_mem _
  smul_mem' s f hf e := by
    classical
    rw [smul_eq_mul, coeff_mul]
    refine Ideal.sum_mem _ fun p hp => ?_
    have hpe : p.1 + p.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hdeg : p.2.degree ≤ e.degree := by
      rw [← hpe, map_add]; exact Nat.le_add_left _ _
    have hle : I ^ (n - m * p.2.degree) ≤ I ^ (n - m * e.degree) :=
      Ideal.pow_le_pow_right (by
        have := Nat.mul_le_mul_left m hdeg
        omega)
    exact Ideal.mul_mem_left _ _ (hle (hf p.2))

theorem mem_F {I : Ideal O} {m n : ℕ} {G : MvPowerSeries σ O} :
    G ∈ F I m n ↔ ∀ e : σ →₀ ℕ, coeff e G ∈ I ^ (n - m * e.degree) := Iff.rfl

theorem F_antitone (I : Ideal O) (m : ℕ) {n n' : ℕ} (h : n ≤ n') : F (σ := σ) I m n' ≤ F I m n := by
  intro G hG e
  exact Ideal.pow_le_pow_right (by omega) (hG e)

theorem F_zero (I : Ideal O) (m : ℕ) : F (σ := σ) I m 0 = ⊤ := by
  ext G
  simp [mem_F]

theorem mul_mem_F {I : Ideal O} {m a b : ℕ} {G H : MvPowerSeries σ O}
    (hG : G ∈ F I m a) (hH : H ∈ F I m b) : G * H ∈ F I m (a + b) := by
  classical
  intro e
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun p hp => ?_
  have hpe : p.1 + p.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hdeg : p.1.degree + p.2.degree = e.degree := by rw [← hpe, map_add]
  have h1 := hG p.1
  have h2 := hH p.2
  have hprod : coeff p.1 G * coeff p.2 H ∈ I ^ ((a - m * p.1.degree) + (b - m * p.2.degree)) := by
    rw [pow_add]; exact Ideal.mul_mem_mul h1 h2
  refine Ideal.pow_le_pow_right ?_ hprod
  have hm' : m * e.degree = m * p.1.degree + m * p.2.degree := by rw [← hdeg, Nat.mul_add]
  generalize m * p.1.degree = x at hm' ⊢
  generalize m * p.2.degree = y at hm' ⊢
  omega

theorem C_mem_F {I : Ideal O} {m k : ℕ} {c : O} (hc : c ∈ I ^ k) : (C c : MvPowerSeries σ O) ∈ F I m k := by
  classical
  intro e
  rw [coeff_C]
  split_ifs with he
  · subst he
    simpa using hc
  · exact Ideal.zero_mem _

section DVR

variable [IsDomain O] [IsDiscreteValuationRing O] (π : O) (hπ : Irreducible π)

local notation "κ" => IsLocalRing.ResidueField O
local notation "𝔪" => IsLocalRing.maximalIdeal O

include hπ in
theorem exists_eq_pow_mul {k : ℕ} {c : O} (h : c ∈ 𝔪 ^ k) : ∃ a : O, c = π ^ k * a := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h
  obtain ⟨a, ha⟩ := h
  exact ⟨a, by rw [← ha, mul_comm]⟩

include hπ in
theorem pow_mul_mem_pow (k : ℕ) (a : O) : π ^ k * a ∈ 𝔪 ^ k := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

def dres (k : ℕ) (c : O) : κ :=
  if h : ∃ a : O, c = π ^ k * a then IsLocalRing.residue O h.choose else 0

include hπ in
theorem dres_eq {k : ℕ} {c a : O} (h : c = π ^ k * a) : dres π k c = IsLocalRing.residue O a := by
  have hex : ∃ a : O, c = π ^ k * a := ⟨a, h⟩
  rw [dres, dif_pos hex]
  congr 1
  have h1 : π ^ k * hex.choose = π ^ k * a := by rw [← hex.choose_spec, h]
  exact mul_left_cancel₀ (pow_ne_zero k hπ.ne_zero) h1

include hπ in
theorem dres_pow_mul (k : ℕ) (a : O) : dres π k (π ^ k * a) = IsLocalRing.residue O a := dres_eq π hπ rfl

variable (m : ℕ)

def idx [Finite σ] (n : ℕ) : Finset (σ →₀ ℕ) :=
  ((Finsupp.finite_of_degree_le (σ := σ) n).toFinset).filter fun e => m * e.degree ≤ n

theorem mem_idx [Finite σ] (hm : 1 ≤ m) {n : ℕ} {e : σ →₀ ℕ} : e ∈ idx (σ := σ) m n ↔ m * e.degree ≤ n := by
  rw [idx, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    nlinarith

def sym [Finite σ] (n : ℕ) (G : MvPowerSeries σ O) : MvPolynomial σ κ :=
  ∑ e ∈ idx (σ := σ) m n, MvPolynomial.monomial e (dres π (n - m * e.degree) (coeff e G))

variable [Finite σ] (hm : 1 ≤ m)
include hm

theorem coeff_sym (n : ℕ) (G : MvPowerSeries σ O) (e : σ →₀ ℕ) :
    MvPolynomial.coeff e (sym π m n G) =
      if m * e.degree ≤ n then dres π (n - m * e.degree) (coeff e G) else 0 := by
  classical
  rw [sym, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  split_ifs with he
  · rw [Finset.sum_eq_single e]
    · rw [if_pos rfl]
    · intro b _ hb; rw [if_neg hb]
    · intro h; exact absurd ((mem_idx m hm).mpr he) h
  · refine Finset.sum_eq_zero fun b hb => ?_
    rw [if_neg]
    rintro rfl
    exact he ((mem_idx m hm).mp hb)

include hπ

theorem sym_eq_zero_of_mem_F_succ {n : ℕ} {G : MvPowerSeries σ O} (hG : G ∈ F 𝔪 m (n + 1)) : sym π m n G = 0 := by
  classical
  ext e
  rw [coeff_sym π m hm, MvPolynomial.coeff_zero]
  split_ifs with he
  · obtain ⟨a, ha⟩ := exists_eq_pow_mul π hπ (hG e)
    have hk : n + 1 - m * e.degree = (n - m * e.degree) + 1 := by omega
    rw [hk, pow_succ, mul_assoc] at ha
    have hπ0 : IsLocalRing.residue O π = 0 :=
      (IsLocalRing.residue_eq_zero_iff π).mpr (by rw [hπ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self _)
    rw [dres_eq π hπ ha, map_mul, hπ0, zero_mul]
  · rfl

theorem mem_F_succ_of_sym_eq_zero {n : ℕ} {G : MvPowerSeries σ O} (hG : G ∈ F 𝔪 m n) (h0 : sym π m n G = 0) :
    G ∈ F 𝔪 m (n + 1) := by
  classical
  intro e
  by_cases he : m * e.degree ≤ n
  · obtain ⟨a, ha⟩ := exists_eq_pow_mul π hπ (hG e)
    have hc := congrArg (MvPolynomial.coeff e) h0
    rw [coeff_sym π m hm, if_pos he, MvPolynomial.coeff_zero, dres_eq π hπ ha,
      IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hc
    obtain ⟨a', ha'⟩ := hc
    have hk : n + 1 - m * e.degree = (n - m * e.degree) + 1 := by omega
    rw [ha, ← ha', hk]
    have : π ^ (n - m * e.degree) * (a' * π) = π ^ (n - m * e.degree + 1) * a' := by ring
    rw [this]
    exact pow_mul_mem_pow π hπ _ _
  · have : n + 1 - m * e.degree = 0 := by omega
    rw [this, pow_zero, Ideal.one_eq_top]; trivial

theorem sym_C_pow_mul (k : ℕ) (u : O) :
    sym π m k (C (π ^ k * u) : MvPowerSeries σ O) = MvPolynomial.C (IsLocalRing.residue O u) := by
  classical
  ext e
  rw [coeff_sym π m hm, MvPolynomial.coeff_C, coeff_C]
  by_cases he : e = 0
  · subst he
    have h0 : m * (0 : σ →₀ ℕ).degree ≤ k := by simp
    rw [if_pos h0, if_pos rfl, if_pos rfl, map_zero, mul_zero, Nat.sub_zero]
    exact dres_pow_mul π hπ k u
  · rw [if_neg (Ne.symm he)]
    split_ifs with h1
    · rw [dres_eq π hπ (show (0 : O) = π ^ (k - m * e.degree) * 0 by rw [mul_zero]), map_zero]
    · rfl

omit hm in

theorem residue_pi : IsLocalRing.residue O π = 0 :=
  (IsLocalRing.residue_eq_zero_iff π).mpr (by rw [hπ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self _)

theorem sym_mul {a b : ℕ} {G H : MvPowerSeries σ O} (hG : G ∈ F 𝔪 m a) (hH : H ∈ F 𝔪 m b) :
    sym π m (a + b) (G * H) = sym π m a G * sym π m b H := by
  classical
  ext e
  rw [coeff_sym π m hm, MvPolynomial.coeff_mul]

  have hGc : ∀ d : σ →₀ ℕ, ∃ g : O, coeff d G = π ^ (a - m * d.degree) * g := fun d => exists_eq_pow_mul π hπ (hG d)
  have hHc : ∀ d : σ →₀ ℕ, ∃ h : O, coeff d H = π ^ (b - m * d.degree) * h := fun d => exists_eq_pow_mul π hπ (hH d)
  choose g hg using hGc
  choose h hh using hHc
  have hRHS : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal e,
      MvPolynomial.coeff p.1 (sym π m a G) * MvPolynomial.coeff p.2 (sym π m b H) =
        if m * p.1.degree ≤ a ∧ m * p.2.degree ≤ b then
          IsLocalRing.residue O (g p.1) * IsLocalRing.residue O (h p.2) else 0 := by
    intro p _
    rw [coeff_sym π m hm, coeff_sym π m hm]
    by_cases h1 : m * p.1.degree ≤ a
    · by_cases h2 : m * p.2.degree ≤ b
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, dres_eq π hπ (hg p.1), dres_eq π hπ (hh p.2)]
      · rw [if_pos h1, if_neg h2, if_neg (fun hh' : m * p.1.degree ≤ a ∧ m * p.2.degree ≤ b => h2 hh'.2), mul_zero]
    · rw [if_neg h1, if_neg (fun hh' : m * p.1.degree ≤ a ∧ m * p.2.degree ≤ b => h1 hh'.1), zero_mul]
  rw [Finset.sum_congr rfl hRHS]
  split_ifs with he
  · set k := a + b - m * e.degree with hk
    have hexp : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal e,
        (a - m * p.1.degree) + (b - m * p.2.degree) = k + ((a - m * p.1.degree) + (b - m * p.2.degree) - k) ∧
        (((a - m * p.1.degree) + (b - m * p.2.degree) - k = 0) ↔ (m * p.1.degree ≤ a ∧ m * p.2.degree ≤ b)) := by
      intro p hp
      have hpe : p.1 + p.2 = e := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      have hdeg : m * e.degree = m * p.1.degree + m * p.2.degree := by rw [← hpe, map_add, Nat.mul_add]
      rw [hk]
      generalize m * p.1.degree = x at hdeg ⊢
      generalize m * p.2.degree = y at hdeg ⊢
      generalize m * e.degree = z at hdeg he ⊢
      omega
    have hcoeff : coeff e (G * H) = π ^ k * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal e,
        π ^ ((a - m * p.1.degree) + (b - m * p.2.degree) - k) * (g p.1 * h p.2) := by
      rw [coeff_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [hg p.1, hh p.2]
      obtain ⟨h1, -⟩ := hexp p hp
      rw [show π ^ (a - m * p.1.degree) * g p.1 * (π ^ (b - m * p.2.degree) * h p.2) =
          π ^ ((a - m * p.1.degree) + (b - m * p.2.degree)) * (g p.1 * h p.2) by rw [pow_add]; ring]
      conv_lhs => rw [h1]
      rw [pow_add]
      ring
    rw [dres_eq π hπ hcoeff, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨-, h2⟩ := hexp p hp
    rw [map_mul, map_pow, map_mul]
    by_cases hgood : m * p.1.degree ≤ a ∧ m * p.2.degree ≤ b
    · rw [if_pos hgood, h2.mpr hgood, pow_zero, one_mul]
    · rw [if_neg hgood]
      have hne : (a - m * p.1.degree) + (b - m * p.2.degree) - k ≠ 0 := fun h0 => hgood (h2.mp h0)
      obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hne
      rw [ht, pow_succ, residue_pi π hπ, mul_zero, zero_mul]
  · symm
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [if_neg]
    rintro ⟨h1, h2⟩
    have hpe := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hdeg : m * e.degree = m * p.1.degree + m * p.2.degree := by rw [← hpe, map_add, Nat.mul_add]
    omega

theorem sym_ne_zero_iff {n : ℕ} {G : MvPowerSeries σ O} (hG : G ∈ F 𝔪 m n) :
    sym π m n G ≠ 0 ↔ G ∉ F 𝔪 m (n + 1) :=
  ⟨fun h hG' => h (sym_eq_zero_of_mem_F_succ π hπ m hm hG'), fun h h0 => h (mem_F_succ_of_sym_eq_zero π hπ m hm hG h0)⟩

theorem mul_notMem_F_succ {a b : ℕ} {G H : MvPowerSeries σ O} (hG : G ∈ F 𝔪 m a) (hGn : G ∉ F 𝔪 m (a + 1))
    (hH : H ∈ F 𝔪 m b) (hHn : H ∉ F 𝔪 m (b + 1)) : G * H ∉ F 𝔪 m (a + b + 1) := by
  have h1 : sym π m a G ≠ 0 := (sym_ne_zero_iff π hπ m hm hG).mpr hGn
  have h2 : sym π m b H ≠ 0 := (sym_ne_zero_iff π hπ m hm hH).mpr hHn
  have h3 : sym π m (a + b) (G * H) ≠ 0 := by
    rw [sym_mul π hπ m hm hG hH]; exact mul_ne_zero h1 h2
  exact (sym_ne_zero_iff π hπ m hm (mul_mem_F hG hH)).mp h3

theorem exists_mem_F_notMem_succ {G : MvPowerSeries σ O} (hG : G ≠ 0) :
    ∃ a : ℕ, G ∈ F 𝔪 m a ∧ G ∉ F 𝔪 m (a + 1) := by
  classical

  have hex : ∃ n : ℕ, G ∉ F 𝔪 m n := by
    by_contra hall
    push Not at hall
    apply hG
    ext e
    rw [map_zero]
    have hmem : ∀ k : ℕ, coeff e G ∈ 𝔪 ^ k := by
      intro k
      have := hall (k + m * e.degree) e
      rwa [Nat.add_sub_cancel] at this
    have hinf : coeff e G ∈ ⨅ k : ℕ, 𝔪 ^ k := Ideal.mem_iInf.mpr hmem
    rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top, Ideal.mem_bot] at hinf
  let n := Nat.find hex
  have hn : G ∉ F 𝔪 m n := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h0
    apply hn
    rw [show n = 0 from h0, F_zero]; trivial
  refine ⟨n - 1, ?_, by rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)]⟩
  have := Nat.find_min hex (m := n - 1) (by omega)
  push Not at this
  exact this

theorem sym_mul_mem_span {r c : ℕ} {ρ H : MvPowerSeries σ O} (hρ : ρ ∈ F 𝔪 m r) (hρn : sym π m r ρ ≠ 0)
    (hHρ : H * ρ ∈ F 𝔪 m c) : sym π m c (H * ρ) ∈ Ideal.span {sym π m r ρ} := by
  classical
  by_cases hcr : c < r
  ·
    have : H * ρ ∈ F 𝔪 m (c + 1) := F_antitone _ m (by omega) (Ideal.mul_mem_left _ H hρ)
    rw [sym_eq_zero_of_mem_F_succ π hπ m hm this]
    exact Ideal.zero_mem _
  · push Not at hcr
    by_cases hH0 : H = 0
    · subst hH0
      rw [zero_mul, show sym π m c (0 : MvPowerSeries σ O) = 0 from
        sym_eq_zero_of_mem_F_succ π hπ m hm (Ideal.zero_mem _)]
      exact Ideal.zero_mem _

    have hHF : H ∈ F 𝔪 m (c - r) := by
      by_contra hnot
      obtain ⟨a, ha, han⟩ := exists_mem_F_notMem_succ π hπ m hm hH0
      have hlt : a < c - r := by
        by_contra hge
        push Not at hge
        exact hnot (F_antitone _ m hge ha)
      have hρn' : ρ ∉ F 𝔪 m (r + 1) := (sym_ne_zero_iff π hπ m hm hρ).mp hρn
      have hprod := mul_notMem_F_succ π hπ m hm ha han hρ hρn'
      exact hprod (F_antitone _ m (by omega) hHρ)
    have hc : c = (c - r) + r := by omega
    rw [hc, sym_mul π hπ m hm hHF hρ]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end DVR

end WIF

theorem WIF.main
    (σ : Type u) [Finite σ] (O : Type v) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) (hπ : Irreducible π) (m : ℕ) (hm : 1 ≤ m) (r c : ℕ)
    (ρ H : MvPowerSeries σ O) (ρbar : MvPolynomial σ (IsLocalRing.ResidueField O)) (hρbar : ρbar ≠ 0)
    (hρ : ∀ e : σ →₀ ℕ, m * e.degree ≤ r →
      ∃ a : O, MvPowerSeries.coeff e ρ = π ^ (r - m * e.degree) * a ∧
        IsLocalRing.residue O a = MvPolynomial.coeff e ρbar)
    (hρ' : ∀ e : σ →₀ ℕ, r < m * e.degree → MvPolynomial.coeff e ρbar = 0)
    (hHρ : ∀ e : σ →₀ ℕ, MvPowerSeries.coeff e (H * ρ) ∈ IsLocalRing.maximalIdeal O ^ (c - m * e.degree)) :
    ∃ Q : MvPolynomial σ (IsLocalRing.ResidueField O),
      (∀ e : σ →₀ ℕ, m * e.degree ≤ c →
        ∃ a : O, MvPowerSeries.coeff e (H * ρ) = π ^ (c - m * e.degree) * a ∧
          IsLocalRing.residue O a = MvPolynomial.coeff e (Q * ρbar)) ∧
      (∀ e : σ →₀ ℕ, c < m * e.degree → MvPolynomial.coeff e (Q * ρbar) = 0) := by
  classical

  have hρF : ρ ∈ WIF.F (IsLocalRing.maximalIdeal O) m r := by
    intro e
    by_cases he : m * e.degree ≤ r
    · obtain ⟨a, ha, -⟩ := hρ e he
      rw [ha]; exact WIF.pow_mul_mem_pow π hπ _ _
    · have : r - m * e.degree = 0 := by omega
      rw [this, pow_zero, Ideal.one_eq_top]; trivial

  have hsym : WIF.sym π m r ρ = ρbar := by
    ext e
    rw [WIF.coeff_sym π m hm]
    split_ifs with he
    · obtain ⟨a, ha, hres⟩ := hρ e he
      rw [WIF.dres_eq π hπ ha, hres]
    · rw [hρ' e (by omega)]
  have hρn : WIF.sym π m r ρ ≠ 0 := by rw [hsym]; exact hρbar
  have hcore := WIF.sym_mul_mem_span π hπ m hm hρF hρn hHρ
  rw [Ideal.mem_span_singleton'] at hcore
  obtain ⟨Q, hQ⟩ := hcore
  refine ⟨Q, fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨a, ha⟩ := WIF.exists_eq_pow_mul π hπ (hHρ e)
    refine ⟨a, ha, ?_⟩
    have hc := congrArg (MvPolynomial.coeff e) hQ
    rw [WIF.coeff_sym π m hm, if_pos he, WIF.dres_eq π hπ ha] at hc
    rw [← hc, hsym]
  · have hc := congrArg (MvPolynomial.coeff e) hQ
    rw [WIF.coeff_sym π m hm, if_neg (by omega)] at hc
    rw [← hsym, hc]

end

universe u' v'

theorem solution
    (σ : Type u') [Finite σ] (O : Type v') [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (π : O) (hπ : Irreducible π) (m : ℕ) (hm : 1 ≤ m) (r c : ℕ)
    (ρ H : MvPowerSeries σ O) (ρbar : MvPolynomial σ (IsLocalRing.ResidueField O)) (hρbar : ρbar ≠ 0)
    (hρ : ∀ e : σ →₀ ℕ, m * e.degree ≤ r →
      ∃ a : O, MvPowerSeries.coeff e ρ = π ^ (r - m * e.degree) * a ∧
        IsLocalRing.residue O a = MvPolynomial.coeff e ρbar)
    (hρ' : ∀ e : σ →₀ ℕ, r < m * e.degree → MvPolynomial.coeff e ρbar = 0)
    (hHρ : ∀ e : σ →₀ ℕ, MvPowerSeries.coeff e (H * ρ) ∈ IsLocalRing.maximalIdeal O ^ (c - m * e.degree)) :
    ∃ Q : MvPolynomial σ (IsLocalRing.ResidueField O),
      (∀ e : σ →₀ ℕ, m * e.degree ≤ c →
        ∃ a : O, MvPowerSeries.coeff e (H * ρ) = π ^ (c - m * e.degree) * a ∧
          IsLocalRing.residue O a = MvPolynomial.coeff e (Q * ρbar)) ∧
      (∀ e : σ →₀ ℕ, c < m * e.degree → MvPolynomial.coeff e (Q * ρbar) = 0) :=
  WIF.main σ O π hπ m hm r c ρ H ρbar hρbar hρ hρ' hHρ

end S_MvPowerSeries_exists_forall_coeff_mul_eq_pow_mul_and_residue_eq_coeff_mul_of_weightedInitialForm_ne_zero
end P2MW
export P2MW.S_MvPowerSeries_exists_forall_coeff_mul_eq_pow_mul_and_residue_eq_coeff_mul_of_weightedInitialForm_ne_zero (solution)
