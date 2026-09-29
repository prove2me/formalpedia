-- Prove2me | solution 1 for MvFormalGroup.coeff_mem_span_sup_pow_of_forall_coeff_ghostComponent_eq_logCovector_of_slope
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/3777e3f9-4c4a-5591-8252-1f3e79a4a84e

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Theorems.Thm_MvPowerSeries_exists_wittVector_forall_coeff_ghostComponent_eq_of_forall_natCast_mul_coeff_mem
import Theorems.Thm_MvPowerSeries_le_mul_degree_of_coeff_coeff_ne_zero_of_forall_coeff_ghostComponent_eq
import Theorems.Thm_WittVector_coeff_mem_span_pow_sub_of_forall_ghostComponent_mem_span_pow
import Theorems.Thm_WittVector_add_coeff_eq_of_forall_coeff_eq_zero
import Theorems.Thm_WittVector_coeff_eq_coeff_of_forall_ghostComponent_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_coeff_mem_span_sup_pow_of_forall_coeff_ghostComponent_eq_logCovector_of_slope

set_option autoImplicit false
open MvPowerSeries

universe u v

namespace S17DO

open MvPowerSeries

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]

section PS
variable {σ : Type v}

theorem mem_span_C_iff (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (f : MvPowerSeries σ 𝓞) :
    f ∈ Ideal.span {(p : MvPowerSeries σ 𝓞)} ↔ ∀ μ, coeff μ f ∈ Ideal.span {(p : 𝓞)} := by
  constructor
  · intro hf μ
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 hf
    rw [show (p : MvPowerSeries σ 𝓞) = C (p : 𝓞) from (map_natCast (C (σ := σ) (R := 𝓞)) p).symm,
      coeff_mul_C]
    exact Ideal.mem_span_singleton'.2 ⟨coeff μ g, rfl⟩
  · intro hf
    choose g hg using fun μ => Ideal.mem_span_singleton'.1 (hf μ)
    refine Ideal.mem_span_singleton'.2 ⟨(fun μ => g μ : MvPowerSeries σ 𝓞), ?_⟩
    ext μ
    rw [show (p : MvPowerSeries σ 𝓞) = C (p : 𝓞) from (map_natCast (C (σ := σ) (R := 𝓞)) p).symm,
      coeff_mul_C]
    exact hg μ

theorem mem_span_natCast_pow_iff (s : ℕ) (f : MvPowerSeries σ 𝓞) :
    f ∈ Ideal.span {(p : MvPowerSeries σ 𝓞) ^ s} ↔ ∀ μ, coeff μ f ∈ Ideal.span {(p : 𝓞) ^ s} := by
  have hC : (p : MvPowerSeries σ 𝓞) ^ s = C ((p : 𝓞) ^ s) := by
    rw [map_pow, show (p : MvPowerSeries σ 𝓞) = C (p : 𝓞) from (map_natCast (C (σ := σ) (R := 𝓞)) p).symm]
  constructor
  · intro hf μ
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 hf
    rw [hC, coeff_mul_C]
    exact Ideal.mem_span_singleton'.2 ⟨coeff μ g, rfl⟩
  · intro hf
    choose g hg using fun μ => Ideal.mem_span_singleton'.1 (hf μ)
    refine Ideal.mem_span_singleton'.2 ⟨(fun μ => g μ : MvPowerSeries σ 𝓞), ?_⟩
    ext μ
    rw [hC, coeff_mul_C]
    exact hg μ

theorem natCast_mem_nonZeroDivisors (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) :
    (p : MvPowerSeries σ 𝓞) ∈ nonZeroDivisors (MvPowerSeries σ 𝓞) := by
  rw [show (p : MvPowerSeries σ 𝓞) = C (p : 𝓞) from (map_natCast (C (σ := σ) (R := 𝓞)) p).symm]
  refine mem_nonZeroDivisors_iff_right.2 fun f hf => ?_
  ext μ
  have := congrArg (coeff μ) hf
  rw [coeff_mul_C, coeff_zero] at this
  simpa using (mem_nonZeroDivisors_iff_right.1 hp) _ this

theorem isReduced_quotient (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) [Algebra 𝓞 (ZMod p)]
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) :
    IsReduced (MvPowerSeries σ 𝓞 ⧸ Ideal.span {(p : MvPowerSeries σ 𝓞)}) := by
  refine ⟨fun x ⟨k, hk⟩ => ?_⟩
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem] at hk
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_span_C_iff p hp]
  intro μ

  have hmap : MvPowerSeries.map (algebraMap 𝓞 (ZMod p)) (f ^ k) = 0 := by
    ext ν
    rw [coeff_map, coeff_zero]
    have := (mem_span_C_iff p hp _).1 hk ν
    rw [← hker] at this
    exact this
  rw [map_pow] at hmap
  have h0 : MvPowerSeries.map (algebraMap 𝓞 (ZMod p)) f = 0 := IsReduced.eq_zero _ ⟨k, hmap⟩
  have := congrArg (coeff μ) h0
  rw [coeff_map, coeff_zero] at this
  rw [← hker]
  exact this

theorem exists_le_degree_eq [DecidableEq σ] : ∀ (E : ℕ) (μ : σ →₀ ℕ), E ≤ μ.degree → ∃ ν : σ →₀ ℕ, ν ≤ μ ∧ ν.degree = E
  | 0, μ, _ => ⟨0, by simp, by simp⟩
  | E + 1, μ, h => by
    obtain ⟨ν, hν, hνE⟩ := exists_le_degree_eq E μ (Nat.le_of_succ_le h)

    have hne : μ - ν ≠ 0 := by
      intro h0
      have : μ = ν := le_antisymm (tsub_eq_zero_iff_le.1 h0) hν
      rw [this, hνE] at h
      omega
    obtain ⟨t, ht⟩ : ∃ t, (μ - ν) t ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (Finsupp.ext hall)
    refine ⟨ν + Finsupp.single t 1, ?_, ?_⟩
    · intro s
      simp only [Finsupp.coe_add, Pi.add_apply]
      have h1 := hν s
      have h2 : (μ - ν) t = μ t - ν t := Finsupp.tsub_apply _ _ _
      by_cases hst : t = s
      · subst hst
        rw [Finsupp.single_eq_same]
        omega
      · rw [Finsupp.single_apply, if_neg hst, add_zero]
        exact h1
    · rw [map_add, hνE, Finsupp.degree_single]

theorem monomial_mem_pow (ν : σ →₀ ℕ) :
    (monomial ν (1 : 𝓞) : MvPowerSeries σ 𝓞) ∈ (Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝓞))) ^ ν.degree := by
  classical
  induction ν using Finsupp.induction with
  | zero => simp
  | single_add t n ν ht hn ih =>
    rw [show (monomial (Finsupp.single t n + ν) (1 : 𝓞) : MvPowerSeries σ 𝓞) =
        monomial (Finsupp.single t n) 1 * monomial ν 1 by rw [monomial_mul_monomial, one_mul],
      map_add, Finsupp.degree_single, pow_add]
    refine Ideal.mul_mem_mul ?_ ih
    rw [show (monomial (Finsupp.single t n) (1 : 𝓞) : MvPowerSeries σ 𝓞) = X t ^ n by
      rw [X_pow_eq]]
    exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self t)) n

theorem mem_pow_of_forall_le_degree [Fintype σ] [DecidableEq σ] (E : ℕ) (f : MvPowerSeries σ 𝓞)
    (hf : ∀ μ : σ →₀ ℕ, coeff μ f ≠ 0 → E ≤ μ.degree) :
    f ∈ (Ideal.span (Set.range (X : σ → MvPowerSeries σ 𝓞))) ^ E := by
  classical

  let fl : (σ →₀ ℕ) → (σ →₀ ℕ) := fun μ =>
    if h : E ≤ μ.degree then Classical.choose (exists_le_degree_eq (σ := σ) E μ h) else 0
  have hfl : ∀ μ, E ≤ μ.degree → fl μ ≤ μ ∧ (fl μ).degree = E := fun μ h => by
    simp only [fl, dif_pos h]; exact Classical.choose_spec (exists_le_degree_eq (σ := σ) E μ h)

  let g : (σ →₀ ℕ) → MvPowerSeries σ 𝓞 := fun ν κ => if fl (κ + ν) = ν then coeff (κ + ν) f else 0
  let S : Finset (σ →₀ ℕ) := (Finset.univ : Finset σ).finsuppAntidiag E
  have hS : ∀ ν : σ →₀ ℕ, ν ∈ S ↔ ν.degree = E := fun ν => by
    show ν ∈ (Finset.univ : Finset σ).finsuppAntidiag E ↔ _
    have hsum : ∑ i ∈ ν.support, ν i = ∑ i, ν i :=
      Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)
    rw [Finset.mem_finsuppAntidiag, Finsupp.degree_apply, hsum]
    simp
  have hdec : f = ∑ ν ∈ S, monomial ν (1 : 𝓞) * g ν := by
    ext κ
    rw [map_sum]
    simp only [coeff_monomial_mul, one_mul]
    by_cases hκ : E ≤ κ.degree
    · obtain ⟨hle, hdeg⟩ := hfl κ hκ
      rw [Finset.sum_eq_single (fl κ)]
      · rw [if_pos hle]
        show coeff κ f = (if fl (κ - fl κ + fl κ) = fl κ then coeff (κ - fl κ + fl κ) f else 0)
        rw [tsub_add_cancel_of_le hle, if_pos rfl]
      · intro ν hν hne
        split_ifs with hνκ
        · show (if fl (κ - ν + ν) = ν then coeff (κ - ν + ν) f else 0) = 0
          rw [tsub_add_cancel_of_le hνκ, if_neg (Ne.symm hne)]
        · rfl
      · intro hnot
        exact absurd ((hS _).2 hdeg) hnot
    · have h0 : coeff κ f = 0 := by
        by_contra hne; exact hκ (hf κ hne)
      rw [h0, eq_comm]
      refine Finset.sum_eq_zero fun ν hν => ?_
      split_ifs with hνκ
      · show (if fl (κ - ν + ν) = ν then coeff (κ - ν + ν) f else 0) = 0
        rw [tsub_add_cancel_of_le hνκ]
        split_ifs
        · exact h0
        · rfl
      · rfl
  rw [hdec]
  refine Ideal.sum_mem _ fun ν hν => ?_
  have := monomial_mem_pow (𝓞 := 𝓞) ν
  rw [(hS ν).1 hν] at this
  exact Ideal.mul_mem_right _ _ this

end PS

theorem pow_sub_self_mem [Algebra 𝓞 (ZMod p)]
    (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)}) (c : 𝓞) :
    c ^ p - c ∈ Ideal.span {(p : 𝓞)} := by
  rw [← hker, RingHom.mem_ker, map_sub, map_pow, ZMod.pow_card, sub_self]

section Arith
variable {𝓞 : Type*} [CommRing 𝓞] {p : ℕ} [hp : Fact p.Prime] {d : ℕ}

omit hp in
theorem mem_span_pow_of_pow_mul_mem (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞) {a : 𝓞} {K e : ℕ} (hKe : K ≤ e)
    (h : (p : 𝓞) ^ K * a ∈ Ideal.span {(p : 𝓞) ^ e}) : a ∈ Ideal.span {(p : 𝓞) ^ (e - K)} := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h
  refine Ideal.mem_span_singleton'.2 ⟨b, ?_⟩
  have h0 : (p : 𝓞) ^ K * (b * (p : 𝓞) ^ (e - K) - a) = 0 := by
    rw [mul_sub, sub_eq_zero, ← hb, mul_comm ((p : 𝓞) ^ K), mul_assoc, ← pow_add, Nat.sub_add_cancel hKe]
  exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 (pow_mem hpR K)).1 _ h0)

theorem mem_span_pow_of_natCast_mul_mem {u : ℕ} (hu : ¬ p ∣ u) {a : 𝓞} {e : ℕ}
    (h : (u : 𝓞) * a ∈ Ideal.span {(p : 𝓞) ^ e}) : a ∈ Ideal.span {(p : 𝓞) ^ e} := by
  have hcop : IsCoprime (u : ℤ) ((p : ℤ) ^ e) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hu).symm)
  obtain ⟨x, y, hxy⟩ := hcop
  have h1 : ((x : 𝓞) * (u : 𝓞) + (y : 𝓞) * (p : 𝓞) ^ e) = 1 := by
    have := congrArg (Int.castRingHom 𝓞) hxy
    simpa using this
  have : a = (x : 𝓞) * ((u : 𝓞) * a) + (p : 𝓞) ^ e * ((y : 𝓞) * a) := by
    calc a = ((x : 𝓞) * (u : 𝓞) + (y : 𝓞) * (p : 𝓞) ^ e) * a := by rw [h1, one_mul]
      _ = _ := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

omit hp in
theorem natCast_mul_coeff_mem (φi : MvPowerSeries (Fin d) 𝓞)
    (hint : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * coeff (m + Finsupp.single j 1) φi ∈ Ideal.span {(p : 𝓞) ^ m.degree})
    (M' : Fin d →₀ ℕ) (i : Fin d) (hi : 1 ≤ M' i) :
    ((M' i : ℕ) : 𝓞) * coeff M' φi ∈ Ideal.span {(p : 𝓞) ^ (M'.degree - 1)} := by
  have hle : Finsupp.single i 1 ≤ M' := Finsupp.single_le_iff.2 hi
  set m := M' - Finsupp.single i 1 with hm
  have hM : m + Finsupp.single i 1 = M' := tsub_add_cancel_of_le hle
  have h1 : m i + 1 = M' i := by
    conv_rhs => rw [← hM]
    simp
  have h2 : m.degree = M'.degree - 1 := by
    conv_rhs => rw [← hM]
    rw [map_add, Finsupp.degree_single]
    simp
  have := hint i m
  rwa [h1, hM, h2] at this

omit hp in

theorem natCast_mul_coeff_trunc_mem (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (φi : MvPowerSeries (Fin d) 𝓞)
    (hint : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * coeff (m + Finsupp.single j 1) φi ∈ Ideal.span {(p : 𝓞) ^ m.degree})
    (M : ℕ) (hM : 1 ≤ M) (G : MvPowerSeries (Fin d) 𝓞)
    (hG : ∀ m : Fin d →₀ ℕ,
      (m.degree ≤ M → G.coeff m = (p : 𝓞) ^ (M - m.degree) * φi.coeff m) ∧
      (M < m.degree → G.coeff m * (p : 𝓞) ^ (m.degree - M) = φi.coeff m ∨
        (G.coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - M) ∣ φi.coeff m)))
    (m : Fin d →₀ ℕ) (j : Fin d) :
    ((m j : ℕ) : 𝓞) * coeff m G ∈ Ideal.span {(p : 𝓞) ^ (M - 1)} := by
  by_cases hj : m j = 0
  · rw [hj, Nat.cast_zero, zero_mul]; exact zero_mem _
  have hA := natCast_mul_coeff_mem φi hint m j (Nat.one_le_iff_ne_zero.2 hj)
  have hdeg : 1 ≤ m.degree := (Nat.one_le_iff_ne_zero.2 hj).trans (Finsupp.le_degree j m)
  rcases le_or_gt m.degree M with hle | hlt
  · rw [show coeff m G = G.coeff m from rfl, (hG m).1 hle, mul_left_comm]
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hA
    refine Ideal.mem_span_singleton'.2 ⟨b, ?_⟩
    rw [show coeff m φi = φi.coeff m from rfl] at hb
    rw [← hb, show M - 1 = (M - m.degree) + (m.degree - 1) by omega, pow_add]
    ring
  · rcases (hG m).2 hlt with h | ⟨h0, -⟩
    · have hx : (p : 𝓞) ^ (m.degree - M) * (((m j : ℕ) : 𝓞) * coeff m G) ∈
          Ideal.span {(p : 𝓞) ^ (m.degree - 1)} := by
        have : (p : 𝓞) ^ (m.degree - M) * (((m j : ℕ) : 𝓞) * coeff m G) =
            ((m j : ℕ) : 𝓞) * (G.coeff m * (p : 𝓞) ^ (m.degree - M)) := by
          rw [show coeff m G = G.coeff m from rfl]; ring
        rw [this, h]
        exact hA
      have := mem_span_pow_of_pow_mul_mem hpR (by omega) hx
      rwa [show m.degree - 1 - (m.degree - M) = M - 1 by omega] at this
    · rw [show coeff m G = G.coeff m from rfl, h0, mul_zero]; exact zero_mem _

end Arith

end S17DO

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {d : ℕ} (φi : MvPowerSeries (Fin d) 𝓞)
    (hφint : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * φi.coeff (m + Finsupp.single j 1) ∈ Ideal.span {(p : 𝓞) ^ m.degree})
    (A B C : ℕ) (hAB : A < B)
    (hslope : ∀ m : Fin d →₀ ℕ, m ≠ 0 →
      φi.coeff m ∈ Ideal.span {(p : 𝓞) ^ ((m.degree - 1) - (A * Nat.log p m.degree) / B - C)})
    (E : ℕ) :
    ∃ n₂ : ℕ, ∀ (M : ℕ) (c : (Fin d →₀ ℕ) → 𝓞),
      (∀ m : Fin d →₀ ℕ,
        (m.degree ≤ M → c m = (p : 𝓞) ^ (M - m.degree) * φi.coeff m) ∧
        (M < m.degree → c m * (p : 𝓞) ^ (m.degree - M) = φi.coeff m ∨
          (c m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - M) ∣ φi.coeff m))) →
      ∀ ℓ : WittVector p (MvPowerSeries (Fin d) 𝓞),
        (∀ n : ℕ, n < M → ∀ m' : Fin d →₀ ℕ,
          (WittVector.ghostComponent n ℓ).coeff m' = c (p ^ (M - 1 - n) • m')) →
        ∀ j : ℕ, j + n₂ < M →
          ℓ.coeff j ∈ Ideal.span {(p : MvPowerSeries (Fin d) 𝓞)} ⊔
            (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞))) ^ E := by
  classical

  rcases Nat.eq_zero_or_pos E with hE0 | hEpos
  · refine ⟨0, fun M c hc ℓ hℓ j hj => ?_⟩
    rw [hE0, pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_sup_right Submodule.mem_top

  set Lg := Nat.log p E with hLg
  set T := C + 3 + Lg with hT
  refine ⟨B * T, fun M c hc ℓ hℓ j hj => ?_⟩
  have hpP : p.Prime := Fact.out
  have hBpos : 0 < B := lt_of_le_of_lt (Nat.zero_le A) hAB
  have hM1 : 1 ≤ M := by omega
  have hjM : j < M := by omega
  set n := M - 1 - j with hn
  have hnBT : B * T ≤ n := by omega
  have hMn : M - 1 - n = j := by omega

  set K := E * p ^ n with hK
  set qK := A * Nat.log p K / B with hqK
  set s := M - 1 - qK - C with hs

  have hlogK : Nat.log p K = Lg + n := by
    rw [hK, hLg]
    clear hK hnBT hMn hn
    induction n with
    | zero => rw [pow_zero, mul_one, add_zero]
    | succ n ih => rw [pow_succ, ← mul_assoc, Nat.log_mul_base hpP.one_lt (Nat.mul_ne_zero (by omega) (pow_ne_zero _ hpP.ne_zero)), ih, add_assoc]
  have hq : qK + T ≤ Lg + n := by
    have h1 : B * qK ≤ A * (Lg + n) := by rw [hqK, hlogK]; exact Nat.mul_div_le _ _
    have h2 : A * (Lg + n) + (Lg + n) ≤ B * (Lg + n) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hAB
    have h4 : B * (qK + T) ≤ B * (Lg + n) := by
      rw [Nat.mul_add]
      calc B * qK + B * T ≤ A * (Lg + n) + (Lg + n) := Nat.add_le_add h1 (hnBT.trans (Nat.le_add_left n Lg))
        _ ≤ B * (Lg + n) := h2
    exact Nat.le_of_mul_le_mul_left h4 hBpos
  have hsj : j + 3 ≤ s := by omega

  have hfrob : ∀ a : 𝓞, a ^ p - a ∈ Ideal.span {(p : 𝓞)} := S17DO.pow_sub_self_mem p hker
  have hp𝓑 := S17DO.natCast_mem_nonZeroDivisors (σ := Fin d) p hp

  let G : MvPowerSeries (Fin d) 𝓞 := fun m => c m
  let Glo : MvPowerSeries (Fin d) 𝓞 := fun m => if m.degree ≤ K then c m else 0
  let Ghi : MvPowerSeries (Fin d) 𝓞 := fun m => if m.degree ≤ K then 0 else c m
  have hGc : ∀ m, coeff m G = c m := fun m => rfl
  have hGlo : ∀ m, coeff m Glo = if m.degree ≤ K then c m else 0 := fun m => rfl
  have hGhi : ∀ m, coeff m Ghi = if m.degree ≤ K then 0 else c m := fun m => rfl
  have hGpin : ∀ m : Fin d →₀ ℕ,
      (m.degree ≤ M → G.coeff m = (p : 𝓞) ^ (M - m.degree) * φi.coeff m) ∧
      (M < m.degree → G.coeff m * (p : 𝓞) ^ (m.degree - M) = φi.coeff m ∨
        (G.coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - M) ∣ φi.coeff m)) := fun m => hc m

  have hdiffG : ∀ (m : Fin d →₀ ℕ) (t : Fin d), ((m t : ℕ) : 𝓞) * coeff m G ∈ Ideal.span {(p : 𝓞) ^ (M - 1)} :=
    fun m t => S17DO.natCast_mul_coeff_trunc_mem hp φi hφint M hM1 G hGpin m t
  have hdiffLo : ∀ (m : Fin d →₀ ℕ) (t : Fin d), ((m t : ℕ) : 𝓞) * coeff m Glo ∈ Ideal.span {(p : 𝓞) ^ (M - 1)} := by
    intro m t; rw [hGlo]; split_ifs
    · exact hdiffG m t
    · rw [mul_zero]; exact zero_mem _
  have hdiffHi : ∀ (m : Fin d →₀ ℕ) (t : Fin d), ((m t : ℕ) : 𝓞) * coeff m Ghi ∈ Ideal.span {(p : 𝓞) ^ (M - 1)} := by
    intro m t; rw [hGhi]; split_ifs
    · rw [mul_zero]; exact zero_mem _
    · exact hdiffG m t

  obtain ⟨ℓlo, hℓlo⟩ :=
    MvPowerSeries.exists_wittVector_forall_coeff_ghostComponent_eq_of_forall_natCast_mul_coeff_mem p hp hfrob M Glo
      hdiffLo
  obtain ⟨ℓhi, hℓhi⟩ :=
    MvPowerSeries.exists_wittVector_forall_coeff_ghostComponent_eq_of_forall_natCast_mul_coeff_mem p hp hfrob M Ghi
      hdiffHi

  have hghost : ∀ k < M, WittVector.ghostComponent k ℓ = WittVector.ghostComponent k (ℓlo + ℓhi) := by
    intro k hk
    ext μ'
    rw [map_add, map_add, show coeff μ' (WittVector.ghostComponent k ℓ) = c (p ^ (M - 1 - k) • μ') from hℓ k hk μ',
      hℓlo k hk μ', hℓhi k hk μ', hGlo, hGhi]
    split_ifs <;> simp
  have hcomp : ∀ k < M, ℓ.coeff k = (ℓlo + ℓhi).coeff k :=
    WittVector.coeff_eq_coeff_of_forall_ghostComponent_eq p hp𝓑 M ℓ (ℓlo + ℓhi) hghost

  have hspan_mono : ∀ {x : 𝓞} {a b : ℕ}, a ≤ b → x ∈ Ideal.span {(p : 𝓞) ^ b} → x ∈ Ideal.span {(p : 𝓞) ^ a} :=
    fun hab hx => Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hab) hx
  have hlowdiv : ∀ ν : Fin d →₀ ℕ, ν.degree ≤ K → c ν ∈ Ideal.span {(p : 𝓞) ^ s} := by
    intro ν hνK
    by_cases hν0 : ν = 0
    · subst hν0
      have h0 := (hc 0).1 (by simp)
      rw [h0]
      simp only [map_zero, tsub_zero]
      refine hspan_mono (show s ≤ M from
        (Nat.sub_le _ C).trans ((Nat.sub_le _ qK).trans (Nat.sub_le M 1))) ?_
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    have hsl := hslope ν hν0
    set q := A * Nat.log p ν.degree / B with hq'
    have hqq : q ≤ qK := by
      rw [hq', hqK]
      exact Nat.div_le_div_right (Nat.mul_le_mul_left _ (Nat.log_mono_right hνK))
    have hdeg1 : 1 ≤ ν.degree := by
      rw [Nat.one_le_iff_ne_zero]; exact fun h => hν0 ((Finsupp.degree_eq_zero_iff ν).1 h)
    rcases le_or_gt ν.degree M with hle | hlt
    · rw [(hc ν).1 hle]
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hsl
      have : (p : 𝓞) ^ (M - ν.degree) * φi.coeff ν ∈ Ideal.span {(p : 𝓞) ^ (M - ν.degree + (ν.degree - 1 - q - C))} := by
        rw [show φi.coeff ν = coeff ν φi from rfl, ← hb, pow_add]
        exact Ideal.mem_span_singleton'.2 ⟨b, by ring⟩
      exact hspan_mono (by omega) this
    · rcases (hc ν).2 hlt with h | ⟨h0, -⟩
      ·
        by_cases hcase : ν.degree - M ≤ ν.degree - 1 - q - C
        · have hx : (p : 𝓞) ^ (ν.degree - M) * c ν ∈ Ideal.span {(p : 𝓞) ^ (ν.degree - 1 - q - C)} := by
            rw [mul_comm, h]; exact hsl
          exact hspan_mono (by omega) (S17DO.mem_span_pow_of_pow_mul_mem hp hcase hx)
        · have hs0 : s = 0 := by omega
          rw [hs0, pow_zero, Ideal.span_singleton_one]
          exact Submodule.mem_top
      · rw [h0]; exact zero_mem _
  have hghost_lo : ∀ k, k < M → WittVector.ghostComponent k ℓlo ∈ Ideal.span {(p : MvPowerSeries (Fin d) 𝓞) ^ s} := by
    intro k hk
    rw [S17DO.mem_span_natCast_pow_iff]
    intro μ'
    rw [hℓlo k hk μ', hGlo]
    split_ifs with hdeg
    · exact hlowdiv _ hdeg
    · exact zero_mem _
  have hlo_p : ∀ k, k < j + 1 → ℓlo.coeff k ∈ Ideal.span {(p : MvPowerSeries (Fin d) 𝓞)} := by
    intro k hk
    have hk' : k < M := by omega
    have := WittVector.coeff_mem_span_pow_sub_of_forall_ghostComponent_mem_span_pow p hp𝓑 ℓlo s M hghost_lo k hk'
    refine Ideal.span_singleton_le_span_singleton.2 ?_ this
    exact dvd_pow_self _ (by omega)

  have hmodp : ℓ.coeff j - ℓhi.coeff j ∈ Ideal.span {(p : MvPowerSeries (Fin d) 𝓞)} := by
    let π := Ideal.Quotient.mk (Ideal.span {(p : MvPowerSeries (Fin d) 𝓞)})
    have hx : ∀ k : ℕ, k < j + 1 → (WittVector.map π ℓlo).coeff k = 0 := fun k hk => by
      rw [WittVector.map_coeff, Ideal.Quotient.eq_zero_iff_mem]; exact hlo_p k hk
    have hV := WittVector.add_coeff_eq_of_forall_coeff_eq_zero p (WittVector.map π ℓlo) (WittVector.map π ℓhi)
      (j + 1) hx j (Nat.lt_succ_self j)
    rw [← map_add, WittVector.map_coeff, WittVector.map_coeff, ← hcomp j hjM] at hV
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
    exact hV

  have hordj : ℓhi.coeff j ∈ (Ideal.span (Set.range (X : Fin d → MvPowerSeries (Fin d) 𝓞))) ^ E := by
    refine S17DO.mem_pow_of_forall_le_degree E _ fun μ' hμ' => ?_
    have hL : ∀ μ : Fin d →₀ ℕ, coeff μ Ghi ≠ 0 → K + 1 ≤ μ.degree := by
      intro μ hμ; rw [hGhi] at hμ; split_ifs at hμ with hd
      · exact absurd rfl hμ
      · omega
    have hle := MvPowerSeries.le_mul_degree_of_coeff_coeff_ne_zero_of_forall_coeff_ghostComponent_eq p hp M
      (K + 1) Ghi hL ℓhi hℓhi j hjM μ' hμ'
    rw [← hn] at hle
    by_contra hlt
    rw [not_le] at hlt
    have hppos : 0 < p ^ n := pow_pos hpP.pos _
    have hlt' : p ^ n * μ'.degree < E * p ^ n := by rw [mul_comm E]; exact (Nat.mul_lt_mul_left hppos).2 hlt
    rw [hK] at hle
    omega

  have : ℓ.coeff j = (ℓ.coeff j - ℓhi.coeff j) + ℓhi.coeff j := by ring
  rw [this]
  exact Submodule.add_mem_sup hmodp hordj

end S_MvFormalGroup_coeff_mem_span_sup_pow_of_forall_coeff_ghostComponent_eq_logCovector_of_slope
end P2MW
export P2MW.S_MvFormalGroup_coeff_mem_span_sup_pow_of_forall_coeff_ghostComponent_eq_logCovector_of_slope (solution)
