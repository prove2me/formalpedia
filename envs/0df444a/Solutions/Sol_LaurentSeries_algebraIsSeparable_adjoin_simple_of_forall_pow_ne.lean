-- Prove2me | solution 1 for LaurentSeries.algebraIsSeparable_adjoin_simple_of_forall_pow_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/62761254-128b-5924-a400-e4eefe4ac4d3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LaurentSeries_algebraIsSeparable_adjoin_simple_of_forall_pow_ne

set_option autoImplicit false

open scoped IntermediateField
open Polynomial

namespace SepLaurent

section Theta

variable {k : Type} [Field k]

noncomputable def thetaFun (f : LaurentSeries k) : LaurentSeries k where
  coeff n := (n : k) * f.coeff n
  isPWO_support' := f.isPWO_support.mono fun n hn => by
    simp only [Function.mem_support, ne_eq] at hn ⊢
    exact fun h => hn (by rw [h, mul_zero])

@[scoped simp] theorem coeff_thetaFun (f : LaurentSeries k) (n : ℤ) :
    (thetaFun f).coeff n = (n : k) * f.coeff n := rfl

theorem support_thetaFun_subset (f : LaurentSeries k) : (thetaFun f).support ⊆ f.support := by
  intro n hn
  simp only [HahnSeries.mem_support, coeff_thetaFun, ne_eq] at hn ⊢
  exact fun h => hn (by rw [h, mul_zero])

theorem thetaFun_add (f g : LaurentSeries k) : thetaFun (f + g) = thetaFun f + thetaFun g := by
  ext n; simp [mul_add]

theorem thetaFun_mul (f g : LaurentSeries k) :
    thetaFun (f * g) = thetaFun f * g + f * thetaFun g := by
  ext n
  rw [HahnSeries.coeff_add, coeff_thetaFun, HahnSeries.coeff_mul,
    HahnSeries.coeff_mul_left' f.isPWO_support (support_thetaFun_subset f),
    HahnSeries.coeff_mul_right' g.isPWO_support (support_thetaFun_subset g),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨-, -, h⟩ := hij
  simp only [coeff_thetaFun]
  rw [← h, Int.cast_add]
  ring

noncomputable def theta : LaurentSeries k →+ LaurentSeries k :=
  AddMonoidHom.mk' thetaFun thetaFun_add

@[scoped simp] theorem theta_apply (f : LaurentSeries k) : theta f = thetaFun f := rfl

theorem theta_leibniz (a b : LaurentSeries k) : theta (a * b) = a * theta b + b * theta a := by
  simp only [theta_apply, thetaFun_mul]
  ring

variable (p : ℕ) [Fact p.Prime] [CharP k p]

omit [Fact p.Prime] in
theorem coeff_eq_zero_of_thetaFun_eq_zero {f : LaurentSeries k} (hf : thetaFun f = 0) {n : ℤ}
    (hn : ¬ (p : ℤ) ∣ n) : f.coeff n = 0 := by
  have h := congrArg (fun g : LaurentSeries k => g.coeff n) hf
  simp only [coeff_thetaFun, HahnSeries.coeff_zero, mul_eq_zero] at h
  rcases h with h | h
  · exact absurd ((CharP.intCast_eq_zero_iff k p n).mp h) hn
  · exact h

theorem powerSeries_exists_pow_eq [PerfectRing k p] (g : PowerSeries k)
    (hg : ∀ n : ℕ, ¬ p ∣ n → PowerSeries.coeff n g = 0) : ∃ h : PowerSeries k, h ^ p = g := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  let g₀ : PowerSeries k := PowerSeries.mk fun n => PowerSeries.coeff (p * n) g
  have hg₀ : PowerSeries.expand p hp g₀ = g := by
    ext n
    rw [PowerSeries.coeff_expand]
    split_ifs with h
    · obtain ⟨m, rfl⟩ := h
      simp [g₀, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hp)]
    · exact (hg n h).symm
  refine ⟨PowerSeries.map ((frobeniusEquiv k p).symm : k →+* k) g₀, ?_⟩
  have key := MvPowerSeries.map_frobenius_expand p hp
    (f := PowerSeries.map ((frobeniusEquiv k p).symm : k →+* k) g₀)
  rw [← key]
  change PowerSeries.map (frobenius k p)
    (PowerSeries.expand p hp (PowerSeries.map ((frobeniusEquiv k p).symm : k →+* k) g₀)) = g
  rw [← hg₀]
  ext n
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_expand]
  split_ifs
  · simp [frobenius_apply_frobeniusEquiv_symm]
  · simp

theorem exists_pow_eq_of_thetaFun_eq_zero [PerfectRing k p] {f : LaurentSeries k}
    (hf : thetaFun f = 0) : ∃ g : LaurentSeries k, g ^ p = f := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  by_cases hf0 : f = 0
  · exact ⟨0, by rw [hf0, zero_pow hp]⟩
  have hcoeff : ∀ n : ℤ, ¬ (p : ℤ) ∣ n → f.coeff n = 0 := fun n hn =>
    coeff_eq_zero_of_thetaFun_eq_zero p hf hn
  have hord : (p : ℤ) ∣ f.order := by
    by_contra h
    exact hf0 (HahnSeries.coeff_order_eq_zero.mp (hcoeff _ h))
  obtain ⟨m, hm⟩ := hord
  obtain ⟨h, hh⟩ := powerSeries_exists_pow_eq p (k := k) f.powerSeriesPart
    (fun n hn => by
      rw [LaurentSeries.powerSeriesPart_coeff]
      apply hcoeff
      rw [hm]
      rintro ⟨c, hc⟩
      apply hn
      have : (n : ℤ) = p * (c - m) := by linarith
      exact Int.natCast_dvd_natCast.mp ⟨c - m, this⟩)
  refine ⟨HahnSeries.single m 1 * HahnSeries.ofPowerSeries ℤ k h, ?_⟩
  rw [mul_pow, HahnSeries.single_pow, one_pow, ← map_pow, hh, nsmul_eq_mul, ← hm,
    LaurentSeries.single_order_mul_powerSeriesPart]

theorem theta_ne_zero_of_forall_pow_ne [PerfectRing k p] {f : LaurentSeries k}
    (hf : ∀ v : LaurentSeries k, v ^ p ≠ f) : theta f ≠ 0 := fun h => by
  obtain ⟨g, hg⟩ := exists_pow_eq_of_thetaFun_eq_zero p h
  exact hf g hg

scoped instance charP_laurentSeries : CharP (LaurentSeries k) p :=
  charP_of_injective_algebraMap (algebraMap k (LaurentSeries k)).injective p

end Theta

section Leibniz

variable {Ω : Type*} [Field Ω] (D : Ω →+ Ω) (hD : ∀ a b : Ω, D (a * b) = a * D b + b * D a)

include hD

theorem leibniz_map_one : D 1 = 0 := by
  have h := hD 1 1
  rw [one_mul, one_mul] at h
  have h2 : D 1 + D 1 = D 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h2

theorem leibniz_map_pow_succ (a : Ω) (n : ℕ) :
    D (a ^ (n + 1)) = (n + 1 : Ω) * a ^ n * D a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, hD, ih]
    push_cast
    ring

theorem leibniz_map_pow_p (p : ℕ) [Fact p.Prime] [CharP Ω p] (a : Ω) : D (a ^ p) = 0 := by
  obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := Nat.exists_eq_succ_of_ne_zero (Fact.out : p.Prime).ne_zero
  rw [hn, leibniz_map_pow_succ D hD]
  have : ((n : Ω) + 1) = ((n + 1 : ℕ) : Ω) := by push_cast; ring
  rw [this, ← hn, CharP.cast_eq_zero, zero_mul, zero_mul]

theorem isSeparable_of_leibniz_map {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra E Ω]
    (p : ℕ) [Fact p.Prime] [CharP Ω p] (u : Ω) (hu : u ≠ 0)
    (hK : ∀ c : K, ∃ e : K,
      D (algebraMap E Ω (algebraMap K E c)) = algebraMap E Ω (algebraMap K E e) * u)
    (hKp : ∀ c : K, D (algebraMap E Ω (algebraMap K E c)) = 0 → ∃ d : K, d ^ p = c)
    [hfin : FiniteDimensional K E] : Algebra.IsSeparable K E := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : CharP E p := (algebraMap E Ω).charP (algebraMap E Ω).injective p
  haveI : CharP K p := (algebraMap K E).charP (algebraMap K E).injective p
  haveI : ExpChar E p := ExpChar.prime Fact.out
  haveI : ExpChar K p := ExpChar.prime Fact.out
  by_contra hsep
  have hS : separableClosure K E ≠ ⊤ := fun h => hsep ((separableClosure.eq_top_iff K E).mp h)

  obtain ⟨x, hxS, hxpS⟩ : ∃ x : E, x ∉ separableClosure K E ∧ x ^ p ∈ separableClosure K E := by
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : E, x₀ ∉ separableClosure K E := by
      by_contra! h
      exact hS (eq_top_iff.2 fun x _ => h x)
    obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem (separableClosure K E) p x₀
    classical
    have hex : ∃ n, x₀ ^ p ^ n ∈ separableClosure K E := ⟨n, by rw [← hy]; exact y.2⟩
    have hN : x₀ ^ p ^ Nat.find hex ∈ separableClosure K E := Nat.find_spec hex
    have hN0 : Nat.find hex ≠ 0 := by
      intro h0
      rw [h0, pow_zero, pow_one] at hN
      exact hx₀ hN
    refine ⟨x₀ ^ p ^ (Nat.find hex - 1), Nat.find_min hex (Nat.sub_one_lt hN0), ?_⟩
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hN0)]
    exact hN

  set y : E := x ^ p with hydef
  have hyint : IsIntegral K y := .of_finite K y
  have hxint : IsIntegral K x := .of_finite K x
  set m : K[X] := minpoly K y with hmdef
  set d : ℕ := m.natDegree with hddef
  set yΩ : Ω := algebraMap E Ω y with hyΩ
  have hDy : D yΩ = 0 := by
    rw [hyΩ, hydef, map_pow]
    exact leibniz_map_pow_p D hD p _
  have hDyi : ∀ i : ℕ, D (yΩ ^ i) = 0 := fun i => by
    cases i with
    | zero => rw [pow_zero]; exact leibniz_map_one D hD
    | succ j => rw [leibniz_map_pow_succ D hD, hDy, mul_zero]
  have hm : m.Monic := minpoly.monic hyint

  have hrelE : y ^ d + ∑ i ∈ Finset.range d, algebraMap K E (m.coeff i) * y ^ i = 0 := by
    have h := minpoly.aeval K y
    rw [← hmdef] at h
    conv_lhs at h => rw [hm.as_sum]
    rw [map_add, map_pow, aeval_X, map_sum] at h
    simp_rw [map_mul, map_pow, aeval_X, aeval_C] at h
    exact h
  have hrelΩ : yΩ ^ d + ∑ i ∈ Finset.range d,
      algebraMap E Ω (algebraMap K E (m.coeff i)) * yΩ ^ i = 0 := by
    have h := congrArg (algebraMap E Ω) hrelE
    rw [map_add, map_pow, map_sum, map_zero] at h
    simp_rw [map_mul, map_pow] at h
    exact h

  choose e he using hK
  have hDrel : (∑ i ∈ Finset.range d,
      algebraMap E Ω (algebraMap K E (e (m.coeff i))) * yΩ ^ i) * u = 0 := by
    have h1 : D (yΩ ^ d + ∑ i ∈ Finset.range d,
        algebraMap E Ω (algebraMap K E (m.coeff i)) * yΩ ^ i) =
        (∑ i ∈ Finset.range d, algebraMap E Ω (algebraMap K E (e (m.coeff i))) * yΩ ^ i) * u := by
      rw [map_add, hDyi, zero_add, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hD, hDyi, mul_zero, zero_add, he]
      ring
    rw [hrelΩ, map_zero] at h1
    exact h1.symm
  have hsum0 : ∑ i ∈ Finset.range d,
      algebraMap E Ω (algebraMap K E (e (m.coeff i))) * yΩ ^ i = 0 :=
    (mul_eq_zero.mp hDrel).resolve_right hu
  have hsumE : ∑ i ∈ Finset.range d, algebraMap K E (e (m.coeff i)) * y ^ i = 0 := by
    apply (algebraMap E Ω).injective
    rw [map_sum, map_zero]
    simp_rw [map_mul, map_pow]
    exact hsum0

  have he0 : ∀ i, i < d → e (m.coeff i) = 0 := by
    have hli := linearIndependent_pow (K := K) y
    rw [Fintype.linearIndependent_iff] at hli
    intro i hi
    have hsum' : ∑ j : Fin d, e (m.coeff j) • y ^ (j : ℕ) = 0 := by
      simp_rw [Algebra.smul_def]
      rw [Fin.sum_univ_eq_sum_range (fun j => algebraMap K E (e (m.coeff j)) * y ^ j) d]
      exact hsumE
    exact hli (fun j => e (m.coeff j)) hsum' ⟨i, hi⟩

  have hroot : ∀ i, i < d → ∃ r : K, r ^ p = m.coeff i := fun i hi =>
    hKp _ (by rw [he, he0 i hi, map_zero, map_zero, zero_mul])
  choose! r hr using hroot
  set mt : K[X] := X ^ d + ∑ i : Fin d, C (r i) * X ^ (i : ℕ) with hmtdef
  have hmt_aeval' : aeval x mt = x ^ d + ∑ i ∈ Finset.range d, algebraMap K E (r i) * x ^ i := by
    rw [hmtdef, map_add, map_pow, aeval_X, map_sum]
    simp_rw [map_mul, map_pow, aeval_X, aeval_C]
    rw [Fin.sum_univ_eq_sum_range (fun i => algebraMap K E (r i) * x ^ i) d]
  have hmt_aeval : aeval x mt = 0 := by
    have h2 : (aeval x mt) ^ p =
        y ^ d + ∑ i ∈ Finset.range d, algebraMap K E (m.coeff i) * y ^ i := by
      rw [hmt_aeval', add_pow_char, sum_pow_char]
      congr 1
      · rw [← pow_mul, mul_comm, pow_mul, ← hydef]
      · refine Finset.sum_congr rfl fun i hi => ?_
        rw [mul_pow, ← map_pow, hr i (Finset.mem_range.mp hi), ← pow_mul, mul_comm i p, pow_mul,
          ← hydef]
    exact (pow_eq_zero_iff hp).mp (h2.trans hrelE)
  have hdeg_mt : mt.degree = d := by
    rw [hmtdef, degree_add_eq_left_of_degree_lt, degree_X_pow]
    rw [degree_X_pow]
    exact degree_sum_fin_lt _
  have hmt_ne : mt ≠ 0 := by
    intro h
    rw [h, degree_zero] at hdeg_mt
    exact WithBot.bot_ne_coe hdeg_mt
  have hxdeg : (minpoly K x).natDegree ≤ d := by
    rw [natDegree_le_iff_degree_le, ← hdeg_mt]
    exact minpoly.degree_le_of_ne_zero K x hmt_ne hmt_aeval

  have hfx : Module.finrank K (IntermediateField.adjoin K {x}) = (minpoly K x).natDegree :=
    IntermediateField.adjoin.finrank hxint
  have hfy : Module.finrank K (IntermediateField.adjoin K {y}) = d :=
    IntermediateField.adjoin.finrank hyint
  have hle : IntermediateField.adjoin K {y} ≤ IntermediateField.adjoin K {x} := by
    rw [IntermediateField.adjoin_simple_le_iff, hydef]
    exact pow_mem (IntermediateField.mem_adjoin_simple_self K x) p
  haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
    IntermediateField.adjoin.finiteDimensional hxint
  have heq : IntermediateField.adjoin K {y} = IntermediateField.adjoin K {x} :=
    IntermediateField.eq_of_le_of_finrank_le hle (by rw [hfx, hfy]; exact hxdeg)
  have hxy : x ∈ IntermediateField.adjoin K {y} := by
    rw [heq]; exact IntermediateField.mem_adjoin_simple_self K x
  have hyS : IntermediateField.adjoin K {y} ≤ separableClosure K E :=
    IntermediateField.adjoin_simple_le_iff.mpr hxpS
  exact hxS (hyS hxy)

end Leibniz

section Constants

theorem leibniz_map_algebraMap {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (p : ℕ) [Fact p.Prime] [CharP Ω p] [CharP k p] [PerfectRing k p]
    (D : Ω →+ Ω) (hD : ∀ a b : Ω, D (a * b) = a * D b + b * D a) (c : k) :
    D (algebraMap k Ω c) = 0 := by
  conv_lhs => rw [← frobenius_apply_frobeniusEquiv_symm k p c]
  rw [frobenius_def, map_pow]
  exact leibniz_map_pow_p D hD p _

noncomputable def toDerivation {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (p : ℕ) [Fact p.Prime] [CharP Ω p] [CharP k p] [PerfectRing k p]
    (D : Ω →+ Ω) (hD : ∀ a b : Ω, D (a * b) = a * D b + b * D a) : Derivation k Ω Ω where
  toFun := D
  map_add' := D.map_add
  map_smul' c a := by
    simp only [RingHom.id_apply]
    rw [Algebra.smul_def, Algebra.smul_def, hD, leibniz_map_algebraMap p D hD, mul_zero, add_zero]
  map_one_eq_zero' := leibniz_map_one D hD
  leibniz' a b := by
    change D (a * b) = a * D b + b * D a
    exact hD a b

theorem toDerivation_apply {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (p : ℕ) [Fact p.Prime] [CharP Ω p] [CharP k p] [PerfectRing k p]
    (D : Ω →+ Ω) (hD : ∀ a b : Ω, D (a * b) = a * D b + b * D a) (a : Ω) :
    toDerivation (k := k) p D hD a = D a := rfl

theorem exists_eq_div_pow {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] (p : ℕ) [Fact p.Prime]
    (E : IntermediateField k Ω) (t : E) (c : E)
    (hc : c ∈ IntermediateField.adjoin k {t}) :
    ∃ R Q : k[X], aeval t Q ≠ 0 ∧ c = aeval t R / (aeval t Q) ^ p := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  obtain ⟨r, s, h⟩ := (IntermediateField.mem_adjoin_simple_iff k c).mp hc
  by_cases hs : aeval t s = 0
  · refine ⟨0, 1, by simp, ?_⟩
    rw [h, hs, div_zero, map_zero, zero_div]
  · refine ⟨r * s ^ (p - 1), s, hs, ?_⟩
    have hsp : (aeval t s) ^ p = aeval t s ^ (p - 1) * aeval t s := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp)]
    rw [map_mul, map_pow, hsp, mul_comm (aeval t s ^ (p - 1)) (aeval t s),
      mul_div_mul_right _ _ (pow_ne_zero _ hs)]
    exact h

theorem leibniz_map_adjoin_simple {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]
    (p : ℕ) [Fact p.Prime] [CharP Ω p] [CharP k p] [PerfectRing k p]
    (D : Ω →+ Ω) (hD : ∀ a b : Ω, D (a * b) = a * D b + b * D a)
    (E : IntermediateField k Ω) (t : E)
    (htr : Transcendental k t) (c : E) (hc : c ∈ IntermediateField.adjoin k {t}) :
    (∃ e : E, e ∈ IntermediateField.adjoin k {t} ∧
        D (algebraMap E Ω c) = algebraMap E Ω e * D (algebraMap E Ω t)) ∧
    (D (algebraMap E Ω t) ≠ 0 → D (algebraMap E Ω c) = 0 →
        ∃ d : E, d ∈ IntermediateField.adjoin k {t} ∧ d ^ p = c) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  let D' : Derivation k Ω Ω := toDerivation p D hD
  have hD' : ∀ a, D a = D' a := fun a => rfl
  obtain ⟨R, Q, hQ, hcRQ⟩ := exists_eq_div_pow p E t c hc
  set tΩ : Ω := algebraMap E Ω t with htΩ
  have hQΩ : aeval tΩ Q ≠ 0 := by
    rw [htΩ, aeval_algebraMap_apply]
    exact (_root_.map_ne_zero _).mpr hQ
  have hcΩ : algebraMap E Ω c = aeval tΩ R / (aeval tΩ Q) ^ p := by
    rw [hcRQ, map_div₀, map_pow, htΩ, ← aeval_algebraMap_apply, ← aeval_algebraMap_apply]
  have hDpow : D' (aeval tΩ Q ^ p) = 0 := leibniz_map_pow_p D hD p _
  have hDc : D (algebraMap E Ω c) = (aeval tΩ (derivative R) / aeval tΩ Q ^ p) * D tΩ := by
    rw [hD', hD', hcΩ, D'.leibniz_div_const _ _ hDpow, D'.map_aeval, smul_eq_mul, smul_eq_mul,
      div_eq_mul_inv]
    ring
  refine ⟨⟨aeval t (derivative R) / aeval t Q ^ p,
    (IntermediateField.mem_adjoin_simple_iff k _).mpr ⟨derivative R, Q ^ p, by rw [map_pow]⟩, ?_⟩, ?_⟩
  · rw [hDc, map_div₀, map_pow, htΩ, ← aeval_algebraMap_apply, ← aeval_algebraMap_apply]
  · intro hDt hDc0
    rw [hDc] at hDc0
    have h1 : aeval tΩ (derivative R) = 0 := by
      rcases mul_eq_zero.mp hDc0 with h | h
      · exact (div_eq_zero_iff.mp h).resolve_right (pow_ne_zero _ hQΩ)
      · exact absurd h hDt
    have h2 : aeval t (derivative R) = 0 := by
      apply (algebraMap E Ω).injective
      rw [← aeval_algebraMap_apply, map_zero]
      exact h1
    have h3 : derivative R = 0 := transcendental_iff.mp htr _ h2
    set R₁ : k[X] := map ((frobeniusEquiv k p).symm : k →+* k) (contract p R) with hR₁
    have hmapR₁ : map (frobenius k p) R₁ = contract p R := by
      rw [hR₁, Polynomial.map_map]
      have hcomp : (frobenius k p).comp ((frobeniusEquiv k p).symm : k →+* k) = RingHom.id k := by
        ext a
        simp
      rw [hcomp, Polynomial.map_id]
    have hR : R = R₁ ^ p := by
      rw [← map_frobenius_expand, map_expand, hmapR₁, expand_contract p h3 hp]
    refine ⟨aeval t R₁ / aeval t Q,
      (IntermediateField.mem_adjoin_simple_iff k _).mpr ⟨R₁, Q, rfl⟩, ?_⟩
    rw [div_pow, ← map_pow, ← hR]
    exact hcRQ.symm

end Constants

end SepLaurent
p2m_reactivate "P2MW.S_LaurentSeries_algebraIsSeparable_adjoin_simple_of_forall_pow_ne.SepLaurent"

open SepLaurent in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (F : IntermediateField k (LaurentSeries k)) (t : ↥F)
    (htr : Transcendental k t) (hp : ∀ v : LaurentSeries k, v ^ p ≠ (t : LaurentSeries k))
    [FiniteDimensional ↥k⟮t⟯ ↥F] :
    Algebra.IsSeparable ↥k⟮t⟯ ↥F := by
  have hfin : FiniteDimensional ↥k⟮t⟯ ↥F := inferInstance
  have hDt : theta (algebraMap F (LaurentSeries k) t) ≠ 0 := theta_ne_zero_of_forall_pow_ne p hp
  refine isSeparable_of_leibniz_map (K := ↥k⟮t⟯) (E := ↥F) theta theta_leibniz p _ hDt
    (fun c => ?_) (fun c hc => ?_) (hfin := hfin)
  · obtain ⟨e, he, h⟩ := (leibniz_map_adjoin_simple p theta theta_leibniz F t htr c c.2).1
    exact ⟨⟨e, he⟩, h⟩
  · obtain ⟨d, hd, h⟩ := (leibniz_map_adjoin_simple p theta theta_leibniz F t htr c c.2).2 hDt hc
    exact ⟨⟨d, hd⟩, Subtype.ext (by rw [← h]; rfl)⟩

end S_LaurentSeries_algebraIsSeparable_adjoin_simple_of_forall_pow_ne
end P2MW
export P2MW.S_LaurentSeries_algebraIsSeparable_adjoin_simple_of_forall_pow_ne (solution)
