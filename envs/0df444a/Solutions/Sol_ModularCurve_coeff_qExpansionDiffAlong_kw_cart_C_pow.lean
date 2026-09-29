-- Prove2me | solution 1 for ModularCurve.coeff_qExpansionDiffAlong_kw_cart_C_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/ddc0db75-183d-5c37-82bd-6b78f42a6a69

import Mathlib
import Definitions.Def_AlgebraicGeometry_KwCartierOperatorTCoordEngine
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_kw_cart_C_pow

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 4000000

namespace CartierQExp

open HahnSeries ModularCurve

variable {K : Type*} [Field K]

theorem coeff_thetaL (f : LaurentSeries K) (n : ℤ) :
    (thetaL K f).coeff n = (n : K) * f.coeff n := by
  rw [thetaL_apply]
  have h := HahnSeries.coeff_single_mul_add (r := (1 : K)) (x := LaurentSeries.derivative K f)
    (a := n - 1) (b := (1 : ℤ))
  rw [sub_add_cancel] at h
  rw [h, one_mul, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff]
  have h2 : n - 1 + ((1 : ℕ) : ℤ) = n := by push_cast; ring
  rw [h2, Ring.choose_one_right, zsmul_eq_mul]

theorem support_thetaL_subset (f : LaurentSeries K) : (thetaL K f).support ⊆ f.support := by
  intro n hn
  rw [HahnSeries.mem_support, coeff_thetaL] at hn
  rw [HahnSeries.mem_support]
  intro h
  exact hn (by rw [h, mul_zero])

theorem thetaL_mul (f g : LaurentSeries K) :
    thetaL K (f * g) = f * thetaL K g + thetaL K f * g := by
  ext n
  rw [coeff_add, coeff_thetaL, coeff_mul,
    coeff_mul_right' g.isPWO_support (support_thetaL_subset g),
    coeff_mul_left' f.isPWO_support (support_thetaL_subset f),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨-, -, hsum⟩ := hij
  rw [coeff_thetaL, coeff_thetaL, ← hsum]
  push_cast
  ring

theorem thetaL_one : thetaL K (1 : LaurentSeries K) = 0 := by
  ext n
  rw [coeff_thetaL, coeff_one, coeff_zero]
  split_ifs with h
  · rw [h]; push_cast; ring
  · rw [mul_zero]

theorem thetaL_C (c : K) : thetaL K (HahnSeries.C c) = 0 := by
  ext n
  rw [coeff_thetaL, HahnSeries.C_apply, coeff_single, coeff_zero]
  split_ifs with h
  · rw [h]; push_cast; ring
  · rw [mul_zero]

theorem thetaL_mul' (f g : LaurentSeries K) :
    thetaL K (f * g) = f * thetaL K g + g * thetaL K f := by
  rw [thetaL_mul, mul_comm g]

theorem leibniz_pow_of_mul {A : Type*} [CommRing A] (D : A →+ A)
    (hD : ∀ a b, D (a * b) = a * D b + b * D a) (a : A) (n : ℕ) :
    D (a ^ n) = n * a ^ (n - 1) * D a := by
  induction n with
  | zero =>
      have h := hD 1 1
      rw [one_mul, one_mul] at h
      have h0 : D 1 = 0 := by
        have h' : D 1 + D 1 = D 1 + 0 := by rw [add_zero]; exact h.symm
        exact add_left_cancel h'
      rw [pow_zero, Nat.cast_zero, zero_mul, zero_mul, h0]
  | succ n ih =>
      rw [pow_succ, hD, ih, Nat.add_sub_cancel]
      rcases n with _ | n
      · simp
      · rw [Nat.add_sub_cancel]
        push_cast
        ring

theorem thetaL_pow (a : LaurentSeries K) (n : ℕ) :
    thetaL K (a ^ n) = n * a ^ (n - 1) * thetaL K a :=
  leibniz_pow_of_mul (thetaL K).toAddMonoidHom thetaL_mul' a n

theorem thetaL_single (n : ℤ) (a : K) : thetaL K (single n a) = single n ((n : K) * a) := by
  ext m
  rw [coeff_thetaL, coeff_single, coeff_single]
  split_ifs with h
  · rw [h]
  · rw [mul_zero]

theorem coeff_thetaL_iterate (k : ℕ) (f : LaurentSeries K) (n : ℤ) :
    ((thetaL K)^[k] f).coeff n = (n : K) ^ k * f.coeff n := by
  induction k generalizing f with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', coeff_thetaL, ih]; ring

variable (p : ℕ) [hp : Fact p.Prime]

variable (K) in

private noncomputable def _root_.CartierQExp.projP : LaurentSeries K →ₗ[K] LaurentSeries K := LinearMap.id - (thetaL K) ^ (p - 1)

p2m_export "CartierQExp" "projP"
theorem projP_apply (h : LaurentSeries K) : projP K p h = h - (thetaL K)^[p - 1] h := by
  rw [projP, LinearMap.sub_apply, LinearMap.id_apply, Module.End.pow_apply]

theorem coeff_projP (h : LaurentSeries K) (n : ℤ) :
    (projP K p h).coeff n = (1 - (n : K) ^ (p - 1)) * h.coeff n := by
  rw [projP_apply, coeff_sub, coeff_thetaL_iterate]; ring

variable [CharP K p]

theorem intCast_pow_p (n : ℤ) : ((n : K)) ^ p = n := by
  have h := map_intCast (frobenius K p) n
  rwa [frobenius_def] at h

theorem projP_thetaL (f : LaurentSeries K) : projP K p (thetaL K f) = 0 := by
  ext n
  rw [coeff_projP, coeff_thetaL, coeff_zero]
  have h1 : (1 - (n : K) ^ (p - 1)) * ((n : K) * f.coeff n)
      = ((n : K) - (n : K) ^ (p - 1 + 1)) * f.coeff n := by ring
  rw [h1, Nat.sub_add_cancel hp.out.one_lt.le, intCast_pow_p p, sub_self, zero_mul]

theorem coeff_projP_mul_p (h : LaurentSeries K) (n : ℤ) :
    (projP K p h).coeff (n * p) = h.coeff (n * p) := by
  rw [coeff_projP]
  have : (((n * p : ℤ)) : K) = 0 := by
    push_cast
    rw [CharP.cast_eq_zero K p, mul_zero]
  rw [this, zero_pow (Nat.sub_ne_zero_of_lt hp.out.one_lt), sub_zero, one_mul]

scoped instance charP_laurentSeries : CharP (LaurentSeries K) p :=
  charP_of_injective_algebraMap (algebraMap K (LaurentSeries K)).injective p

theorem thetaL_pow_p (c : LaurentSeries K) : thetaL K (c ^ p) = 0 := by
  rw [thetaL_pow, CharP.cast_eq_zero (LaurentSeries K) p, zero_mul, zero_mul]

theorem thetaL_pow_p_mul (c w : LaurentSeries K) :
    thetaL K (c ^ p * w) = c ^ p * thetaL K w := by
  rw [thetaL_mul, thetaL_pow_p, zero_mul, add_zero]

theorem thetaL_iterate_pow_p_mul (k : ℕ) (c w : LaurentSeries K) :
    (thetaL K)^[k] (c ^ p * w) = c ^ p * (thetaL K)^[k] w := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, thetaL_pow_p_mul, Function.iterate_succ_apply']

theorem projP_pow_p_mul (c w : LaurentSeries K) :
    projP K p (c ^ p * w) = c ^ p * projP K p w := by
  rw [projP_apply, projP_apply, thetaL_iterate_pow_p_mul, mul_sub]

theorem projP_pow_mul_thetaL (t : LaurentSeries K) (i : ℕ) (hi : ((i + 1 : ℕ) : K) ≠ 0) :
    projP K p (t ^ i * thetaL K t) = 0 := by
  have h := thetaL_pow t (i + 1)
  rw [Nat.add_sub_cancel, mul_assoc, ← nsmul_eq_mul] at h
  have h2 := projP_thetaL p (t ^ (i + 1))
  rw [h, map_nsmul, ← Nat.cast_smul_eq_nsmul K, smul_eq_zero] at h2
  exact h2.resolve_left hi

end CartierQExp
p2m_reactivate "P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_kw_cart_C_pow.CartierQExp"

namespace CartierQExp

open HahnSeries ModularCurve

variable {K : Type*} [Field K]

def VanishLT (x : LaurentSeries K) (M : ℤ) : Prop := ∀ m < M, x.coeff m = 0

theorem VanishLT.add {x y : LaurentSeries K} {M : ℤ} (hx : VanishLT x M) (hy : VanishLT y M) :
    VanishLT (x + y) M := fun m hm => by rw [coeff_add, hx m hm, hy m hm, add_zero]

theorem VanishLT.sub {x y : LaurentSeries K} {M : ℤ} (hx : VanishLT x M) (hy : VanishLT y M) :
    VanishLT (x - y) M := fun m hm => by rw [coeff_sub, hx m hm, hy m hm, sub_zero]

theorem VanishLT.mul {x y : LaurentSeries K} {A B : ℤ} (hx : VanishLT x A) (hy : VanishLT y B) :
    VanishLT (x * y) (A + B) := by
  intro m hm
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨-, -, hsum⟩ := hij
  by_cases h : ij.1 < A
  · rw [hx _ h, zero_mul]
  · have h2 : ij.2 < B := by omega
    rw [hy _ h2, mul_zero]

theorem VanishLT.one : VanishLT (1 : LaurentSeries K) 0 := fun m hm => by
  rw [coeff_one, if_neg hm.ne]

theorem VanishLT.pow {x : LaurentSeries K} {A : ℤ} (hx : VanishLT x A) (k : ℕ) :
    VanishLT (x ^ k) (k * A) := by
  induction k with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul]; exact VanishLT.one
  | succ k ih =>
      rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
      exact ih.mul hx

theorem VanishLT.thetaL {x : LaurentSeries K} {M : ℤ} (hx : VanishLT x M) :
    VanishLT (thetaL K x) M := fun m hm => by rw [coeff_thetaL, hx m hm, mul_zero]

theorem VanishLT.thetaL_iterate {x : LaurentSeries K} {M : ℤ} (hx : VanishLT x M) (k : ℕ) :
    VanishLT ((ModularCurve.thetaL K)^[k] x) M := fun m hm => by
  rw [coeff_thetaL_iterate, hx m hm, mul_zero]

theorem VanishLT.projP (p : ℕ) [Fact p.Prime] {x : LaurentSeries K} {M : ℤ} (hx : VanishLT x M) :
    VanishLT (projP K p x) M := fun m hm => by rw [coeff_projP, hx m hm, mul_zero]

theorem coeff_finsetSum_single (s : Finset ℤ) (c : ℤ → K) (n : ℤ) :
    (∑ k ∈ s, single k (c k)).coeff n = if n ∈ s then c n else 0 := by
  rw [coeff_sum]
  split_ifs with hn
  · rw [Finset.sum_eq_single n]
    · exact coeff_single_same n (c n)
    · intro k _ hk
      exact coeff_single_of_ne hk.symm
    · intro h
      exact absurd hn h
  · exact Finset.sum_eq_zero fun k hk => coeff_single_of_ne fun h => hn (h ▸ hk)

theorem exists_finset_add_vanishLT (x : LaurentSeries K) (M : ℤ) :
    ∃ (s : Finset ℤ) (c : ℤ → K) (r : LaurentSeries K),
      x = (∑ k ∈ s, single k (c k)) + r ∧ VanishLT r M := by
  have hfin : (x.support ∩ Set.Iio M).Finite := by
    have hwf : (x.support ∩ Set.Iio M).IsWF := x.isWF_support.mono Set.inter_subset_left
    by_cases hne : (x.support ∩ Set.Iio M).Nonempty
    · refine (Set.finite_Icc (hwf.min hne) M).subset ?_
      intro k hk
      exact ⟨hwf.min_le hne hk, le_of_lt hk.2⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      exact Set.finite_empty
  refine ⟨hfin.toFinset, x.coeff, x - ∑ k ∈ hfin.toFinset, single k (x.coeff k),
    (add_sub_cancel _ _).symm, ?_⟩
  intro m hm
  rw [coeff_sub, coeff_finsetSum_single]
  split_ifs with h
  · exact sub_self _
  · rw [sub_zero]
    by_contra hne
    exact h (hfin.mem_toFinset.mpr ⟨hne, hm⟩)

variable (p : ℕ) [hp : Fact p.Prime]

theorem nsmul_p_eq (k : ℤ) : p • k = k * p := by rw [nsmul_eq_mul, mul_comm]

variable [CharP K p]

theorem coeff_pow_p (g : LaurentSeries K) (n : ℤ) :
    (g ^ p).coeff (n * p) = (g.coeff n) ^ p := by
  obtain ⟨s, c, r, hx, hr⟩ := exists_finset_add_vanishLT g (n + 1)
  rw [hx, coeff_add, hr n (lt_add_one n), add_zero, add_pow_char, coeff_add,
    coeff_finsetSum_single]
  have hrp : (r ^ p).coeff (n * p) = 0 := by
    refine hr.pow p _ ?_
    have : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
    nlinarith
  rw [hrp, add_zero, sum_pow_char, coeff_sum]
  simp_rw [single_pow, nsmul_p_eq p]
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  split_ifs with hn
  · rw [Finset.sum_eq_single n]
    · exact coeff_single_same _ _
    · intro k _ hk
      exact coeff_single_of_ne fun h => hk (mul_right_cancel₀ hp0 h).symm
    · intro h
      exact absurd hn h
  · rw [zero_pow hp.out.ne_zero]
    exact Finset.sum_eq_zero fun k hk =>
      coeff_single_of_ne fun h => hn ((mul_right_cancel₀ hp0 h) ▸ hk)

end CartierQExp
p2m_reactivate "P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_kw_cart_C_pow.CartierQExp"

namespace CartierQExp

open HahnSeries ModularCurve

section DerivLemma

theorem choose_div_mul_eq {p : ℕ} (hp : p.Prime) {k : ℕ} (hk1 : 1 ≤ k) (hkp : k < p) :
    p.choose k / p * k = (p - 1).choose (k - 1) := by
  have hdvd : p ∣ p.choose k := hp.dvd_choose_self (by omega) hkp
  rw [Nat.div_mul_right_comm hdvd]
  have h := Nat.add_one_mul_choose_eq (p - 1) (k - 1)
  rw [Nat.sub_add_cancel hp.one_lt.le, Nat.sub_add_cancel hk1] at h
  rw [← h, Nat.mul_div_cancel_left _ hp.pos]

theorem choose_div_mul_sub_eq {p : ℕ} (hp : p.Prime) {k : ℕ} (hk1 : 1 ≤ k) (hkp : k < p) :
    p.choose k / p * (p - k) = (p - 1).choose k := by
  have hdvd : p ∣ p.choose k := hp.dvd_choose_self (by omega) hkp
  rw [Nat.div_mul_right_comm hdvd]
  have h := Nat.choose_mul_succ_eq (p - 1) k
  rw [Nat.sub_add_cancel hp.one_lt.le] at h
  rw [← h, Nat.mul_div_cancel _ hp.pos]

variable {A : Type*} [CommRing A]

def corrQ (p : ℕ) (x y : A) : A :=
  ∑ k ∈ Finset.range (p + 1), (p.choose k / p) • (x ^ k * y ^ (p - k))

theorem corrQ_sumA {p : ℕ} (hp : p.Prime) (x y : A) :
    ∑ k ∈ Finset.range (p + 1), ((p.choose k / p * k : ℕ) : A) * (x ^ (k - 1) * y ^ (p - k))
      = (x + y) ^ (p - 1) - x ^ (p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.one_lt.le).symm⟩
  have hq : 1 ≤ q := by have := hp.two_le; omega
  rw [Nat.add_sub_cancel, Finset.sum_range_succ', Finset.sum_range_succ, add_pow,
    Finset.sum_range_succ]
  have h0 : (((q + 1).choose 0 / (q + 1) * 0 : ℕ) : A) * (x ^ (0 - 1) * y ^ (q + 1 - 0)) = 0 := by
    rw [Nat.mul_zero, Nat.cast_zero, zero_mul]
  have htop : (((q + 1).choose (q + 1) / (q + 1) * (q + 1) : ℕ) : A)
      * (x ^ (q + 1 - 1) * y ^ (q + 1 - (q + 1))) = 0 := by
    rw [Nat.choose_self, Nat.div_eq_of_lt (by omega : 1 < q + 1), Nat.zero_mul, Nat.cast_zero,
      zero_mul]
  rw [h0, htop, add_zero, add_zero, Nat.choose_self, Nat.sub_self, Nat.cast_one, mul_one, pow_zero,
    mul_one, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [choose_div_mul_eq hp (by omega) (by omega)]
  have e3 : q + 1 - (j + 1) = q - j := by omega
  simp only [e3, Nat.add_sub_cancel]
  ring

theorem corrQ_sumB {p : ℕ} (hp : p.Prime) (x y : A) :
    ∑ k ∈ Finset.range (p + 1), ((p.choose k / p * (p - k) : ℕ) : A) * (x ^ k * y ^ (p - k - 1))
      = (x + y) ^ (p - 1) - y ^ (p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.one_lt.le).symm⟩
  have hq : 1 ≤ q := by have := hp.two_le; omega
  rw [Nat.add_sub_cancel, Finset.sum_range_succ, Finset.sum_range_succ', add_pow,
    Finset.sum_range_succ']
  have h0 : (((q + 1).choose 0 / (q + 1) * (q + 1 - 0) : ℕ) : A) * (x ^ 0 * y ^ (q + 1 - 0 - 1)) = 0 := by
    rw [Nat.choose_zero_right, Nat.div_eq_of_lt (by omega : 1 < q + 1), Nat.zero_mul, Nat.cast_zero,
      zero_mul]
  have htop : (((q + 1).choose (q + 1) / (q + 1) * (q + 1 - (q + 1)) : ℕ) : A)
      * (x ^ (q + 1) * y ^ (q + 1 - (q + 1) - 1)) = 0 := by
    rw [Nat.sub_self, Nat.mul_zero, Nat.cast_zero, zero_mul]
  rw [h0, htop, add_zero, add_zero, Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, mul_one,
    pow_zero, one_mul, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [choose_div_mul_sub_eq hp (by omega) (by omega)]
  have e1 : q + 1 - (j + 1) - 1 = q - (j + 1) := by omega
  simp only [e1, Nat.add_sub_cancel]
  ring

variable (D : A →+ A) (hD : ∀ a b, D (a * b) = a * D b + b * D a)
include hD

theorem deriv_corrQ {p : ℕ} (hp : p.Prime) (x y : A) :
    D (corrQ p x y)
      = (x + y) ^ (p - 1) * D (x + y) - x ^ (p - 1) * D x - y ^ (p - 1) * D y := by
  have key : D (corrQ p x y)
      = (∑ k ∈ Finset.range (p + 1), ((p.choose k / p * k : ℕ) : A) * (x ^ (k - 1) * y ^ (p - k))) * D x
        + (∑ k ∈ Finset.range (p + 1),
            ((p.choose k / p * (p - k) : ℕ) : A) * (x ^ k * y ^ (p - k - 1))) * D y := by
    rw [corrQ, map_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_nsmul, hD, leibniz_pow_of_mul D hD, leibniz_pow_of_mul D hD, nsmul_eq_mul]
    push_cast
    ring
  rw [key, corrQ_sumA hp, corrQ_sumB hp, map_add]
  ring

end DerivLemma
p2m_reactivate "P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_kw_cart_C_pow.CartierQExp"

variable {K : Type*} [Field K] (p : ℕ) [hp : Fact p.Prime] [CharP K p]

noncomputable def gam (x : LaurentSeries K) : LaurentSeries K :=
  projP K p (x ^ (p - 1) * thetaL K x) - thetaL K x ^ p

theorem gam_add (x y : LaurentSeries K) : gam p (x + y) = gam p x + gam p y := by
  have h := deriv_corrQ (thetaL K).toAddMonoidHom thetaL_mul' hp.out x y
  simp only [LinearMap.toAddMonoidHom_coe, map_add] at h
  have h2 : (x + y) ^ (p - 1) * thetaL K (x + y)
      = thetaL K (corrQ p x y) + x ^ (p - 1) * thetaL K x + y ^ (p - 1) * thetaL K y := by
    rw [map_add, h]; ring
  unfold gam
  rw [h2, map_add, map_add, projP_thetaL, zero_add, map_add, add_pow_char]
  ring

theorem projP_single_of_cast_eq_zero (m : ℤ) (hm : (m : K) = 0) (c : K) :
    projP K p (single m c) = single m c := by
  ext i
  rw [coeff_projP, coeff_single]
  split_ifs with h
  · rw [h, hm, zero_pow (Nat.sub_ne_zero_of_lt hp.out.one_lt), sub_zero, one_mul]
  · rw [mul_zero]

theorem gam_single (n : ℤ) (a : K) : gam p (single n a) = 0 := by
  unfold gam
  rw [thetaL_single, single_pow, single_mul_single, single_pow]
  have hidx : (p - 1) • n + n = p • n := by
    rw [nsmul_eq_mul, nsmul_eq_mul, Nat.cast_pred hp.out.pos]; ring
  have hcast : (((p • n : ℤ)) : K) = 0 := by
    rw [nsmul_eq_mul]; push_cast; rw [CharP.cast_eq_zero K p, zero_mul]
  have hcoef : a ^ (p - 1) * ((n : K) * a) = ((n : K) * a) ^ p := by
    rw [mul_pow, intCast_pow_p p n, mul_left_comm, ← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le]
  rw [hidx, hcoef, projP_single_of_cast_eq_zero p _ hcast, sub_self]

theorem gam_zero : gam p (0 : LaurentSeries K) = 0 := by
  unfold gam
  rw [map_zero, mul_zero, map_zero, zero_pow hp.out.ne_zero, sub_zero]

theorem gam_finsetSum (s : Finset ℤ) (c : ℤ → K) :
    gam p (∑ k ∈ s, single k (c k)) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, gam_zero]
  | insert k s hk ih => rw [Finset.sum_insert hk, gam_add, gam_single, ih, add_zero]

theorem gam_vanishLT {x : LaurentSeries K} {M : ℤ} (hx : VanishLT x M) :
    VanishLT (gam p x) (p * M) := by
  unfold gam
  have h1 : VanishLT (x ^ (p - 1) * thetaL K x) (p * M) := by
    have h := (hx.pow (p - 1)).mul hx.thetaL
    have e : (((p - 1 : ℕ)) : ℤ) * M + M = p * M := by rw [Nat.cast_pred hp.out.pos]; ring
    rwa [e] at h
  have h2 : VanishLT (thetaL K x ^ p) (p * M) := hx.thetaL.pow p
  exact (h1.projP p).sub h2

theorem gam_eq_zero (x : LaurentSeries K) : gam p x = 0 := by
  ext m
  rw [coeff_zero]
  obtain ⟨s, c, r, hx, hr⟩ := exists_finset_add_vanishLT x (m.toNat + 1)
  have hmM : m < (p : ℤ) * (m.toNat + 1) := by
    have h1 : m < (m.toNat : ℤ) + 1 := by have := Int.self_le_toNat m; omega
    have h2 : ((m.toNat : ℤ) + 1) ≤ (p : ℤ) * (m.toNat + 1) :=
      le_mul_of_one_le_left (by omega) (by exact_mod_cast hp.out.one_lt.le)
    omega
  rw [hx, gam_add, gam_finsetSum, zero_add]
  exact gam_vanishLT p hr m hmM

theorem projP_pow_pred_mul_thetaL (t : LaurentSeries K) :
    projP K p (t ^ (p - 1) * thetaL K t) = thetaL K t ^ p :=
  sub_eq_zero.mp (gam_eq_zero p t)

end CartierQExp
p2m_reactivate "P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_kw_cart_C_pow.CartierQExp"

namespace CartierQExp

open HahnSeries ModularCurve AlgebraicCurve.KwCart AlgebraicCurve.KwPke

variable {K : Type*} [Field K]

section QExp

variable (F : IntermediateField K (LaurentSeries K))

theorem algebraMap_laurent_apply (c : K) :
    algebraMap K (LaurentSeries K) c = HahnSeries.C c := by
  change HahnSeries.ofPowerSeries ℤ K (algebraMap K (PowerSeries K) c) = HahnSeries.C c
  rw [PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    HahnSeries.ofPowerSeries_C]

theorem algebra_smul_eq (c : K) (v : LaurentSeries K) :
    algebraMap K (LaurentSeries K) c * v = c • v := by
  rw [algebraMap_laurent_apply, HahnSeries.C_mul_eq_smul]

theorem thetaL_algebraMap (c : K) : thetaL K (algebraMap K (LaurentSeries K) c) = 0 := by
  rw [algebraMap_laurent_apply]
  exact thetaL_C c

scoped instance isScalarTower_intermediateField : IsScalarTower K F (LaurentSeries K) :=
  ⟨fun c x v => by
    rw [IntermediateField.smul_def, IntermediateField.smul_def, smul_eq_mul, smul_eq_mul,
      IntermediateField.coe_smul, Algebra.smul_def, mul_assoc, algebra_smul_eq]⟩

noncomputable def derF : Derivation K F (LaurentSeries K) where
  toFun x := thetaL K (x : LaurentSeries K)
  map_add' x y := by
    rw [IntermediateField.coe_add, map_add]
  map_smul' c x := by
    rw [RingHom.id_apply, IntermediateField.coe_smul, Algebra.smul_def, thetaL_mul,
      thetaL_algebraMap, zero_mul, add_zero, algebra_smul_eq]
  map_one_eq_zero' := by
    show thetaL K ((1 : F) : LaurentSeries K) = 0
    rw [OneMemClass.coe_one]
    exact thetaL_one
  leibniz' x y := by
    show thetaL K ((x * y : F) : LaurentSeries K)
      = x • thetaL K (y : LaurentSeries K) + y • thetaL K (x : LaurentSeries K)
    rw [IntermediateField.coe_mul, thetaL_mul, IntermediateField.smul_def,
      IntermediateField.smul_def, smul_eq_mul, smul_eq_mul, mul_comm (thetaL K (x : LaurentSeries K))]

theorem derF_apply (x : F) : derF F x = thetaL K (x : LaurentSeries K) := rfl

theorem exists_isQExpansionDiffAlong :
    ∃ φ, IsQExpansionDiffAlong F.val φ :=
  ⟨(derF F).liftKaehlerDifferential.restrictScalars K,
    fun x => by
      show (derF F).liftKaehlerDifferential (KaehlerDifferential.D K F x) = _
      rw [Derivation.liftKaehlerDifferential_comp_D]
      rfl,
    fun f ω => by
      have h := LinearMap.map_smul ((derF F).liftKaehlerDifferential) f ω
      rw [IntermediateField.smul_def, smul_eq_mul] at h
      exact h⟩

theorem isQExpansionDiffAlong_qExpansionDiffAlong :
    IsQExpansionDiffAlong F.val (qExpansionDiffAlong F.val) := by
  have h := exists_isQExpansionDiffAlong F
  have e : qExpansionDiffAlong F.val = h.choose := dif_pos h
  rw [e]
  exact h.choose_spec

theorem qExpansionDiffAlong_smul_D (u t : F) :
    qExpansionDiffAlong F.val (u • KaehlerDifferential.D K F t)
      = (u : LaurentSeries K) * thetaL K (t : LaurentSeries K) := by
  obtain ⟨h1, h2⟩ := isQExpansionDiffAlong_qExpansionDiffAlong F
  have h := h2 u (KaehlerDifferential.D K F t)
  have h1t := h1 t
  exact h.trans (congrArg (fun z => F.val u * z) h1t)

end QExp
p2m_reactivate "P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_kw_cart_C_pow.CartierQExp"

section Main

variable (p : ℕ) [hp : Fact p.Prime]

theorem charP_base (F : IntermediateField K (LaurentSeries K)) [CharP F p] : CharP K p :=
  (RingHom.charP_iff (algebraMap K F) (algebraMap K F).injective p).mpr inferInstance

theorem cast_succ_ne_zero [CharP K p] (i : ℕ) (hi : i + 1 < p) : ((i + 1 : ℕ) : K) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff K p] at h
  exact absurd (Nat.le_of_dvd (Nat.succ_pos i) h) (not_le.mpr hi)

theorem coeff_qExpansionDiffAlong_cart_C_pow
    (F : IntermediateField K (LaurentSeries K)) [CharP F p] (t : F)
    (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := p) t).toSubfield x)
    (hdeg : (minpoly (kw_pke_pthPowers F p) t).natDegree = p)
    (ω : Ω[F⁄K]) (n : ℤ) :
    (qExpansionDiffAlong F.val (kw_cart_C (K := K) t hdt hspan hsep hdeg ω)).coeff n ^ p
      = (qExpansionDiffAlong F.val ω).coeff (n * p) := by
  haveI : CharP K p := charP_base p F
  have hw := kw_cart_dtCoord_spec (K := K) t hdt hspan ω

  have hc := kw_cart_repr_spec t hsep hdeg (kw_cart_dtCoord t hdt hspan ω)
  have hlt : p - 1 < p := by have := hp.out.pos; omega
  have hroot : ∀ i : Fin p,
      ((kw_cart_root (kw_cart_repr t hsep hdeg (kw_cart_dtCoord t hdt hspan ω) i) : F) :
          LaurentSeries K) ^ p
        = (((kw_cart_repr t hsep hdeg (kw_cart_dtCoord t hdt hspan ω) i : F)) :
            LaurentSeries K) := by
    intro i
    rw [← IntermediateField.coe_pow, kw_cart_root_pow]

  have hL : qExpansionDiffAlong F.val (kw_cart_C (K := K) t hdt hspan hsep hdeg ω)
      = ((kw_cart_root (kw_cart_repr t hsep hdeg (kw_cart_dtCoord t hdt hspan ω)
            ⟨p - 1, hlt⟩) : F) : LaurentSeries K) * thetaL K (t : LaurentSeries K) :=
    qExpansionDiffAlong_smul_D F _ t
  have hR : qExpansionDiffAlong F.val ω
      = ((kw_cart_dtCoord t hdt hspan ω : F) : LaurentSeries K)
          * thetaL K (t : LaurentSeries K) := by
    conv_lhs => rw [hw]
    exact qExpansionDiffAlong_smul_D F _ t

  have key : projP K p (((kw_cart_dtCoord t hdt hspan ω : F) : LaurentSeries K)
        * thetaL K (t : LaurentSeries K))
      = ((kw_cart_root (kw_cart_repr t hsep hdeg (kw_cart_dtCoord t hdt hspan ω)
            ⟨p - 1, hlt⟩) : F) : LaurentSeries K) ^ p
          * thetaL K (t : LaurentSeries K) ^ p := by
    conv_lhs => rw [hc, IntermediateField.coe_sum, Finset.sum_mul]
    rw [map_sum]
    simp_rw [IntermediateField.coe_mul, IntermediateField.coe_pow]
    rw [Finset.sum_eq_single (⟨p - 1, hlt⟩ : Fin p)]
    · rw [← hroot, mul_assoc, projP_pow_p_mul, projP_pow_pred_mul_thetaL]
    · intro i _ hi
      rw [← hroot i, mul_assoc, projP_pow_p_mul, projP_pow_mul_thetaL p _ _ ?_, mul_zero]
      apply cast_succ_ne_zero p
      have h1 : (i : ℕ) < p := i.2
      have h2 : (i : ℕ) ≠ p - 1 := fun h => hi (Fin.ext h)
      omega
    · intro h
      exact absurd (Finset.mem_univ _) h
  have final : (((kw_cart_root (kw_cart_repr t hsep hdeg (kw_cart_dtCoord t hdt hspan ω)
            ⟨p - 1, hlt⟩) : F) : LaurentSeries K) * thetaL K (t : LaurentSeries K)).coeff n ^ p
      = (((kw_cart_dtCoord t hdt hspan ω : F) : LaurentSeries K)
          * thetaL K (t : LaurentSeries K)).coeff (n * p) := by
    rw [← coeff_pow_p p, mul_pow, ← key, coeff_projP_mul_p]
  exact ((congrArg (fun z => HahnSeries.coeff z n ^ p) hL).trans final).trans
    (congrArg (fun z => HahnSeries.coeff z (n * p)) hR).symm

end Main
p2m_reactivate "P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_kw_cart_C_pow.CartierQExp"

end CartierQExp
p2m_reactivate "P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_kw_cart_C_pow.CartierQExp"

open ModularCurve AlgebraicCurve.KwCart AlgebraicCurve.KwPke

theorem solution
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime]
    (F : IntermediateField K (LaurentSeries K)) [CharP F p] (t : F)
    (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := p) t).toSubfield x)
    (hdeg : (minpoly (kw_pke_pthPowers F p) t).natDegree = p)
    (ω : Ω[F⁄K]) (n : ℤ) :
    (qExpansionDiffAlong F.val (kw_cart_C (K := K) t hdt hspan hsep hdeg ω)).coeff n ^ p
      = (qExpansionDiffAlong F.val ω).coeff (n * p) :=
  CartierQExp.coeff_qExpansionDiffAlong_cart_C_pow p F t hdt hspan hsep hdeg ω n

end S_ModularCurve_coeff_qExpansionDiffAlong_kw_cart_C_pow
end P2MW
export P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_kw_cart_C_pow (solution)
