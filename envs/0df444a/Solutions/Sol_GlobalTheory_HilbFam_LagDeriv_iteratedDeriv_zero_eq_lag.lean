-- Prove2me | solution 1 for GlobalTheory.HilbFam.LagDeriv.iteratedDeriv_zero_eq_lag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:30:29.932797+00:00
-- url     : https://prove2.me/submissions/1da1bb22-6a20-496f-af7f-2a10dd8994c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivZeroEqLaguerreDerivativePolynomialV
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


section
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace GlobalTheory.HilbFam.LagDeriv
set_option autoImplicit false in
open Filter Topology in
private lemma hasDerivAt_inv_pow_mul_exp_div_one_add_mul (c y : ℂ) (j : ℕ) {z : ℂ} (hz : 1 + z * c ≠ 0) :
    HasDerivAt (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ j * Complex.exp (y * w / (1 + w * c)))
      (-(j * c) * ((1 + z * c)⁻¹ ^ (j + 1) * Complex.exp (y * z / (1 + z * c))) +
        y * ((1 + z * c)⁻¹ ^ (j + 2) * Complex.exp (y * z / (1 + z * c)))) z := by
  have hu : HasDerivAt (fun w : ℂ ↦ 1 + w * c) c z := by
    simpa using ((hasDerivAt_id z).mul_const c).const_add 1
  have hinv : HasDerivAt (fun w : ℂ ↦ (1 + w * c)⁻¹) (-c / (1 + z * c) ^ 2) z := hu.inv hz
  have hpow : HasDerivAt (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ j)
      (j * (1 + z * c)⁻¹ ^ (j - 1) * (-c / (1 + z * c) ^ 2)) z := hinv.pow j
  have hq : HasDerivAt (fun w : ℂ ↦ y * w / (1 + w * c)) (y / (1 + z * c) ^ 2) z := by
    refine (((hasDerivAt_id z).const_mul y).div hu hz).congr_deriv ?_
    simp only [id, mul_one]
    field_simp
    ring
  refine (hpow.mul hq.cexp).congr_deriv ?_
  rcases j with _ | j
  · simp [div_eq_mul_inv]
    ring
  · simp only [Nat.cast_succ, Nat.add_sub_cancel, inv_pow]
    field_simp
    ring
set_option autoImplicit false in
open Filter Topology in
private lemma rco_eq_zero_of_lt (k n m : ℕ) (hm : n < m) :
    _root_.GlobalTheory.HilbFam.rco k n m = 0 := by
  unfold _root_.GlobalTheory.HilbFam.rco
  simp [Nat.choose_eq_zero_of_lt hm]
set_option autoImplicit false in
open Filter Topology in
private lemma ascFactorial_succ_eq_mul_succ_ascFactorial (a e : ℕ) :
    a.ascFactorial (e + 1) = a * (a + 1).ascFactorial e := by
  induction e with
  | zero => simp [Nat.ascFactorial_succ]
  | succ e ih =>
    rw [Nat.ascFactorial_succ, ih, Nat.ascFactorial_succ]
    ring
set_option autoImplicit false in
open Filter Topology in
private lemma rco_succ_succ (k n m : ℕ) (hm : m ≤ n) :
    (_root_.GlobalTheory.HilbFam.rco k (n + 1) (m + 1) : ℤ) =
      -((k + n + m + 1 : ℕ) : ℤ) * _root_.GlobalTheory.HilbFam.rco k n (m + 1) +
        _root_.GlobalTheory.HilbFam.rco k n m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  unfold _root_.GlobalTheory.HilbFam.rco
  rcases d with _ | e
  · simp
  · have h1 : m + (e + 1) + 1 - (m + 1) = e + 1 := by omega
    have h2 : m + (e + 1) - (m + 1) = e := by omega
    have h3 : m + (e + 1) - m = e + 1 := by omega
    rw [h1, h2, h3]
    have hc := Nat.choose_succ_right_eq (m + (e + 1)) m
    have hc' : m + (e + 1) - m = e + 1 := by omega
    rw [hc'] at hc
    have hs : (m + (e + 1) + 1).choose (m + 1) = (m + (e + 1)).choose m + (m + (e + 1)).choose (m + 1) :=
      Nat.choose_succ_succ' _ _
    have ha1 : (k + (m + 1)).ascFactorial (e + 1) = (k + (m + 1) + e) * (k + (m + 1)).ascFactorial e :=
      Nat.ascFactorial_succ
    have ha2 := ascFactorial_succ_eq_mul_succ_ascFactorial (k + m) e
    rw [hs, ha1, ha2]
    have hkm : k + m + 1 = k + (m + 1) := by omega
    rw [hkm]
    push_cast
    have hcz : ((m + (e + 1)).choose (m + 1) : ℤ) * (m + 1) = ((m + (e + 1)).choose m : ℤ) * (e + 1) := by
      exact_mod_cast hc
    rw [pow_succ]
    linear_combination ((-1 : ℤ) ^ e * ((k + (m + 1)).ascFactorial e : ℤ)) * hcz
set_option autoImplicit false in
open Filter Topology in
private lemma rco_mul_pow_mul_pow_succ_succ (k n m : ℕ) (hm : m ≤ n) (c y : ℂ) :
    (_root_.GlobalTheory.HilbFam.rco k (n + 1) (m + 1) : ℂ) * c ^ (n + 1 - (m + 1)) * y ^ (m + 1) =
      -(((k + n + (m + 1) : ℕ) : ℂ) * c) *
          ((_root_.GlobalTheory.HilbFam.rco k n (m + 1) : ℂ) * c ^ (n - (m + 1)) * y ^ (m + 1)) +
        y * ((_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) * y ^ m) := by
  have hZ := congrArg (Int.cast : ℤ → ℂ) (rco_succ_succ k n m hm)
  push_cast at hZ
  rw [hZ]
  rcases hm.lt_or_eq with hlt | rfl
  · obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have e1 : m + t + 1 + 1 - (m + 1) = t + 1 := by omega
    have e2 : m + t + 1 - (m + 1) = t := by omega
    have e3 : m + t + 1 - m = t + 1 := by omega
    rw [e1, e2, e3]
    push_cast
    ring
  · rw [rco_eq_zero_of_lt k m (m + 1) (Nat.lt_succ_self m)]
    simp only [Nat.sub_self, pow_zero]
    push_cast
    ring
set_option autoImplicit false in
open Filter Topology in
private lemma rco_succ_zero (k n : ℕ) :
    (_root_.GlobalTheory.HilbFam.rco k (n + 1) 0 : ℤ) =
      -((k + n : ℕ) : ℤ) * _root_.GlobalTheory.HilbFam.rco k n 0 := by
  unfold _root_.GlobalTheory.HilbFam.rco
  simp only [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, add_zero, Nat.ascFactorial_succ]
  push_cast
  ring
set_option autoImplicit false in
open Filter Topology in
private lemma rco_mul_pow_mul_pow_succ_zero (k n : ℕ) (c y : ℂ) :
    (_root_.GlobalTheory.HilbFam.rco k (n + 1) 0 : ℂ) * c ^ (n + 1 - 0) * y ^ 0 =
      -(((k + n + 0 : ℕ) : ℂ) * c) *
        ((_root_.GlobalTheory.HilbFam.rco k n 0 : ℂ) * c ^ (n - 0) * y ^ 0) := by
  have hZ := congrArg (Int.cast : ℤ → ℂ) (rco_succ_zero k n)
  push_cast at hZ
  rw [hZ]
  simp only [Nat.sub_zero, pow_zero, add_zero]
  push_cast
  ring
set_option autoImplicit false in
open Filter Topology in
private lemma iteratedDeriv_inv_pow_mul_exp_eq_sum_rco (c y : ℂ) (n : ℕ) :
    ∀ k : ℕ, ∀ z : ℂ, 1 + z * c ≠ 0 →
      iteratedDeriv n (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ k * Complex.exp (y * w / (1 + w * c))) z =
        ∑ m ∈ Finset.range (n + 1), (_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) *
          y ^ m * ((1 + z * c)⁻¹ ^ (k + n + m) * Complex.exp (y * z / (1 + z * c))) := by
  induction n with
  | zero =>
    intro k z _
    simp [_root_.GlobalTheory.HilbFam.rco]
  | succ n ih =>
    intro k z hz
    have hopen : IsOpen {w : ℂ | 1 + w * c ≠ 0} :=
      isOpen_ne_fun (by fun_prop) continuous_const
    have hev : iteratedDeriv n (fun w : ℂ ↦ (1 + w * c)⁻¹ ^ k * Complex.exp (y * w / (1 + w * c))) =ᶠ[𝓝 z]
        fun w ↦ ∑ m ∈ Finset.range (n + 1), (_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) *
          y ^ m * ((1 + w * c)⁻¹ ^ (k + n + m) * Complex.exp (y * w / (1 + w * c))) :=
      Filter.eventually_of_mem (hopen.mem_nhds hz) fun w hw ↦ ih k w hw
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hd := HasDerivAt.fun_sum (u := Finset.range (n + 1)) (fun m _ ↦
      (hasDerivAt_inv_pow_mul_exp_div_one_add_mul c y (k + n + m) hz).const_mul
        ((_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) * y ^ m))
    rw [hd.deriv]
    set H : ℕ → ℂ := fun j ↦ (1 + z * c)⁻¹ ^ j * Complex.exp (y * z / (1 + z * c)) with hH
    set C : ℕ → ℕ → ℂ := fun n m ↦
      (_root_.GlobalTheory.HilbFam.rco k n m : ℂ) * c ^ (n - m) * y ^ m with hC
    change ∑ m ∈ Finset.range (n + 1), C n m * (-(((k + n + m : ℕ) : ℂ) * c) * H (k + n + m + 1) +
        y * H (k + n + m + 2)) = ∑ m ∈ Finset.range (n + 1 + 1), C (n + 1) m * H (k + (n + 1) + m)
    have hA : ∑ m ∈ Finset.range (n + 1 + 1), -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1) =
        ∑ m ∈ Finset.range (n + 1), -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1) := by
      rw [Finset.sum_range_succ]
      simp [hC, rco_eq_zero_of_lt k n (n + 1) (Nat.lt_succ_self n)]
    have hT : ∀ m ∈ Finset.range (n + 1), C (n + 1) (m + 1) * H (k + (n + 1) + (m + 1)) =
        -(((k + n + (m + 1) : ℕ) : ℂ) * c) * C n (m + 1) * H (k + n + (m + 1) + 1) +
          C n m * (y * H (k + n + m + 2)) := by
      intro m hm
      have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      simp only [hC]
      rw [rco_mul_pow_mul_pow_succ_succ k n m hmn c y]
      have e1 : k + (n + 1) + (m + 1) = k + n + (m + 1) + 1 := by omega
      have e2 : k + n + m + 2 = k + n + (m + 1) + 1 := by omega
      rw [e1, e2]
      ring
    have h0 : C (n + 1) 0 * H (k + (n + 1) + 0) = -(((k + n + 0 : ℕ) : ℂ) * c) * C n 0 * H (k + n + 0 + 1) := by
      simp only [hC]
      rw [rco_mul_pow_mul_pow_succ_zero k n c y]
      have e1 : k + (n + 1) + 0 = k + n + 0 + 1 := by omega
      rw [e1]
    have hS : ∑ m ∈ Finset.range (n + 1), -(((k + n + (m + 1) : ℕ) : ℂ) * c) * C n (m + 1) *
          H (k + n + (m + 1) + 1) + -(((k + n + 0 : ℕ) : ℂ) * c) * C n 0 * H (k + n + 0 + 1) =
        ∑ m ∈ Finset.range (n + 1), -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1) := by
      rw [← Finset.sum_range_succ' (fun m ↦ -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1))]
      exact hA
    have hB : ∑ m ∈ Finset.range (n + 1), C n m * (-(((k + n + m : ℕ) : ℂ) * c) * H (k + n + m + 1)) =
        ∑ m ∈ Finset.range (n + 1), -(((k + n + m : ℕ) : ℂ) * c) * C n m * H (k + n + m + 1) :=
      Finset.sum_congr rfl fun m _ ↦ by ring
    conv_rhs => rw [Finset.sum_range_succ', Finset.sum_congr rfl hT, Finset.sum_add_distrib, h0]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hB, ← hS]
    ring
end GlobalTheory.HilbFam.LagDeriv
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.HilbFam GlobalTheory.HilbFam.LagDeriv
set_option autoImplicit false
open Filter Topology
namespace GlobalTheory.HilbFam.LagDeriv
namespace _root_.GlobalTheory.HilbFam.LagDeriv
theorem _root_.solution : ∀ (k n : ℕ) (c y : ℂ),
    iteratedDeriv n (fun z : ℂ ↦ (1 + z * c)⁻¹ ^ k * Complex.exp (y * z / (1 + z * c))) 0 =
      _root_.GlobalTheory.HilbFam.lag k n c y := by
  intro k n c y
  rw [iteratedDeriv_inv_pow_mul_exp_eq_sum_rco c y n k 0 (by simp)]
  unfold _root_.GlobalTheory.HilbFam.lag
  simp
end _root_.GlobalTheory.HilbFam.LagDeriv
end GlobalTheory.HilbFam.LagDeriv
