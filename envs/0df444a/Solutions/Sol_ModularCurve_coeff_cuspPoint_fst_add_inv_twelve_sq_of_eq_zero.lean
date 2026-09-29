-- Prove2me | solution 1 for ModularCurve.coeff_cuspPoint_fst_add_inv_twelve_sq_of_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/0d2a87dd-bee2-5bef-9898-eebc3f68e2ce

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_sub_one_mul_coeff_tateUnivX_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq_of_eq_zero
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

open ModularCurve Finset

noncomputable section

namespace X4TOR

abbrev ep (i k : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 k

@[scoped simp] theorem ep_zero (i k : ℕ) : ep i k 0 = i := by simp [ep, Finsupp.add_apply, Finsupp.single_apply]
@[scoped simp] theorem ep_one (i k : ℕ) : ep i k 1 = k := by simp [ep, Finsupp.add_apply, Finsupp.single_apply]

theorem ep_eq (e : Fin 2 →₀ ℕ) : ep (e 0) (e 1) = e := by
  ext s; fin_cases s <;> simp

theorem ep_add (i k i' k' : ℕ) : ep i k + ep i' k' = ep (i + i') (k + k') := by
  ext s; fin_cases s <;> simp [Finsupp.add_apply]

theorem ep_injective {i k i' k' : ℕ} (h : ep i k = ep i' k') : i = i' ∧ k = k' := by
  have h0 := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
  have h1 := congrArg (fun e : Fin 2 →₀ ℕ => e 1) h
  simp at h0 h1
  exact ⟨h0, h1⟩

def Xc (i k : ℕ) : ℤ := MvPowerSeries.coeff (ep i k) tateUnivX

theorem Xc_eq (i k : ℕ) : Xc i k =
    if i = k then -2 * ∑ d ∈ k.divisors, (d : ℤ)
    else if k < i then (if i - k ∣ k then ((i - k : ℕ) : ℤ) else 0)
    else (if k - i ∣ k then ((k - i : ℕ) : ℤ) else 0) := coeff_tateUnivX i k

theorem Xc_eq_zero_of_lt {i k : ℕ} (hk : 0 < k) (h : 2 * k < i) : Xc i k = 0 := by
  rw [Xc_eq, if_neg (by omega), if_pos (by omega), if_neg]
  intro hd
  have := Nat.le_of_dvd hk hd
  omega

theorem Xc_zero_right (i : ℕ) : Xc i 0 = i := by
  rw [Xc_eq]
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h; simp
  · rw [if_neg (by omega), if_pos h, if_pos (dvd_zero _), Nat.sub_zero]

theorem coeff_mul_ep (f g : MvPowerSeries (Fin 2) ℤ) (i k : ℕ) :
    MvPowerSeries.coeff (ep i k) (f * g) =
      ∑ i₁ ∈ range (i + 1), ∑ k₁ ∈ range (k + 1),
        MvPowerSeries.coeff (ep i₁ k₁) f * MvPowerSeries.coeff (ep (i - i₁) (k - k₁)) g := by
  classical
  rw [MvPowerSeries.coeff_mul, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun p => (p.1 0, p.1 1)) (fun q => (ep q.1 q.2, ep (i - q.1) (k - q.2))) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h0 := congrArg (fun e : Fin 2 →₀ ℕ => e 0) hp
    have h1 := congrArg (fun e : Fin 2 →₀ ℕ => e 1) hp
    simp [ep, Finsupp.single_apply] at h0 h1
    simp only [Finset.mem_product, Finset.mem_range]
    omega
  · intro q hq
    simp only [Finset.mem_product, Finset.mem_range] at hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal, ep_add]
    congr 1 <;> omega
  · intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h0 := congrArg (fun e : Fin 2 →₀ ℕ => e 0) hp
    have h1 := congrArg (fun e : Fin 2 →₀ ℕ => e 1) hp
    simp [ep, Finsupp.single_apply] at h0 h1
    ext
    · simp only; rw [ep_eq]
    · simp only
      rw [show i - p.1 0 = p.2 0 by omega, show k - p.1 1 = p.2 1 by omega, ep_eq]
  · intro q hq
    simp
  · intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h0 := congrArg (fun e : Fin 2 →₀ ℕ => e 0) hp
    have h1 := congrArg (fun e : Fin 2 →₀ ℕ => e 1) hp
    simp [ep, Finsupp.single_apply] at h0 h1
    simp only
    rw [ep_eq, show i - p.1 0 = p.2 0 by omega, show k - p.1 1 = p.2 1 by omega, ep_eq]

end X4TOR
p2m_reactivate "P2MW.S_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq_of_eq_zero.X4TOR"

namespace X4TOR

def P (k i : ℕ) : ℤ := ∑ j ∈ range (i + 1), Xc j k

def G (k i : ℕ) : ℤ := ∑ j ∈ range (i + 1), ((i - j : ℕ) : ℤ) * Xc j k

def H (k i : ℕ) : ℤ := ∑ k₁ ∈ Ico 1 k, ∑ i₁ ∈ range (i + 1), Xc i₁ k₁ * Xc (i - i₁) (k - k₁)

theorem G_zero (k : ℕ) : G k 0 = 0 := by simp [G]

theorem G_succ (k i : ℕ) : G k (i + 1) = G k i + P k i := by
  rw [G, G, P, Finset.sum_range_succ, Nat.sub_self, Nat.cast_zero, zero_mul, add_zero, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  rw [show i + 1 - j = (i - j) + 1 by omega]; push_cast; ring

theorem P_succ (k i : ℕ) : P k (i + 1) = P k i + Xc (i + 1) k := by
  rw [P, P, Finset.sum_range_succ]

theorem G_delta (k M : ℕ) : G k (M + 2) - 2 * G k (M + 1) + G k M = Xc (M + 1) k := by
  rw [show M + 2 = (M + 1) + 1 by rfl, G_succ, G_succ, P_succ]; ring

theorem coeff_sq (k : ℕ) (hk : 1 ≤ k) (i : ℕ) :
    MvPowerSeries.coeff (ep i k) (tateUnivX ^ 2) = 2 * G k i + H k i := by
  rw [sq, coeff_mul_ep]
  rw [Finset.sum_comm]

  have hsplit : range (k + 1) = insert 0 (insert k (Ico 1 k)) := by
    ext x; simp [Finset.mem_Ico]; omega
  rw [hsplit, Finset.sum_insert (by simp [Finset.mem_Ico]; omega), Finset.sum_insert (by simp [Finset.mem_Ico])]
  have h0 : ∑ i₁ ∈ range (i + 1), MvPowerSeries.coeff (ep i₁ 0) tateUnivX * MvPowerSeries.coeff (ep (i - i₁) (k - 0)) tateUnivX
      = G k i := by
    rw [Nat.sub_zero, G]
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    show Xc (i + 1 - 1 - j) 0 * Xc (i - (i + 1 - 1 - j)) k = _
    rw [Xc_zero_right, show i + 1 - 1 - j = i - j by omega, show i - (i - j) = j by omega]
  have hk' : ∑ i₁ ∈ range (i + 1), MvPowerSeries.coeff (ep i₁ k) tateUnivX * MvPowerSeries.coeff (ep (i - i₁) (k - k)) tateUnivX
      = G k i := by
    rw [Nat.sub_self, G]
    refine Finset.sum_congr rfl fun j hj => ?_
    show Xc j k * Xc (i - j) 0 = _
    rw [Xc_zero_right, mul_comm]
  rw [h0, hk', H]
  have hmid : ∑ k₁ ∈ Ico 1 k, ∑ i₁ ∈ range (i + 1),
      MvPowerSeries.coeff (ep i₁ k₁) tateUnivX * MvPowerSeries.coeff (ep (i - i₁) (k - k₁)) tateUnivX =
      ∑ k₁ ∈ Ico 1 k, ∑ i₁ ∈ range (i + 1), Xc i₁ k₁ * Xc (i - i₁) (k - k₁) := rfl
  rw [hmid]; ring

theorem coeff_A4 (i k : ℕ) : MvPowerSeries.coeff (ep i k) tateUnivA4 = if i = k then PowerSeries.coeff k tateA4 else 0 := by
  rw [tateUnivA4_apply, ep_zero, ep_one]
  split_ifs with h
  · rw [h]
  · rfl

theorem E (k : ℕ) (hk : 1 ≤ k) (i : ℕ) :
    (((i : ℤ) - k) ^ 2 - 1) * Xc i k = 12 * G k i + 6 * H k i + 2 * (if i = k then PowerSeries.coeff k tateA4 else 0) := by
  have h := ModularCurve.sub_one_mul_coeff_tateUnivX_eq i k
  rw [coeff_sq k hk i, coeff_A4] at h
  rw [Xc]; linear_combination h

theorem H_eq_zero (k i : ℕ) (hi : 2 * k < i) : H k i = 0 := by
  refine Finset.sum_eq_zero fun k₁ hk₁ => Finset.sum_eq_zero fun i₁ hi₁ => ?_
  rw [Finset.mem_Ico] at hk₁
  rw [Finset.mem_range] at hi₁
  by_cases h1 : 2 * k₁ < i₁
  · rw [Xc_eq_zero_of_lt (by omega) h1, zero_mul]
  · rw [Xc_eq_zero_of_lt (k := k - k₁) (by omega) (by omega), mul_zero]

theorem G_eq_zero (k : ℕ) (hk : 1 ≤ k) (i : ℕ) (hi : 2 * k + 1 < i) : G k i = 0 := by
  have h := E k hk i
  rw [Xc_eq_zero_of_lt (by omega) (by omega), H_eq_zero k i (by omega), if_neg (by omega)] at h
  linarith

end X4TOR
p2m_reactivate "P2MW.S_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq_of_eq_zero.X4TOR"

namespace X4TOR

variable {K : Type*} [CommRing K]

theorem G_sum_identity (k : ℕ) (c : K) (M : ℕ) :
    (1 - c) ^ 2 * ∑ i ∈ range (M + 1), c ^ i * (G k i : K) =
      c * ∑ i ∈ range (M + 1), c ^ i * (Xc i k : K) - c ^ (M + 1) * ((G k (M + 1) : K) - c * (G k M : K)) := by
  induction M with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, pow_one, G_zero, Int.cast_zero, mul_zero]
    rw [show G k 1 = Xc 0 k by rw [show (1 : ℕ) = 0 + 1 by rfl, G_succ, G_zero, P]; simp]
    ring
  | succ M ih =>
    rw [Finset.sum_range_succ (fun i => c ^ i * (G k i : K)), Finset.sum_range_succ (fun i => c ^ i * (Xc i k : K)),
      mul_add, ih]
    have hd := G_delta k M
    have hd' : ((G k (M + 2) : ℤ) : K) = 2 * (G k (M + 1) : K) - (G k M : K) + (Xc (M + 1) k : K) := by
      rw [show G k (M + 2) = 2 * G k (M + 1) - G k M + Xc (M + 1) k by linarith]; push_cast; ring
    rw [show M + 1 + 1 = M + 2 by rfl, hd']
    ring

theorem G_sum_eq (k : ℕ) (hk : 1 ≤ k) (c : K) (M : ℕ) (hM : 2 * k + 2 ≤ M) :
    (1 - c) ^ 2 * ∑ i ∈ range (M + 1), c ^ i * (G k i : K) = c * ∑ i ∈ range (M + 1), c ^ i * (Xc i k : K) := by
  rw [G_sum_identity, G_eq_zero k hk (M + 1) (by omega), G_eq_zero k hk M (by omega)]
  simp

theorem E_sum (k : ℕ) (hk : 1 ≤ k) (c : K) (M : ℕ) (hM : k ≤ M) :
    ∑ i ∈ range (M + 1), c ^ i * (((((i : ℤ) - k) ^ 2 - 1) * Xc i k : ℤ) : K) =
      12 * ∑ i ∈ range (M + 1), c ^ i * (G k i : K) + 6 * ∑ i ∈ range (M + 1), c ^ i * (H k i : K) +
        2 * c ^ k * ((PowerSeries.coeff k tateA4 : ℤ) : K) := by
  have hA : ∑ i ∈ range (M + 1), c ^ i * (((if i = k then PowerSeries.coeff k tateA4 else 0 : ℤ)) : K) =
      c ^ k * ((PowerSeries.coeff k tateA4 : ℤ) : K) := by
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr (by omega))]
    · rw [if_pos rfl]
    · intro i _ hi; rw [if_neg hi, Int.cast_zero, mul_zero]
  rw [Finset.mul_sum, Finset.mul_sum, mul_assoc (2 : K), ← hA, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [E k hk i]; push_cast; ring

theorem eval_identity (k : ℕ) (hk : 1 ≤ k) (c : K) (M : ℕ) (hM : 2 * k + 2 ≤ M) :
    (1 - c) ^ 2 * (∑ i ∈ range (M + 1), c ^ i * (((((i : ℤ) - k) ^ 2 - 1) * Xc i k : ℤ) : K) -
        6 * ∑ i ∈ range (M + 1), c ^ i * (H k i : K) - 2 * c ^ k * ((PowerSeries.coeff k tateA4 : ℤ) : K)) =
      12 * c * ∑ i ∈ range (M + 1), c ^ i * (Xc i k : K) := by
  rw [E_sum k hk c M (by omega)]
  have := G_sum_eq k hk c M hM
  linear_combination (12 : K) * this

end X4TOR
p2m_reactivate "P2MW.S_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq_of_eq_zero.X4TOR"

namespace X4TOR

variable {K : Type*} [Field K]

theorem col_eval (φ : ℤ → K) (k : ℕ) (hk : 1 ≤ k) (c : K) (hc : c ≠ 0) (M : ℕ) (hM : 2 * k ≤ M) :
    ∑ i ∈ range (M + 1), c ^ i * (φ ((i : ℤ) - k) * (Xc i k : K)) =
      c ^ k * (φ 0 * (-2 * ∑ d ∈ k.divisors, (d : K)) +
        ∑ d ∈ k.divisors, (d : K) * (φ d * c ^ d + φ (-(d : ℤ)) * c⁻¹ ^ d)) := by
  classical

  have hkmem : k ∈ range (M + 1) := Finset.mem_range.mpr (by omega)
  rw [← Finset.add_sum_erase _ _ hkmem]
  have hdiag : c ^ k * (φ ((k : ℤ) - k) * (Xc k k : K)) = c ^ k * (φ 0 * (-2 * ∑ d ∈ k.divisors, (d : K))) := by
    rw [sub_self, Xc_eq, if_pos rfl]; push_cast; ring
  rw [hdiag, mul_add, add_right_inj]
  rw [← Finset.sum_filter_add_sum_filter_not ((range (M + 1)).erase k) (fun i => k < i)]

  have habove : ∑ i ∈ ((range (M + 1)).erase k).filter (fun i => k < i), c ^ i * (φ ((i : ℤ) - k) * (Xc i k : K)) =
      ∑ d ∈ k.divisors, c ^ k * ((d : K) * (φ d * c ^ d)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (((range (M + 1)).erase k).filter (fun i => k < i)) (fun i => i - k ∣ k)]
    have hz : ∑ i ∈ (((range (M + 1)).erase k).filter (fun i => k < i)).filter (fun i => ¬ (i - k ∣ k)),
        c ^ i * (φ ((i : ℤ) - k) * (Xc i k : K)) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range] at hi
      rw [Xc_eq, if_neg (by omega), if_pos hi.1.2, if_neg hi.2]; simp
    rw [hz, add_zero]
    refine Finset.sum_nbij' (fun i => i - k) (fun d => k + d) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range] at hi
      exact Nat.mem_divisors.mpr ⟨hi.2, by omega⟩
    · intro d hd
      have hd' := Nat.mem_divisors.mp hd
      have hdk : d ≤ k := Nat.divisor_le hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range]
      refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, by rw [Nat.add_sub_cancel_left]; exact hd'.1⟩
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range] at hi
      show k + (i - k) = i; omega
    · intro d hd; show k + d - k = d; omega
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range] at hi
      obtain ⟨⟨⟨hik, hiM⟩, hlt⟩, hdvd⟩ := hi
      rw [Xc_eq, if_neg (by omega), if_pos hlt, if_pos hdvd]
      have : ((i : ℤ) - k) = ((i - k : ℕ) : ℤ) := by omega
      rw [this, show c ^ i = c ^ k * c ^ (i - k) by rw [← pow_add]; congr 1; omega]
      push_cast; ring

  have hbelow : ∑ i ∈ ((range (M + 1)).erase k).filter (fun i => ¬ k < i), c ^ i * (φ ((i : ℤ) - k) * (Xc i k : K)) =
      ∑ d ∈ k.divisors, c ^ k * ((d : K) * (φ (-(d : ℤ)) * c⁻¹ ^ d)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (((range (M + 1)).erase k).filter (fun i => ¬ k < i)) (fun i => k - i ∣ k)]
    have hz : ∑ i ∈ (((range (M + 1)).erase k).filter (fun i => ¬ k < i)).filter (fun i => ¬ (k - i ∣ k)),
        c ^ i * (φ ((i : ℤ) - k) * (Xc i k : K)) = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range] at hi
      rw [Xc_eq, if_neg (by omega), if_neg hi.1.2, if_neg hi.2]; simp
    rw [hz, add_zero]
    refine Finset.sum_nbij' (fun i => k - i) (fun d => k - d) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range] at hi
      exact Nat.mem_divisors.mpr ⟨hi.2, by omega⟩
    · intro d hd
      have hd' := Nat.mem_divisors.mp hd
      have hdk : d ≤ k := Nat.divisor_le hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range]
      refine ⟨⟨⟨by omega, by omega⟩, by omega⟩, by rw [Nat.sub_sub_self hdk]; exact hd'.1⟩
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range] at hi
      show k - (k - i) = i; omega
    · intro d hd
      have hdk : d ≤ k := Nat.divisor_le hd
      show k - (k - d) = d; omega
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range] at hi
      obtain ⟨⟨⟨hik, hiM⟩, hlt⟩, hdvd⟩ := hi
      rw [Xc_eq, if_neg (by omega), if_neg hlt, if_pos hdvd]
      have hle : i ≤ k := by omega
      have : ((i : ℤ) - k) = -((k - i : ℕ) : ℤ) := by omega
      rw [this, show c ^ i = c ^ k * c⁻¹ ^ (k - i) by
        rw [inv_pow, show c ^ k = c ^ i * c ^ (k - i) by rw [← pow_add]; congr 1; omega, mul_assoc,
          mul_inv_cancel₀ (pow_ne_zero _ hc), mul_one]]
      push_cast; ring
  rw [habove, hbelow, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => by ring

end X4TOR
p2m_reactivate "P2MW.S_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq_of_eq_zero.X4TOR"

namespace X4TOR

variable {K : Type*} [Field K]

theorem cauchy_trunc (A B : ℕ → K) (a b M : ℕ) (hA : ∀ i, a < i → A i = 0) (hB : ∀ i, b < i → B i = 0)
    (h : a + b ≤ M) (c : K) :
    ∑ i ∈ range (M + 1), c ^ i * ∑ i₁ ∈ range (i + 1), A i₁ * B (i - i₁) =
      (∑ i ∈ range (M + 1), c ^ i * A i) * (∑ i ∈ range (M + 1), c ^ i * B i) := by
  classical
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_sigma']

  rw [← Finset.sum_filter_add_sum_filter_not (range (M + 1) ×ˢ range (M + 1)) (fun p => p.1 + p.2 ≤ M)]
  have hz : ∑ p ∈ (range (M + 1) ×ˢ range (M + 1)).filter (fun p => ¬ p.1 + p.2 ≤ M),
      c ^ p.1 * A p.1 * (c ^ p.2 * B p.2) = 0 := by
    refine Finset.sum_eq_zero fun p hp => ?_
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    by_cases h1 : a < p.1
    · rw [hA _ h1]; ring
    · rw [hB _ (by omega)]; ring
  rw [hz, add_zero]
  refine Finset.sum_nbij' (fun s => (s.2, s.1 - s.2)) (fun p => ⟨p.1 + p.2, p.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    simp only [Finset.mem_sigma, Finset.mem_range] at hs
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    simp only [Finset.mem_sigma, Finset.mem_range]
    omega
  · intro s hs
    simp only [Finset.mem_sigma, Finset.mem_range] at hs
    ext <;> simp <;> omega
  · intro p hp
    simp
  · intro s hs
    simp only [Finset.mem_sigma, Finset.mem_range] at hs
    simp only
    rw [show c ^ s.1 = c ^ s.2 * c ^ (s.1 - s.2) by rw [← pow_add]; congr 1; omega]
    ring

theorem H_eval (k : ℕ) (hk : 1 ≤ k) (c : K) (M : ℕ) (hM : 2 * k ≤ M) :
    ∑ i ∈ range (M + 1), c ^ i * (H k i : K) =
      ∑ k₁ ∈ Ico 1 k, (∑ i ∈ range (M + 1), c ^ i * (Xc i k₁ : K)) * (∑ i ∈ range (M + 1), c ^ i * (Xc i (k - k₁) : K)) := by
  have : ∀ i, (H k i : K) = ∑ k₁ ∈ Ico 1 k, ∑ i₁ ∈ range (i + 1), (Xc i₁ k₁ : K) * (Xc (i - i₁) (k - k₁) : K) := by
    intro i; rw [H]; push_cast; rfl
  simp_rw [this, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k₁ hk₁ => ?_
  rw [Finset.mem_Ico] at hk₁
  simp_rw [← Finset.mul_sum]
  exact cauchy_trunc (fun i => (Xc i k₁ : K)) (fun i => (Xc i (k - k₁) : K)) (2 * k₁) (2 * (k - k₁)) M
    (fun i hi => by show (Xc i k₁ : K) = 0; rw [Xc_eq_zero_of_lt (by omega) hi, Int.cast_zero])
    (fun i hi => by show (Xc i (k - k₁) : K) = 0; rw [Xc_eq_zero_of_lt (by omega) hi, Int.cast_zero]) (by omega) c

end X4TOR
p2m_reactivate "P2MW.S_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq_of_eq_zero.X4TOR"

namespace X4TOR

variable {K : Type*} [Field K]

def T (N : ℕ) (c ci : K) (m : ℕ) : K :=
  if m = 0 then 0 else
    (∑ d ∈ m.divisors, if N ∣ d then ((m / d : ℕ) : K) * (c ^ (m / d) + ci ^ (m / d)) else 0)
      - 2 * (if N ∣ m then ∑ e ∈ (m / N).divisors, (e : K) else 0)

theorem T_of_not_dvd (N : ℕ) (c ci : K) (m : ℕ) (hm : ¬ N ∣ m) : T N c ci m = 0 := by
  rw [T]
  by_cases h0 : m = 0
  · rw [if_pos h0]
  · rw [if_neg h0, if_neg hm, mul_zero, sub_zero]
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [if_neg]
    intro hNd
    exact hm (hNd.trans (Nat.dvd_of_mem_divisors hd))

theorem T_mul (N : ℕ) [NeZero N] (c ci : K) (k : ℕ) (hk : 1 ≤ k) :
    T N c ci (N * k) = (∑ e ∈ k.divisors, (e : K) * (c ^ e + ci ^ e)) - 2 * ∑ e ∈ k.divisors, (e : K) := by
  have hN : 0 < N := NeZero.pos N
  rw [T, if_neg (by positivity), if_pos (dvd_mul_right N k), Nat.mul_div_cancel_left k hN]
  congr 1

  rw [← Finset.sum_filter, ← Nat.sum_div_divisors k (fun e => (e : K) * (c ^ e + ci ^ e))]
  refine Finset.sum_nbij' (fun d => d / N) (fun d' => N * d') ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hd1, hne⟩, ⟨t, rfl⟩⟩ := hd
    rw [Nat.mem_divisors, Nat.mul_div_cancel_left t hN]
    exact ⟨Nat.dvd_of_mul_dvd_mul_left hN hd1, by omega⟩
  · intro d' hd'
    rw [Nat.mem_divisors] at hd'
    simp only [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨Nat.mul_dvd_mul_left N hd'.1, by positivity⟩, dvd_mul_right N d'⟩
  · intro d hd
    simp only [Finset.mem_filter] at hd
    obtain ⟨-, ⟨t, rfl⟩⟩ := hd
    show N * (N * t / N) = N * t
    rw [Nat.mul_div_cancel_left t hN]
  · intro d' hd'; show N * d' / N = d'; rw [Nat.mul_div_cancel_left d' hN]
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hd1, hne⟩, ⟨t, rfl⟩⟩ := hd
    rw [Nat.mul_div_cancel_left t hN, Nat.mul_div_mul_left _ _ hN]

theorem coeff_sq_ofPowerSeries (g : ℕ → K) (n : ℕ) :
    ((HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk g)) ^ 2).coeff (n : ℤ) =
      ∑ i ∈ range (n + 1), g i * g (n - i) := by
  rw [← map_pow, HahnSeries.ofPowerSeries_apply_coeff, sq, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j => PowerSeries.coeff i (PowerSeries.mk g) * PowerSeries.coeff j (PowerSeries.mk g)]
  simp only [PowerSeries.coeff_mk]

theorem sum_sq_of_not_dvd (N : ℕ) (g : ℕ → K) (hg : ∀ m, ¬ N ∣ m → g m = 0) (n : ℕ) (hn : ¬ N ∣ n) :
    ∑ i ∈ range (n + 1), g i * g (n - i) = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mem_range] at hi
  by_cases h : N ∣ i
  · rw [hg (n - i) (fun h' => hn ?_), mul_zero]
    have := Nat.dvd_add h h'
    rwa [Nat.add_sub_cancel' (by omega)] at this
  · rw [hg i h, zero_mul]

theorem sum_sq_mul (N : ℕ) [NeZero N] (g : ℕ → K) (hg : ∀ m, ¬ N ∣ m → g m = 0) (k : ℕ) :
    ∑ i ∈ range (N * k + 1), g i * g (N * k - i) = ∑ j ∈ range (k + 1), g (N * j) * g (N * (k - j)) := by
  classical
  have hN : 0 < N := NeZero.pos N
  rw [← Finset.sum_filter_add_sum_filter_not (range (N * k + 1)) (fun i => N ∣ i)]
  have hz : ∑ i ∈ (range (N * k + 1)).filter (fun i => ¬ N ∣ i), g i * g (N * k - i) = 0 :=
    Finset.sum_eq_zero fun i hi => by rw [hg i (Finset.mem_filter.mp hi).2, zero_mul]
  rw [hz, add_zero]
  refine Finset.sum_nbij' (fun i => i / N) (fun j => N * j) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    rw [Finset.mem_range]
    obtain ⟨t, rfl⟩ := hi.2
    rw [Nat.mul_div_cancel_left t hN]; nlinarith
  · intro j hj
    rw [Finset.mem_range] at hj
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by nlinarith, dvd_mul_right N j⟩
  · intro i hi
    simp only [Finset.mem_filter] at hi
    obtain ⟨t, rfl⟩ := hi.2
    show N * (N * t / N) = N * t; rw [Nat.mul_div_cancel_left t hN]
  · intro j hj; show N * j / N = j; exact Nat.mul_div_cancel_left j hN
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨t, rfl⟩ := hi.2
    rw [Nat.mul_div_cancel_left t hN, ← Nat.mul_sub N k t]

end X4TOR
p2m_reactivate "P2MW.S_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq_of_eq_zero.X4TOR"

namespace X4TOR

variable {K : Type*} [Field K]

theorem rhs_eq (N : ℕ) [NeZero N] (c ci : K) (n : ℕ) (hn : 1 ≤ n) :
    ∑ md ∈ n.divisorsAntidiagonal, ((md.2 : ℕ) : K) ^ 3 *
        ((if N ∣ md.1 then c ^ md.2 else 0) + (if N ∣ md.1 then ci ^ md.2 else 0)) =
      if N ∣ n then ∑ d ∈ (n / N).divisors, ((d : ℕ) : K) ^ 3 * (c ^ d + ci ^ d) else 0 := by
  classical
  have hN : 0 < N := NeZero.pos N
  rw [Nat.sum_divisorsAntidiagonal' (fun m d => ((d : ℕ) : K) ^ 3 * ((if N ∣ m then c ^ d else 0) + (if N ∣ m then ci ^ d else 0)))]
  have hterm : ∀ d ∈ n.divisors, ((d : ℕ) : K) ^ 3 * ((if N ∣ n / d then c ^ d else 0) + (if N ∣ n / d then ci ^ d else 0)) =
      if N ∣ n / d then ((d : ℕ) : K) ^ 3 * (c ^ d + ci ^ d) else 0 := by
    intro d _; split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm]
  split_ifs with hNn
  · obtain ⟨k, rfl⟩ := hNn
    rw [Nat.mul_div_cancel_left k hN]
    have hk : k ≠ 0 := by rintro rfl; simp at hn
    symm
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨m, hm⟩, -⟩
      refine ⟨⟨Dvd.intro (N * m) (by rw [hm]; ring), by positivity⟩, ?_⟩
      rw [hm, show N * (d * m) = d * (N * m) by ring, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (by rintro rfl; simp at hm; omega))]
      exact dvd_mul_right N m
    · rintro ⟨⟨hd, -⟩, hNd⟩
      refine ⟨?_, hk⟩
      obtain ⟨m, hm⟩ := hNd
      have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hd; omega)
      have := Nat.div_mul_cancel hd
      rw [hm] at this
      exact Dvd.intro m (Nat.eq_of_mul_eq_mul_left hN (by linarith [this]))
  · refine Finset.sum_eq_zero fun d hd => ?_
    rw [if_neg]
    intro h
    exact hNn (h.trans (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)))

def τ (c : K) (j : ℕ) : K := (∑ e ∈ j.divisors, (e : K) * (c ^ e + c⁻¹ ^ e)) - 2 * ∑ e ∈ j.divisors, (e : K)

theorem toric_core [CharZero K] (c : K) (hc : c ≠ 0) (hc1 : c ≠ 1) (k : ℕ) (hk : 1 ≤ k) :
    2 * (c * (1 - c)⁻¹ ^ 2 + 12⁻¹) * τ c k + ∑ j ∈ Ico 1 k, τ c j * τ c (k - j) =
      6⁻¹ * ∑ e ∈ k.divisors, (e : K) ^ 3 * (c ^ e + c⁻¹ ^ e) + (240 / 144 : K) * ∑ e ∈ k.divisors, (e : K) ^ 3 := by
  set M := 2 * k + 2 with hM

  have hcol : ∀ j, 1 ≤ j → j ≤ k → ∑ i ∈ range (M + 1), c ^ i * (Xc i j : K) = c ^ j * τ c j := by
    intro j hj hjk
    have := col_eval (fun _ => (1 : K)) j hj c hc M (by omega)
    simp only [one_mul] at this
    rw [this, τ]; ring
  have hcolw : ∑ i ∈ range (M + 1), c ^ i * (((((i : ℤ) - k) ^ 2 - 1) * Xc i k : ℤ) : K) =
      c ^ k * ((∑ e ∈ k.divisors, (e : K) ^ 3 * (c ^ e + c⁻¹ ^ e)) - τ c k) := by
    have := col_eval (fun z => ((z : K)) ^ 2 - 1) k hk c hc M (by omega)
    rw [Finset.sum_congr rfl (fun i _ => by push_cast; rfl)] at this ⊢
    rw [this, τ]
    simp only [Int.cast_zero, Int.cast_neg, Int.cast_natCast]
    have hs : ∑ d ∈ k.divisors, (d : K) * ((((d : K)) ^ 2 - 1) * c ^ d + ((-(d : K)) ^ 2 - 1) * c⁻¹ ^ d) =
        ∑ d ∈ k.divisors, (d : K) ^ 3 * (c ^ d + c⁻¹ ^ d) - ∑ d ∈ k.divisors, (d : K) * (c ^ d + c⁻¹ ^ d) := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun d _ => by ring)
    rw [hs]; ring
  have hH' : ∑ i ∈ range (M + 1), c ^ i * (H k i : K) = c ^ k * ∑ j ∈ Ico 1 k, τ c j * τ c (k - j) := by
    rw [H_eval k hk c M (by omega), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    rw [hcol j hj.1 (by omega), hcol (k - j) (by omega) (by omega),
      show c ^ k = c ^ j * c ^ (k - j) by rw [← pow_add]; congr 1; omega]
    ring
  have hE := eval_identity k hk c M (le_refl _)
  rw [hcolw, hH', hcol k hk le_rfl] at hE
  have hA : ((PowerSeries.coeff k tateA4 : ℤ) : K) = -5 * ∑ e ∈ k.divisors, (e : K) ^ 3 := by
    rw [coeff_tateA4]; push_cast
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have hck : c ^ k ≠ 0 := pow_ne_zero _ hc
  have key : (1 - c) ^ 2 * (((∑ e ∈ k.divisors, (e : K) ^ 3 * (c ^ e + c⁻¹ ^ e)) - τ c k) -
      6 * (∑ j ∈ Ico 1 k, τ c j * τ c (k - j)) - 2 * ((PowerSeries.coeff k tateA4 : ℤ) : K)) = 12 * c * τ c k := by
    apply mul_left_cancel₀ hck
    linear_combination hE
  have h1c : (1 - c) ≠ 0 := sub_ne_zero.mpr (Ne.symm hc1)
  have hu : (1 - c) * (1 - c)⁻¹ = 1 := mul_inv_cancel₀ h1c
  apply mul_left_cancel₀ (pow_ne_zero 2 h1c)
  linear_combination (-(1 / 6 : K)) * key + (2 * c * τ c k * ((1 - c) * (1 - c)⁻¹ + 1)) * hu + (-(1 - c) ^ 2 / 3) * hA

end X4TOR
p2m_reactivate "P2MW.S_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq_of_eq_zero.X4TOR"

namespace X4TOR

theorem toric_lhs (L : Type) [Field L] [CharZero L] (N : ℕ) [NeZero N] (ξ : Lˣ) (hξ : IsPrimitiveRoot (ξ : L) N)
    (v : Fin 2 → ZMod N) (hv : v ≠ 0) (hv1 : v 1 = 0) (n : ℕ) (hn : 1 ≤ n) :
    (((ModularCurve.cuspPoint L N ξ v).1 + HahnSeries.C ((12 : L)⁻¹)) ^ 2).coeff (n : ℤ) =
      (6 : L)⁻¹ * (if N ∣ n then ∑ d ∈ (n / N).divisors,
          ((d : ℕ) : L) ^ 3 * (((ξ ^ (v 0).val : Lˣ) : L) ^ d + (((ξ ^ (v 0).val : Lˣ) : L))⁻¹ ^ d) else 0) +
        (if N ∣ n then (240 / 144 : L) * ∑ d ∈ (n / N).divisors, ((d : ℕ) : L) ^ 3 else 0) := by
  classical
  have hN : 0 < N := NeZero.pos N
  have hv0 : v 0 ≠ 0 := by
    intro h0; apply hv; funext i; fin_cases i
    · exact h0
    · exact hv1
  set cu : Lˣ := ξ ^ (v 0).val with hcu
  set c : L := (cu : L) with hc
  have hcval : c = (ξ : L) ^ (v 0).val := by rw [hc, hcu, Units.val_pow_eq_pow_val]
  have hc0 : c ≠ 0 := by rw [hc]; exact cu.ne_zero
  have hc1 : c ≠ 1 := by
    rw [hcval, Ne, hξ.pow_eq_one_iff_dvd]
    intro hdvd
    have hlt : (v 0).val < N := ZMod.val_lt _
    have hne : (v 0).val ≠ 0 := fun h => hv0 ((ZMod.val_eq_zero _).mp h)
    exact hne (Nat.eq_zero_of_dvd_of_lt hdvd hlt)
  have hci : (((cu)⁻¹ : Lˣ) : L) = c⁻¹ := by rw [Units.val_inv_eq_inv_val]

  set g : ℕ → L := fun m => T N c c⁻¹ m + (if m = 0 then c * (1 - c)⁻¹ ^ 2 + 12⁻¹ else 0) with hg
  have hpt : (ModularCurve.cuspPoint L N ξ v).1 + HahnSeries.C ((12 : L)⁻¹) =
      HahnSeries.ofPowerSeries ℤ L (PowerSeries.mk g) := by
    rw [ModularCurve.cuspPoint_of_eq_zero ξ hv1, ModularCurve.tateToricPoint_fst, ← HahnSeries.ofPowerSeries_C, ← map_add]
    congr 1
    ext m
    rw [map_add, PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_C]
    simp only [← hcu, hci, Ring.inverse_eq_inv, hg, T]
    rw [← hc]
    by_cases hm : m = 0
    · simp only [hm, if_true]; ring
    · simp only [hm, if_false]
  have hgN : ∀ m, ¬ N ∣ m → g m = 0 := by
    intro m hm
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero N)
    simp only [hg, T_of_not_dvd N c c⁻¹ m hm, if_neg hm0, add_zero]
  rw [hpt, coeff_sq_ofPowerSeries]
  by_cases hNn : N ∣ n
  · obtain ⟨k, rfl⟩ := hNn
    have hk : 1 ≤ k := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    rw [if_pos (dvd_mul_right N k), if_pos (dvd_mul_right N k), Nat.mul_div_cancel_left k hN,
      sum_sq_mul N g hgN k]

    have hsplit : range (k + 1) = insert 0 (insert k (Ico 1 k)) := by
      ext x; simp [Finset.mem_Ico]; omega
    rw [hsplit, Finset.sum_insert (by simp [Finset.mem_Ico]; omega), Finset.sum_insert (by simp [Finset.mem_Ico])]
    have hg0 : g (N * 0) = c * (1 - c)⁻¹ ^ 2 + 12⁻¹ := by
      simp only [hg, mul_zero, T, if_true]; ring
    have hgk : ∀ j, 1 ≤ j → g (N * j) = τ c j := by
      intro j hj
      have hj0 : N * j ≠ 0 := by positivity
      simp only [hg, if_neg hj0, add_zero, T_mul N c c⁻¹ j hj, τ]
    have hmid : ∑ j ∈ Ico 1 k, g (N * j) * g (N * (k - j)) = ∑ j ∈ Ico 1 k, τ c j * τ c (k - j) :=
      Finset.sum_congr rfl fun j hj => by
        rw [Finset.mem_Ico] at hj
        rw [hgk j hj.1, hgk (k - j) (by omega)]
    rw [Nat.sub_zero, Nat.sub_self, hg0, hgk k hk, hmid]
    have := toric_core c hc0 hc1 k hk
    linear_combination this
  · rw [if_neg hNn, if_neg hNn, sum_sq_of_not_dvd N g hgN n hNn]; ring

end X4TOR
p2m_reactivate "P2MW.S_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq_of_eq_zero.X4TOR"

end
p2m_reactivate "P2MW.S_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq_of_eq_zero.X4TOR"

namespace X4TOR

theorem toric_rhs (L : Type) [Field L] (N : ℕ) [NeZero N] (ξ : Lˣ) (v : Fin 2 → ZMod N) (hv1 : v 1 = 0)
    (n : ℕ) (hn : 1 ≤ n) :
    (6 : L)⁻¹ * ∑ md ∈ Nat.divisorsAntidiagonal n,
          ((md.2 : ℕ) : L) ^ 3 *
            ((if ((md.1 : ℕ) : ZMod N) = v 1 then ((ξ ^ (md.2 * (v 0).val) : Lˣ) : L) else 0) +
              (if ((md.1 : ℕ) : ZMod N) = -v 1 then ((ξ⁻¹ ^ (md.2 * (v 0).val) : Lˣ) : L) else 0)) +
        (if N ∣ n then (240 / 144 : L) * ((Nat.divisors (n / N)).sum fun d => ((d : ℕ) : L) ^ 3) else 0) =
      (6 : L)⁻¹ * (if N ∣ n then ∑ d ∈ (n / N).divisors,
          ((d : ℕ) : L) ^ 3 * (((ξ ^ (v 0).val : Lˣ) : L) ^ d + (((ξ ^ (v 0).val : Lˣ) : L))⁻¹ ^ d) else 0) +
        (if N ∣ n then (240 / 144 : L) * ∑ d ∈ (n / N).divisors, ((d : ℕ) : L) ^ 3 else 0) := by
  rw [← rhs_eq N (((ξ ^ (v 0).val : Lˣ) : L)) ((((ξ ^ (v 0).val : Lˣ) : L))⁻¹) n hn]
  congr 2
  refine Finset.sum_congr rfl fun md _ => ?_
  congr 1
  have e1 : (((md.1 : ℕ) : ZMod N) = v 1) ↔ (N ∣ md.1) := by
    rw [hv1, ZMod.natCast_eq_zero_iff]
  have e2 : (((md.1 : ℕ) : ZMod N) = -v 1) ↔ (N ∣ md.1) := by
    rw [hv1, neg_zero, ZMod.natCast_eq_zero_iff]
  have v1eq : ((ξ ^ (md.2 * (v 0).val) : Lˣ) : L) = ((ξ ^ (v 0).val : Lˣ) : L) ^ md.2 := by
    rw [← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm]
  have v2eq : ((ξ⁻¹ ^ (md.2 * (v 0).val) : Lˣ) : L) = (((ξ ^ (v 0).val : Lˣ) : L))⁻¹ ^ md.2 := by
    rw [← Units.val_inv_eq_inv_val, ← Units.val_pow_eq_pow_val, ← inv_pow, ← pow_mul, mul_comm, inv_pow]
  rw [v1eq, v2eq]
  exact congrArg₂ (· + ·) (if_congr e1 rfl rfl) (if_congr e2 rfl rfl)

end X4TOR
p2m_reactivate "P2MW.S_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq_of_eq_zero.X4TOR"

theorem solution
    (L : Type) [Field L] [CharZero L] (N : ℕ) [NeZero N] (ξ : Lˣ) (hξ : IsPrimitiveRoot (ξ : L) N)
    (v : Fin 2 → ZMod N) (hv : v ≠ 0) (hv1 : v 1 = 0) (n : ℕ) (hn : 1 ≤ n) :
    (((ModularCurve.cuspPoint L N ξ v).1 + HahnSeries.C ((12 : L)⁻¹)) ^ 2).coeff (n : ℤ) =
      (6 : L)⁻¹ * ∑ md ∈ Nat.divisorsAntidiagonal n,
          ((md.2 : ℕ) : L) ^ 3 *
            ((if ((md.1 : ℕ) : ZMod N) = v 1 then ((ξ ^ (md.2 * (v 0).val) : Lˣ) : L) else 0) +
              (if ((md.1 : ℕ) : ZMod N) = -v 1 then ((ξ⁻¹ ^ (md.2 * (v 0).val) : Lˣ) : L) else 0)) +
        (if N ∣ n then (240 / 144 : L) * ((Nat.divisors (n / N)).sum fun d => ((d : ℕ) : L) ^ 3) else 0) := by
  exact (X4TOR.toric_lhs L N ξ hξ v hv hv1 n hn).trans (X4TOR.toric_rhs L N ξ v hv1 n hn).symm

end S_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq_of_eq_zero
end P2MW
export P2MW.S_ModularCurve_coeff_cuspPoint_fst_add_inv_twelve_sq_of_eq_zero (solution)
