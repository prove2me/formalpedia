-- Prove2me | solution 1 for ModularCurve.SiegelUnit.exists_peaked_exponent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/89a4e89e-db8e-5928-9e3b-1566d1fe5ff6

import Mathlib
import Theorems.Thm_ModularCurve_SiegelUnit_mem_span_levelBernoulliWeight_dilate_iff_even
import Theorems.Thm_ModularCurve_SiegelUnit_sum_levelBernoulliWeight_add_mul
import Theorems.Thm_ModularCurve_SiegelUnit_sum_totient_mul_levelBernoulliWeight_dilate_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SiegelUnit_exists_peaked_exponent

set_option autoImplicit false

namespace Peak

def W (N v : ℕ) : ℤ := 6 * (v : ℤ) ^ 2 - 6 * (N : ℤ) * (v : ℤ) + (N : ℤ) ^ 2

theorem W_zero (N : ℕ) : W N 0 = (N : ℤ) ^ 2 := by simp [W]

theorem W_le_sq {N v : ℕ} (hv : v ≤ N) : W N v ≤ (N : ℤ) ^ 2 := by
  have : (v : ℤ) ≤ N := by exact_mod_cast hv
  have h0 : (0 : ℤ) ≤ v := by exact_mod_cast Nat.zero_le v
  simp only [W]
  nlinarith

theorem neg_sq_le_W (N v : ℕ) : -(N : ℤ) ^ 2 ≤ W N v := by
  simp only [W]
  nlinarith [sq_nonneg (2 * (v : ℤ) - N)]

theorem W_one_sub (N v : ℕ) : W N 1 - W N v = 6 * ((v : ℤ) - 1) * ((N : ℤ) - 1 - v) := by
  simp only [W]; push_cast; ring

section sums

variable {N : ℕ} [NeZero N]

theorem sum_W_val : ∑ u : ZMod N, W N u.val = N := by
  have h := ModularCurve.SiegelUnit.sum_levelBernoulliWeight_add_mul N 0 1
  simp only [Int.cast_zero, Int.cast_one, zero_add, mul_one] at h
  have hg : Int.gcd 1 (N : ℤ) = 1 := by simp
  rw [hg] at h
  simp only [Nat.cast_one, Int.emod_one, mul_zero, zero_mul, sub_zero, one_pow, zero_add, mul_one,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  simpa [W] using h

theorem sum_sum_W_linear (x y a b : ZMod N) (hab : a * x + b * y = 1) :
    ∑ r : ZMod N, ∑ s : ZMod N, W N (r * x + s * y).val = (N : ℤ) ^ 2 := by
  set F : ZMod N → ℤ := fun u => ∑ r : ZMod N, ∑ s : ZMod N, W N (r * x + s * y + u).val with hF
  have hshift : ∀ u, F u = F 0 := by
    intro u
    simp only [hF]

    have e1 : ∑ r : ZMod N, ∑ s : ZMod N, W N ((r + u * a) * x + (s + u * b) * y + 0).val =
        ∑ r : ZMod N, ∑ s : ZMod N, W N (r * x + s * y + 0).val := by
      rw [Fintype.sum_equiv (Equiv.addRight (u * a))
        (fun r => ∑ s : ZMod N, W N ((r + u * a) * x + (s + u * b) * y + 0).val)
        (fun r => ∑ s : ZMod N, W N (r * x + (s + u * b) * y + 0).val) (fun r => rfl)]
      refine Finset.sum_congr rfl fun r _ => ?_
      exact Fintype.sum_equiv (Equiv.addRight (u * b))
        (fun s => W N (r * x + (s + u * b) * y + 0).val) (fun s => W N (r * x + s * y + 0).val) (fun s => rfl)
    rw [← e1]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    congr 2
    linear_combination (-u) * hab
  have havg : ∑ u : ZMod N, F u = (N : ℤ) * F 0 := by
    rw [Finset.sum_congr rfl fun u _ => hshift u, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul]
  have havg' : ∑ u : ZMod N, F u = (N : ℤ) ^ 2 * N := by
    simp only [hF]
    rw [Finset.sum_comm]
    have inner : ∀ r : ZMod N, ∑ u : ZMod N, ∑ s : ZMod N, W N (r * x + s * y + u).val = (N : ℤ) * N := by
      intro r
      rw [Finset.sum_comm]
      have : ∀ s : ZMod N, ∑ u : ZMod N, W N (r * x + s * y + u).val = N := by
        intro s
        rw [Fintype.sum_equiv (Equiv.addLeft (r * x + s * y)) (fun u => W N (r * x + s * y + u).val)
          (fun u => W N u.val) (fun u => rfl)]
        exact sum_W_val
      rw [Finset.sum_congr rfl fun s _ => this s, Finset.sum_const, Finset.card_univ, ZMod.card,
        nsmul_eq_mul]
    rw [Finset.sum_congr rfl fun r _ => inner r, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul]
    ring
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have : (N : ℤ) * F 0 = (N : ℤ) * (N : ℤ) ^ 2 := by rw [← havg, havg']; ring
  have hF0 := mul_left_cancel₀ hN this
  simpa [hF] using hF0

theorem sum_W_add_mul_le (x y : ZMod N) : ∑ s : ZMod N, W N (x + s * y).val ≤ (N : ℤ) ^ 3 := by
  have h := ModularCurve.SiegelUnit.sum_levelBernoulliWeight_add_mul N (x.val : ℤ) (y.val : ℤ)
  have hx : ((x.val : ℤ) : ZMod N) = x := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hy : ((y.val : ℤ) : ZMod N) = y := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [hx, hy] at h
  have hW : ∑ s : ZMod N, W N (x + s * y).val = ∑ s : ZMod N,
      (6 * ((((x + s * y).val : ℕ)) : ℤ) ^ 2 - 6 * (N : ℤ) * ((((x + s * y).val : ℕ)) : ℤ) + (N : ℤ) ^ 2) := by
    rfl
  rw [hW, h]
  set g : ℕ := Int.gcd (y.val : ℤ) N with hg
  set u : ℤ := (x.val : ℤ) % (g : ℤ) with hu
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hgpos : 0 < g := by
    rw [hg, Int.gcd_natCast_natCast]; exact Nat.gcd_pos_of_pos_right _ hNpos
  have hgle : g ≤ N := by
    rw [hg, Int.gcd_natCast_natCast]; exact Nat.gcd_le_right _ hNpos
  have hu0 : 0 ≤ u := Int.emod_nonneg _ (by exact_mod_cast hgpos.ne')
  have hug : u < g := Int.emod_lt_of_pos _ (by exact_mod_cast hgpos)
  have hgN : (g : ℤ) ≤ N := by exact_mod_cast hgle
  have hN0 : (0 : ℤ) ≤ N := by exact_mod_cast Nat.zero_le N
  nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hug.le), mul_nonneg hN0 (mul_nonneg hu0 (sub_nonneg.mpr hug.le)),
    mul_le_mul_of_nonneg_left (mul_le_mul hgN hgN (by exact_mod_cast Nat.zero_le g) hN0) hN0]

end sums

end Peak

namespace Peak

section construction

variable {N : ℕ} [NeZero N]

def wt (N : ℕ) (r : ZMod N) : ℕ := (N / Nat.gcd r.val N) * Nat.totient (Nat.gcd r.val N)

theorem wt_pos (r : ZMod N) : 0 < wt N r := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hg : 0 < Nat.gcd r.val N := Nat.gcd_pos_of_pos_right _ hNpos
  refine Nat.mul_pos (Nat.div_pos (Nat.gcd_le_right _ hNpos) hg) (Nat.totient_pos.mpr hg)

theorem sum_mZ_mul (K : ℤ) (C : ZMod N → ℤ) (w : ZMod N → ZMod N → ℤ) :
    ∑ r : ZMod N, ∑ s : ZMod N,
      (K - K * (if r = 0 ∧ s = 0 then 1 else 0) - (if r = 1 then 1 else 0) + (if r = 0 then C s else 0)) * w r s =
      K * (∑ r : ZMod N, ∑ s : ZMod N, w r s) - K * w 0 0 - (∑ s : ZMod N, w 1 s) + ∑ s : ZMod N, C s * w 0 s := by
  have e1 : ∑ r : ZMod N, ∑ s : ZMod N, K * w r s = K * ∑ r : ZMod N, ∑ s : ZMod N, w r s := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => ?_; rw [Finset.mul_sum]
  have e2 : ∑ r : ZMod N, ∑ s : ZMod N, (K * (if r = 0 ∧ s = 0 then 1 else 0)) * w r s = K * w 0 0 := by
    rw [Finset.sum_eq_single (0 : ZMod N)]
    · rw [Finset.sum_eq_single (0 : ZMod N)]
      · simp
      · intro s _ hs; simp [hs]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro r _ hr; apply Finset.sum_eq_zero; intro s _; simp [hr]
    · intro h; exact absurd (Finset.mem_univ _) h
  have e3 : ∑ r : ZMod N, ∑ s : ZMod N, (if r = 1 then (1 : ℤ) else 0) * w r s = ∑ s : ZMod N, w 1 s := by
    rw [Finset.sum_eq_single (1 : ZMod N)]
    · simp
    · intro r _ hr; apply Finset.sum_eq_zero; intro s _; simp [hr]
    · intro h; exact absurd (Finset.mem_univ _) h
  have e4 : ∑ r : ZMod N, ∑ s : ZMod N, (if r = 0 then C s else 0) * w r s = ∑ s : ZMod N, C s * w 0 s := by
    rw [Finset.sum_eq_single (0 : ZMod N)]
    · simp
    · intro r _ hr; apply Finset.sum_eq_zero; intro s _; simp [hr]
    · intro h; exact absurd (Finset.mem_univ _) h
  have : ∀ r s : ZMod N,
      (K - K * (if r = 0 ∧ s = 0 then 1 else 0) - (if r = 1 then 1 else 0) + (if r = 0 then C s else 0)) * w r s =
        K * w r s - (K * (if r = 0 ∧ s = 0 then 1 else 0)) * w r s - (if r = 1 then (1 : ℤ) else 0) * w r s +
          (if r = 0 then C s else 0) * w r s := by
    intro r s; ring
  simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [e1, e2, e3, e4]

end construction

end Peak

open Peak in
theorem solution (N : ℕ) [NeZero N] (hN : 2 ≤ N) :
    ∃ (m : ZMod N → ZMod N → ℕ) (Ord : ZMod N → ZMod N → ℤ),
      (∀ x y : ZMod N, Ord x y =
        ∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
          (6 * (((r * x + s * y).val : ℕ) : ℤ) ^ 2
            - 6 * (N : ℤ) * (((r * x + s * y).val : ℕ) : ℤ) + (N : ℤ) ^ 2)) ∧
      m 0 0 = 0 ∧
      (∀ r s : ZMod N, m r (s + r) = m r s) ∧
      0 < Ord 1 0 ∧
      ∀ x y : ZMod N, (∃ a b : ZMod N, a * x + b * y = 1) →
        ¬ (y = 0 ∧ (x = 1 ∨ x = -1)) → ¬ (y = 1 ∨ y = -1) →
        Ord 1 0 < Ord x y := by
  classical
  haveI : Fact (1 < N) := ⟨by omega⟩
  have hNpos : 0 < N := by omega
  have hNZ : (0 : ℤ) < N := by exact_mod_cast hNpos
  have h01 : (0 : ZMod N) ≠ 1 := zero_ne_one
  have h0m1 : (0 : ZMod N) ≠ -1 := by
    intro h; apply h01; have := congrArg Neg.neg h; simpa using this

  set t₀ : ℚ := (N : ℚ) ^ 3 + 1 with ht₀
  set L : ℚ := 2 * (N : ℚ) ^ 3 + 1 with hL
  let P : ZMod N → Prop := fun r => r = 1 ∨ r = -1
  set T' : ZMod N → ℚ := fun r => if r = 0 then t₀ else t₀ + L with hT'
  set Spm : ℚ := ∑ r ∈ Finset.univ.filter P, (wt N r : ℚ) with hSpm
  set rest : ℚ := ∑ r ∈ Finset.univ.filter (fun r => ¬ P r), (wt N r : ℚ) * T' r with hrest
  have hSpm_pos : 0 < Spm := by
    rw [hSpm]
    refine Finset.sum_pos' (fun r _ => by exact_mod_cast Nat.zero_le _) ⟨1, ?_, by exact_mod_cast wt_pos 1⟩
    simp [P]
  set τ : ℚ := -rest / Spm with hτ
  set T : ZMod N → ℚ := fun r => if r = 0 then t₀ else if P r then τ else t₀ + L with hT
  have hT_even : ∀ r : ZMod N, T (-r) = T r := by
    intro r
    simp only [hT, P, neg_eq_zero]
    have : ((-r = 1) ∨ (-r = -1)) ↔ (r = 1 ∨ r = -1) := by
      rw [neg_eq_iff_eq_neg, neg_inj, or_comm]
    simp only [this]
  have hΛT : ∑ r : ZMod N, (wt N r : ℚ) * T r = 0 := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ P]
    have h1 : ∑ r ∈ Finset.univ.filter P, (wt N r : ℚ) * T r = τ * Spm := by
      rw [hSpm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.mem_filter] at hr
      have hr0 : r ≠ 0 := by
        rcases hr.2 with h | h
        · rw [h]; exact one_ne_zero
        · rw [h]; exact fun h' => h0m1 h'.symm
      simp only [hT, if_neg hr0, if_pos hr.2]; ring
    have h2 : ∑ r ∈ Finset.univ.filter (fun r => ¬ P r), (wt N r : ℚ) * T r = rest := by
      rw [hrest]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.mem_filter] at hr
      simp only [hT, hT', if_neg hr.2]
    rw [h1, h2, hτ, div_mul_cancel₀ _ hSpm_pos.ne']
    ring

  have hspan := (ModularCurve.SiegelUnit.mem_span_levelBernoulliWeight_dilate_iff_even N T).mpr hT_even
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℚ)).mp hspan
  have hcr : ∀ r : ZMod N, ∑ s : ZMod N, c s * (W N (s * r).val : ℚ) = T r := by
    intro r
    have := congrFun hc r
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, W] using this
  have hc0 : c 0 = 0 := by

    have hdeg : ∀ s : ZMod N, s ≠ 0 → ∑ r : ZMod N, (wt N r : ℚ) * (W N (s * r).val : ℚ) = 0 := by
      intro s hs
      have h := ModularCurve.SiegelUnit.sum_totient_mul_levelBernoulliWeight_dilate_eq_zero N s hs
      have h' : ∑ r : ZMod N, (wt N r : ℤ) * W N (s * r).val = 0 := by simpa [wt, W] using h
      have := congrArg (fun z : ℤ => (z : ℚ)) h'
      push_cast at this
      exact this
    have hsum : ∑ r : ZMod N, (wt N r : ℚ) * T r =
        ∑ s : ZMod N, c s * ∑ r : ZMod N, (wt N r : ℚ) * (W N (s * r).val : ℚ) := by
      simp_rw [← hcr, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun r _ => ?_
      ring
    rw [hΛT] at hsum
    rw [Finset.sum_eq_single (0 : ZMod N) (fun s _ hs => by rw [hdeg s hs, mul_zero])
      (fun h => absurd (Finset.mem_univ _) h)] at hsum
    simp only [zero_mul, ZMod.val_zero, W_zero] at hsum
    have hν : (0 : ℚ) < ∑ r : ZMod N, (wt N r : ℚ) * ((N : ℤ) ^ 2 : ℤ) := by
      refine Finset.sum_pos (fun r _ => ?_) Finset.univ_nonempty
      have := wt_pos (N := N) r
      positivity
    exact (mul_eq_zero.mp hsum.symm).resolve_right hν.ne'

  set D : ℕ := ∏ s : ZMod N, (c s).den with hD
  have hDpos : 0 < D := Finset.prod_pos fun s _ => (c s).den_pos
  set Cz : ZMod N → ℤ := fun s => (c s).num * ((D / (c s).den : ℕ) : ℤ) with hCz
  have hCzQ : ∀ s, (Cz s : ℚ) = (D : ℚ) * c s := by
    intro s
    have hdvd : (c s).den ∣ D := Finset.dvd_prod_of_mem (fun s => (c s).den) (Finset.mem_univ s)
    obtain ⟨k, hk⟩ := hdvd
    have hq : D / (c s).den = k := by rw [hk, Nat.mul_div_cancel_left _ (c s).den_pos]
    simp only [hCz, hq]
    rw [hk]
    push_cast
    rw [← Rat.mul_den_eq_num (c s)]
    ring
  have hCz0 : Cz 0 = 0 := by simp [hCz, hc0]
  set E : ZMod N → ℤ := fun y => ∑ s : ZMod N, Cz s * W N (s * y).val with hE
  have hEQ : ∀ y, (E y : ℚ) = D * T y := by
    intro y
    simp only [hE]
    push_cast
    simp_rw [hCzQ, mul_assoc, ← Finset.mul_sum, hcr y]
  have hE0 : E 0 = D * ((N : ℤ) ^ 3 + 1) := by
    have := hEQ 0
    simp only [hT, if_pos rfl, ht₀] at this
    exact_mod_cast this
  have hEy : ∀ y : ZMod N, y ≠ 0 → ¬ (y = 1 ∨ y = -1) → E y = D * (3 * (N : ℤ) ^ 3 + 2) := by
    intro y hy hP
    have := hEQ y
    simp only [hT, if_neg hy, P, if_neg hP, ht₀, hL] at this
    have h2 : (E y : ℚ) = ((D * (3 * (N : ℤ) ^ 3 + 2) : ℤ) : ℚ) := by rw [this]; push_cast; ring
    exact_mod_cast h2

  set K : ℤ := 1 + ∑ s : ZMod N, |Cz s| with hK
  set mZ : ZMod N → ZMod N → ℤ := fun r s =>
    K - K * (if r = 0 ∧ s = 0 then 1 else 0) - (if r = 1 then 1 else 0) + (if r = 0 then Cz s else 0) with hmZ
  have hmZ00 : mZ 0 0 = 0 := by simp [hmZ, h01, hCz0]
  have hmZ_nonneg : ∀ r s, 0 ≤ mZ r s := by
    intro r s
    by_cases h : r = 0 ∧ s = 0
    · obtain ⟨rfl, rfl⟩ := h; rw [hmZ00]
    · have habs : |Cz s| ≤ ∑ t : ZMod N, |Cz t| :=
        Finset.single_le_sum (f := fun t => |Cz t|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
      have h1 : (if r = 1 then (1 : ℤ) else 0) ≤ 1 := by split_ifs <;> norm_num
      have h2 : -|Cz s| ≤ (if r = 0 then Cz s else 0) := by
        split_ifs
        · exact neg_abs_le _
        · simp
      simp only [hmZ, if_neg h, mul_zero, sub_zero]
      linarith
  have hmZ_inv : ∀ r s, mZ r (s + r) = mZ r s := by
    intro r s
    by_cases hr : r = 0
    · subst hr; simp [hmZ]
    · simp [hmZ, hr]
  set m : ZMod N → ZMod N → ℕ := fun r s => (mZ r s).toNat with hm
  have hm_cast : ∀ r s, (m r s : ℤ) = mZ r s := fun r s => Int.toNat_of_nonneg (hmZ_nonneg r s)

  have hOrd : ∀ x y : ZMod N, (∃ a b : ZMod N, a * x + b * y = 1) →
      ∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) * W N (r * x + s * y).val =
        -(∑ s : ZMod N, W N (x + s * y).val) + E y := by
    intro x y ⟨a, b, hab⟩
    simp_rw [hm_cast]
    have := sum_mZ_mul K Cz (fun r s => W N (r * x + s * y).val)
    simp only [hmZ] at this ⊢
    rw [this, sum_sum_W_linear x y a b hab]
    simp only [zero_mul, zero_add, add_zero, ZMod.val_zero, W_zero, one_mul, hE]
    ring

  refine ⟨m, fun x y => ∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
      (6 * (((r * x + s * y).val : ℕ) : ℤ) ^ 2 - 6 * (N : ℤ) * (((r * x + s * y).val : ℕ) : ℤ) + (N : ℤ) ^ 2),
    fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · simp [hm, hmZ00]
  · intro r s; simp only [hm, hmZ_inv]
  ·
    show 0 < ∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) * W N (r * 1 + s * 0).val
    rw [hOrd 1 0 ⟨1, 0, by ring⟩, hE0]
    simp only [mul_zero, add_zero, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, nsmul_eq_mul]
    rw [ZMod.val_one]
    have h1 : W N 1 ≤ (N : ℤ) ^ 2 := W_le_sq (by omega)
    have hD1 : (1 : ℤ) ≤ D := by exact_mod_cast hDpos
    have e1 : (N : ℤ) * W N 1 ≤ (N : ℤ) ^ 3 := by
      have := mul_le_mul_of_nonneg_left h1 hNZ.le; nlinarith
    have e2 : ((N : ℤ) ^ 3 + 1) ≤ (D : ℤ) * ((N : ℤ) ^ 3 + 1) := le_mul_of_one_le_left (by positivity) hD1
    nlinarith
  · intro x y hprim hinf h0
    show ∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) * W N (r * 1 + s * 0).val <
      ∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) * W N (r * x + s * y).val
    rw [hOrd 1 0 ⟨1, 0, by ring⟩, hOrd x y hprim]
    simp only [mul_zero, add_zero, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, nsmul_eq_mul, ZMod.val_one]
    by_cases hy : y = 0
    ·
      subst hy
      have hx1 : x ≠ 1 := fun h => hinf ⟨rfl, Or.inl h⟩
      have hxm1 : x ≠ -1 := fun h => hinf ⟨rfl, Or.inr h⟩
      have hx0 : x ≠ 0 := by
        rintro rfl; obtain ⟨a, b, hab⟩ := hprim; simp at hab
      simp only [mul_zero, add_zero, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul, nsmul_eq_mul]
      set v : ℕ := x.val with hv
      have hvN : v < N := x.val_lt
      have hv0 : v ≠ 0 := fun h => hx0 ((ZMod.val_eq_zero x).mp h)
      have hv1 : v ≠ 1 := by
        intro h; apply hx1
        apply ZMod.val_injective N
        rw [← hv, h, ZMod.val_one]
      have hvN1 : v ≠ N - 1 := by
        intro h; apply hxm1
        have : (x : ZMod N) = ((v : ℕ) : ZMod N) := (ZMod.natCast_zmod_val x).symm
        rw [this, h, Nat.cast_sub (by omega), Nat.cast_one, ZMod.natCast_self, zero_sub]
      have hdiff := W_one_sub N v
      have hpos : 0 < W N 1 - W N v := by
        rw [hdiff]
        have h2 : (0 : ℤ) < (v : ℤ) - 1 := by omega
        have h3 : (0 : ℤ) < (N : ℤ) - 1 - v := by omega
        positivity
      have := mul_pos hNZ hpos
      nlinarith
    · rw [hE0, hEy y hy h0]
      have hB := sum_W_add_mul_le x y
      have h1 : -(N : ℤ) ^ 2 ≤ W N 1 := neg_sq_le_W N 1
      have hD1 : (1 : ℤ) ≤ D := by exact_mod_cast hDpos
      have e1 : -(N : ℤ) ^ 3 ≤ (N : ℤ) * W N 1 := by
        have := mul_le_mul_of_nonneg_left h1 hNZ.le; nlinarith
      have e2 : (2 * (N : ℤ) ^ 3 + 1) ≤ (D : ℤ) * (2 * (N : ℤ) ^ 3 + 1) :=
        le_mul_of_one_le_left (by positivity) hD1
      nlinarith

end S_ModularCurve_SiegelUnit_exists_peaked_exponent
end P2MW
export P2MW.S_ModularCurve_SiegelUnit_exists_peaked_exponent (solution)
