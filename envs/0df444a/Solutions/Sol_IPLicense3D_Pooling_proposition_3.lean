-- Prove2me | solution 1 for IPLicense3D.Pooling.proposition_3
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-03T07:55:10.184728+00:00
-- url     : https://prove2.me/submissions/6f62754e-3df4-4f55-aef0-6d29f924819a

import Mathlib
import Definitions.Def_IPLicense3D_Pooling_Model
open Filter Topology
open IPLicense3D.Pooling IPLicense3D.Pooling.Model

namespace IPL3DProp3Disproof

lemma surplus_sub (M : Model 2) (i : Fin 2) (f r : ℝ) :
    M.surplus i f r = M.surplus i 0 r - f := by
  simp only [surplus, surplusL, surplusF, costAF]; ring

lemma oemProfit_two (M : Model 2) (f r : ℝ) :
    M.oemProfit f r =
      (if 0 ≤ M.surplus 0 f r then f + r * M.lam 0 else (M.w - M.c) * M.lam 0) +
      (if 0 ≤ M.surplus 1 f r then f + r * M.lam 1 else (M.w - M.c) * M.lam 1) := by
  have : M.oemProfit f r = ∑ i, (if 0 ≤ M.surplus i f r then M.profitA i f r else M.profitT i) := by
    unfold oemProfit optsIn
    rw [Finset.sum_ite, Finset.filter_not]; ring
  rw [this, Fin.sum_univ_two]
  simp [profitA, profitT]

/-- `T_i(r) = S_i(0,r) + r λ_i` is antitone. -/
lemma T_anti (M : Model 2) (hM : M.Standing) (i : Fin 2) {r r' : ℝ} (hr : 0 ≤ r) (hrr : r ≤ r') :
    M.surplus i 0 r' + r' * M.lam i ≤ M.surplus i 0 r + r * M.lam i := by
  obtain ⟨hh, hw, hp, hkA, hkAT, hlA, hlAT, hz, hl⟩ := hM
  have hli := hl i
  have hc : 0 ≤ M.lam i * M.ellA + M.z * Real.sqrt (M.lam i * M.ellA) := by positivity
  have hs : Real.sqrt (2 * M.h * (r + M.p) * M.lam i * M.kA)
      ≤ Real.sqrt (2 * M.h * (r' + M.p) * M.lam i * M.kA) := by
    apply Real.sqrt_le_sqrt
    have : 0 ≤ 2 * M.h * M.lam i * M.kA := by positivity
    nlinarith
  simp only [surplus, surplusL, surplusF, costAF]
  nlinarith [mul_nonneg (mul_nonneg hh.le (sub_nonneg.2 hrr)) hc]

/-- `D(r) = S_1(0,r) - S_0(0,r)` is antitone when `λ_0 ≤ λ_1`. -/
lemma D_anti (M : Model 2) (hM : M.Standing) (hlam : M.lam 0 ≤ M.lam 1) {r r' : ℝ} (hr : 0 ≤ r)
    (hrr : r ≤ r') :
    M.surplus 1 0 r' - M.surplus 0 0 r' ≤ M.surplus 1 0 r - M.surplus 0 0 r := by
  obtain ⟨hh, hw, hp, hkA, hkAT, hlA, hlAT, hz, hl⟩ := hM
  have h0 := hl 0
  have h1 := hl 1
  have hsq : Real.sqrt (M.lam 0 * M.ellA) ≤ Real.sqrt (M.lam 1 * M.ellA) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hc : M.lam 0 * M.ellA + M.z * Real.sqrt (M.lam 0 * M.ellA) ≤
      M.lam 1 * M.ellA + M.z * Real.sqrt (M.lam 1 * M.ellA) := by
    nlinarith [mul_le_mul_of_nonneg_left hsq hz]
  have key : ∀ x l : ℝ, 0 ≤ x → 0 ≤ l →
      Real.sqrt (2 * M.h * x * l * M.kA) = Real.sqrt (2 * M.h * x * M.kA) * Real.sqrt l := by
    intro x l hx hl'
    rw [← Real.sqrt_mul (by positivity)]; ring_nf
  have hX : Real.sqrt (2 * M.h * (r + M.p) * M.kA) ≤ Real.sqrt (2 * M.h * (r' + M.p) * M.kA) := by
    apply Real.sqrt_le_sqrt
    have : 0 ≤ 2 * M.h * M.kA := by positivity
    nlinarith
  have hL : Real.sqrt (M.lam 0) ≤ Real.sqrt (M.lam 1) := Real.sqrt_le_sqrt hlam
  simp only [surplus, surplusL, surplusF, costAF, costTF]
  rw [key (r + M.p) (M.lam 0) (by linarith) h0.le, key (r + M.p) (M.lam 1) (by linarith) h1.le,
    key (r' + M.p) (M.lam 0) (by linarith) h0.le, key (r' + M.p) (M.lam 1) (by linarith) h1.le]
  nlinarith [mul_nonneg (sub_nonneg.2 hX) (sub_nonneg.2 hL),
    mul_nonneg (mul_nonneg hh.le (sub_nonneg.2 hrr)) (sub_nonneg.2 hc),
    mul_nonneg (sub_nonneg.2 hrr) (sub_nonneg.2 hlam)]

/-- Upper bound on the profit of any valid license. -/
lemma profit_le (M : Model 2) (hM : M.Standing) (hlam : M.lam 0 ≤ M.lam 1) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hD : M.surplus 0 0 ρ ≤ M.surplus 1 0 ρ) (f r : ℝ) (hf : 0 ≤ f) (hr : 0 ≤ r) :
    M.oemProfit f r ≤ max ((M.w - M.c) * (M.lam 0 + M.lam 1))
      (max ((M.w - M.c) * M.lam 1 + (M.surplus 0 0 ρ + ρ * M.lam 0))
        (max ((M.w - M.c) * M.lam 0 + M.maxSurplus 1) (M.maxSurplus 0 + M.maxSurplus 1))) := by
  have T0 := T_anti M hM 0 (le_refl 0) hr
  have T1 := T_anti M hM 1 (le_refl 0) hr
  have e0 := surplus_sub M 0 f r
  have e1 := surplus_sub M 1 f r
  simp only [zero_mul, add_zero] at T0 T1
  rw [oemProfit_two]
  unfold maxSurplus
  split_ifs with h0 h1 h1
  · apply le_max_of_le_right; apply le_max_of_le_right; apply le_max_of_le_right
    linarith
  · apply le_max_of_le_right; apply le_max_of_le_left
    have hρr : ρ < r := by
      by_contra hc
      push Not at hc
      have := D_anti M hM hlam hr hc
      linarith
    have := T_anti M hM 0 hρ hρr.le
    linarith
  · apply le_max_of_le_right; apply le_max_of_le_right; apply le_max_of_le_left
    linarith
  · apply le_max_of_le_left; ring_nf; rfl

lemma exists_root (M : Model 2) (i : Fin 2) (R : ℝ) (hR : 0 ≤ R) (hR' : 0 ≤ R + M.p)
    (h0 : 0 ≤ M.surplus i 0 0) (hneg : M.surplus i 0 R ≤ 0) :
    ∃ rb, 0 ≤ rb ∧ M.surplus i 0 rb = 0 := by
  have hc : ContinuousOn (fun r => M.surplus i 0 r) (Set.Icc 0 R) := by
    simp only [surplus, surplusL, surplusF, costAF, costTF]
    fun_prop
  obtain ⟨x, hx, hx'⟩ := intermediate_value_Icc' hR hc ⟨hneg, h0⟩
  exact ⟨x, hx.1, hx'⟩

lemma surplus_eval (M : Model 2) (i : Fin 2) (r a b cc d : ℝ)
    (ha : Real.sqrt (M.lam i * M.ellT) = a) (hb : Real.sqrt (2 * M.h * M.w * M.lam i * M.kT) = b)
    (hc : Real.sqrt (M.lam i * M.ellA) = cc) (hd : Real.sqrt (2 * M.h * (r + M.p) * M.lam i * M.kA) = d) :
    M.surplus i 0 r = M.h * M.w * (M.lam i * M.ellT + M.z * a) + b + M.w * M.lam i
      - (0 + M.h * (r + M.p) * (M.lam i * M.ellA + M.z * cc) + d + (r + M.p) * M.lam i) := by
  simp only [surplus, surplusL, surplusF, costAF, costTF]
  rw [ha, hb, hc, hd]

lemma sqrt_eval {x y : ℝ} (hy : 0 ≤ y) (h : x = y ^ 2) : Real.sqrt x = y := by
  rw [h, Real.sqrt_sq hy]

noncomputable def M0 : Model 2 :=
  { h := 20, w := 289 / 10000, c := -1965 / 2, p := 1 / 1000000, kT := 31360, kA := 32 / 5,
    ellT := 100, ellA := 16 / 25, z := 3 / 2, lam := ![1 / 2500, 1] }

noncomputable def M1 : Model 2 := M0.withW (1 / 25)


lemma M0_h : M0.h = 20 := rfl
lemma M0_w : M0.w = 289 / 10000 := rfl
lemma M0_p : M0.p = 1 / 1000000 := rfl
lemma M0_kT : M0.kT = 31360 := rfl
lemma M0_kA : M0.kA = 32 / 5 := rfl
lemma M0_lT : M0.ellT = 100 := rfl
lemma M0_lA : M0.ellA = 16 / 25 := rfl
lemma M0_z : M0.z = 3 / 2 := rfl
lemma M0_l0 : M0.lam 0 = 1 / 2500 := rfl
lemma M0_l1 : M0.lam 1 = 1 := rfl
lemma M1_h : M1.h = 20 := rfl
lemma M1_w : M1.w = 1 / 25 := rfl
lemma M1_p : M1.p = 1 / 1000000 := rfl
lemma M1_kT : M1.kT = 31360 := rfl
lemma M1_kA : M1.kA = 32 / 5 := rfl
lemma M1_lT : M1.ellT = 100 := rfl
lemma M1_lA : M1.ellA = 16 / 25 := rfl
lemma M1_z : M1.z = 3 / 2 := rfl
lemma M1_l0 : M1.lam 0 = 1 / 2500 := rfl
lemma M1_l1 : M1.lam 1 = 1 := rfl
lemma M1_c : M1.c = -1965 / 2 := rfl
lemma M0_c : M0.c = -1965 / 2 := rfl

lemma M0_std : M0.Standing := by
  refine ⟨by norm_num [M0], by norm_num [M0], by norm_num [M0], by norm_num [M0], by norm_num [M0],
    by norm_num [M0], by norm_num [M0], by norm_num [M0], ?_⟩
  intro i; fin_cases i <;> norm_num [M0]

lemma M1_std : M1.Standing := by
  refine ⟨by norm_num [M1, M0, withW], by norm_num [M1, M0, withW], by norm_num [M1, M0, withW],
    by norm_num [M1, M0, withW], by norm_num [M1, M0, withW], by norm_num [M1, M0, withW],
    by norm_num [M1, M0, withW], by norm_num [M1, M0, withW], ?_⟩
  intro i; fin_cases i <;> norm_num [M1, M0, withW]

/-- Surplus of buyer 0 in model M0 at royalty `q^2 - p`. -/
lemma S00 (q : ℝ) (hq : 0 ≤ q) : M0.surplus 0 0 (q ^ 2 - 1 / 1000000) =
    20 * (289 / 10000) * (1 / 2500 * 100 + 3 / 2 * (1 / 5)) + 1120 * (17 / 100) * (1 / 50)
      + 289 / 10000 * (1 / 2500)
      - (0 + 20 * q ^ 2 * (1 / 2500 * (16 / 25) + 3 / 2 * (2 / 125)) + 16 * q * (1 / 50)
        + q ^ 2 * (1 / 2500)) := by
  rw [surplus_eval M0 0 _ (1 / 5) (1120 * (17 / 100) * (1 / 50)) (2 / 125) (16 * q * (1 / 50))]
  · simp only [M0_h, M0_w, M0_lT, M0_lA, M0_z, M0_l0, M0_l1, M0_p]; ring
  · exact sqrt_eval (by norm_num) (by simp only [M0_h, M0_w, M0_p, M0_kT, M0_kA, M0_lT, M0_lA, M0_z, M0_l0, M0_l1]; norm_num)
  · exact sqrt_eval (by norm_num) (by simp only [M0_h, M0_w, M0_p, M0_kT, M0_kA, M0_lT, M0_lA, M0_z, M0_l0, M0_l1]; norm_num)
  · exact sqrt_eval (by norm_num) (by simp only [M0_h, M0_w, M0_p, M0_kT, M0_kA, M0_lT, M0_lA, M0_z, M0_l0, M0_l1]; norm_num)
  · exact sqrt_eval (by positivity) (by simp only [M0_h, M0_w, M0_p, M0_kT, M0_kA, M0_lT, M0_lA, M0_z, M0_l0, M0_l1]; ring)

lemma S01 (q : ℝ) (hq : 0 ≤ q) : M0.surplus 1 0 (q ^ 2 - 1 / 1000000) =
    20 * (289 / 10000) * (1 * 100 + 3 / 2 * 10) + 1120 * (17 / 100) * 1 + 289 / 10000 * 1
      - (0 + 20 * q ^ 2 * (1 * (16 / 25) + 3 / 2 * (4 / 5)) + 16 * q * 1 + q ^ 2 * 1) := by
  rw [surplus_eval M0 1 _ 10 (1120 * (17 / 100) * 1) (4 / 5) (16 * q * 1)]
  · simp only [M0_h, M0_w, M0_lT, M0_lA, M0_z, M0_l0, M0_l1, M0_p]; ring
  · exact sqrt_eval (by norm_num) (by simp only [M0_h, M0_w, M0_p, M0_kT, M0_kA, M0_lT, M0_lA, M0_z, M0_l0, M0_l1]; norm_num)
  · exact sqrt_eval (by norm_num) (by simp only [M0_h, M0_w, M0_p, M0_kT, M0_kA, M0_lT, M0_lA, M0_z, M0_l0, M0_l1]; norm_num)
  · exact sqrt_eval (by norm_num) (by simp only [M0_h, M0_w, M0_p, M0_kT, M0_kA, M0_lT, M0_lA, M0_z, M0_l0, M0_l1]; norm_num)
  · exact sqrt_eval (by positivity) (by simp only [M0_h, M0_w, M0_p, M0_kT, M0_kA, M0_lT, M0_lA, M0_z, M0_l0, M0_l1]; ring)

lemma S10 (q : ℝ) (hq : 0 ≤ q) : M1.surplus 0 0 (q ^ 2 - 1 / 1000000) =
    20 * (1 / 25) * (1 / 2500 * 100 + 3 / 2 * (1 / 5)) + 1120 * (1 / 5) * (1 / 50)
      + 1 / 25 * (1 / 2500)
      - (0 + 20 * q ^ 2 * (1 / 2500 * (16 / 25) + 3 / 2 * (2 / 125)) + 16 * q * (1 / 50)
        + q ^ 2 * (1 / 2500)) := by
  rw [surplus_eval M1 0 _ (1 / 5) (1120 * (1 / 5) * (1 / 50)) (2 / 125) (16 * q * (1 / 50))]
  · simp only [M1_h, M1_w, M1_lT, M1_lA, M1_z, M1_l0, M1_l1, M1_p]; ring
  · exact sqrt_eval (by norm_num) (by simp only [M1_h, M1_w, M1_p, M1_kT, M1_kA, M1_lT, M1_lA, M1_z, M1_l0, M1_l1]; norm_num)
  · exact sqrt_eval (by norm_num) (by simp only [M1_h, M1_w, M1_p, M1_kT, M1_kA, M1_lT, M1_lA, M1_z, M1_l0, M1_l1]; norm_num)
  · exact sqrt_eval (by norm_num) (by simp only [M1_h, M1_w, M1_p, M1_kT, M1_kA, M1_lT, M1_lA, M1_z, M1_l0, M1_l1]; norm_num)
  · exact sqrt_eval (by positivity) (by simp only [M1_h, M1_w, M1_p, M1_kT, M1_kA, M1_lT, M1_lA, M1_z, M1_l0, M1_l1]; ring)

lemma S11 (q : ℝ) (hq : 0 ≤ q) : M1.surplus 1 0 (q ^ 2 - 1 / 1000000) =
    20 * (1 / 25) * (1 * 100 + 3 / 2 * 10) + 1120 * (1 / 5) * 1 + 1 / 25 * 1
      - (0 + 20 * q ^ 2 * (1 * (16 / 25) + 3 / 2 * (4 / 5)) + 16 * q * 1 + q ^ 2 * 1) := by
  rw [surplus_eval M1 1 _ 10 (1120 * (1 / 5) * 1) (4 / 5) (16 * q * 1)]
  · simp only [M1_h, M1_w, M1_lT, M1_lA, M1_z, M1_l0, M1_l1, M1_p]; ring
  · exact sqrt_eval (by norm_num) (by simp only [M1_h, M1_w, M1_p, M1_kT, M1_kA, M1_lT, M1_lA, M1_z, M1_l0, M1_l1]; norm_num)
  · exact sqrt_eval (by norm_num) (by simp only [M1_h, M1_w, M1_p, M1_kT, M1_kA, M1_lT, M1_lA, M1_z, M1_l0, M1_l1]; norm_num)
  · exact sqrt_eval (by norm_num) (by simp only [M1_h, M1_w, M1_p, M1_kT, M1_kA, M1_lT, M1_lA, M1_z, M1_l0, M1_l1]; norm_num)
  · exact sqrt_eval (by positivity) (by simp only [M1_h, M1_w, M1_p, M1_kT, M1_kA, M1_lT, M1_lA, M1_z, M1_l0, M1_l1]; ring)

end IPL3DProp3Disproof

open IPL3DProp3Disproof in
theorem solution : ¬ (∀ (M : Model 2) (hM : M.Standing) (hlam : M.lam 0 < M.lam 1)
    (hS0 : 0 < M.maxSurplus 0) (hS1 : 0 < M.maxSurplus 1) (rb0 rb1 : ℝ)
    (hrb0 : 0 ≤ rb0 ∧ M.surplus 0 0 rb0 = 0) (hrb1 : 0 ≤ rb1 ∧ M.surplus 1 0 rb1 = 0),
    (M.maxSurplus 0 ≤ M.maxSurplus 1 → rb1 ≤ rb0 →
      ∀ rh : ℝ, 0 ≤ rh → M.surplus 0 0 rh = M.surplus 1 0 rh →
        IsLUB M.validProfits (M.caseIValue rh) ∧
        (0 ≤ M.surplus 0 0 rh ∧
          M.oemProfit (M.surplus 0 0 rh) rh = 2 * M.surplus 0 0 rh + rh * (M.lam 0 + M.lam 1) ∧
          M.optsIn (M.surplus 0 0 rh) rh = Finset.univ) ∧
        (0 < M.surplus 0 0 rh →
          (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ M.surplus 0 0 (rh + ε) ∧ 0 ≤ rh + ε ∧
            M.optsIn (M.surplus 0 0 (rh + ε)) (rh + ε) = {0}) ∧
          Tendsto (fun ε => M.oemProfit (M.surplus 0 0 (rh + ε)) (rh + ε)) (𝓝[>] 0)
            (𝓝 ((M.w - M.c) * M.lam 1 + M.surplus 0 0 rh + rh * M.lam 0)))) ∧
    (M.maxSurplus 0 ≤ M.maxSurplus 1 → rb0 < rb1 →
      IsLUB M.validProfits (M.caseIIValue rb0) ∧
      M.oemProfit 0 rb0 = rb0 * (M.lam 0 + M.lam 1) ∧ M.optsIn 0 rb0 = Finset.univ) ∧
    (M.maxSurplus 1 < M.maxSurplus 0 →
      IsLUB M.validProfits M.caseIIIValue ∧
      (M.oemProfit (M.maxSurplus 1) 0 = 2 * M.maxSurplus 1 ∧
        M.optsIn (M.maxSurplus 1) 0 = Finset.univ) ∧
      (M.oemProfit (M.maxSurplus 0) 0 = (M.w - M.c) * M.lam 1 + M.maxSurplus 0 ∧
        M.optsIn (M.maxSurplus 0) 0 = {0})) ∧
    (M.maxSurplus 0 ≤ M.maxSurplus 1 →
      M.oemProfit (M.maxSurplus 0) 0 = 2 * M.maxSurplus 0 ∧
      M.optsIn (M.maxSurplus 0) 0 = Finset.univ) ∧
    (M.maxSurplus 0 < M.maxSurplus 1 →
      M.oemProfit (M.maxSurplus 1) 0 = (M.w - M.c) * M.lam 0 + M.maxSurplus 1 ∧
      M.optsIn (M.maxSurplus 1) 0 = {1}) ∧
    ((∃ f r : ℝ, 0 ≤ f ∧ 0 ≤ r ∧ ∀ i, M.surplus i f r < 0) ∧
      ∀ f r : ℝ, (∀ i, M.surplus i f r < 0) →
        M.oemProfit f r = (M.w - M.c) * (M.lam 0 + M.lam 1) ∧ M.optsIn f r = ∅) ∧
    (∀ w' : ℝ, M.w ≤ w' → ∀ v v' : ℝ,
      IsLUB M.validProfits v → IsLUB (M.withW w').validProfits v' → v ≤ v')) := by
  intro H
  have hlam : M0.lam 0 < M0.lam 1 := by norm_num [M0]
  have hlam' : M1.lam 0 ≤ M1.lam 1 := by norm_num [M1, M0, withW]
  -- maximal surpluses (royalty 0 = (1/1000)^2 - p)
  have z0 : (0 : ℝ) = (1 / 1000) ^ 2 - 1 / 1000000 := by norm_num
  have hS00 : M0.maxSurplus 0 = M0.surplus 0 0 ((1 / 1000) ^ 2 - 1 / 1000000) := by
    unfold maxSurplus; rw [← z0]
  have hS01 : M0.maxSurplus 1 = M0.surplus 1 0 ((1 / 1000) ^ 2 - 1 / 1000000) := by
    unfold maxSurplus; rw [← z0]
  have hS0 : 0 < M0.maxSurplus 0 := by rw [hS00, S00 _ (by norm_num)]; norm_num
  have hS1 : 0 < M0.maxSurplus 1 := by rw [hS01, S01 _ (by norm_num)]; norm_num
  -- roots
  obtain ⟨rb0, hrb0⟩ := exists_root M0 0 ((100 : ℝ) ^ 2 - 1 / 1000000) (by norm_num)
    (by simp only [M0_h, M0_w, M0_p, M0_kT, M0_kA, M0_lT, M0_lA, M0_z, M0_l0, M0_l1]; norm_num) hS0.le (by rw [S00 _ (by norm_num)]; norm_num)
  obtain ⟨rb1, hrb1⟩ := exists_root M0 1 ((100 : ℝ) ^ 2 - 1 / 1000000) (by norm_num)
    (by simp only [M0_h, M0_w, M0_p, M0_kT, M0_kA, M0_lT, M0_lA, M0_z, M0_l0, M0_l1]; norm_num) hS1.le (by rw [S01 _ (by norm_num)]; norm_num)
  have Hm := (H M0 M0_std hlam hS0 hS1 rb0 rb1 hrb0 hrb1).2.2.2.2.2.2 (1 / 25)
    (by norm_num [M0])
  -- the profit set at w
  have hD0 : M0.surplus 0 0 0 ≤ M0.surplus 1 0 0 := by
    have a := hS00; have b := hS01; simp only [maxSurplus] at a b
    rw [a, b, S00 _ (by norm_num), S01 _ (by norm_num)]; norm_num
  have bdd0 : BddAbove M0.validProfits := by
    exact ⟨_, fun v ⟨f, r, hf, hr, hv⟩ => hv ▸ profit_le M0 M0_std hlam.le 0 le_rfl hD0 f r hf hr⟩
  have ne0 : M0.validProfits.Nonempty := ⟨M0.oemProfit 0 0, 0, 0, le_rfl, le_rfl, rfl⟩
  -- bound at w' with ρ = q1^2 - p
  set q1 : ℝ := 26855 / 10000
  have hρ : 0 ≤ q1 ^ 2 - 1 / 1000000 := by norm_num [q1]
  have hD1 : M1.surplus 0 0 (q1 ^ 2 - 1 / 1000000) ≤ M1.surplus 1 0 (q1 ^ 2 - 1 / 1000000) := by
    rw [S10 _ (by norm_num [q1]), S11 _ (by norm_num [q1])]; norm_num [q1]
  have hS10 : M1.maxSurplus 0 = M1.surplus 0 0 ((1 / 1000) ^ 2 - 1 / 1000000) := by
    unfold maxSurplus; rw [← z0]
  have hS11 : M1.maxSurplus 1 = M1.surplus 1 0 ((1 / 1000) ^ 2 - 1 / 1000000) := by
    unfold maxSurplus; rw [← z0]
  have bdd1 : ∀ v ∈ M1.validProfits, v ≤ 98293402 / 100000 := by
    rintro v ⟨f, r, hf, hr, rfl⟩
    have := profit_le M1 M1_std hlam' _ hρ hD1 f r hf hr
    rw [hS10, hS11, S10 _ (by norm_num), S11 _ (by norm_num), S10 _ (by norm_num [q1])] at this
    have hw : M1.w = 1 / 25 := rfl
    have hc : M1.c = -1965 / 2 := rfl
    have hl0 : M1.lam 0 = 1 / 2500 := rfl
    have hl1 : M1.lam 1 = 1 := rfl
    rw [hw, hc, hl0, hl1] at this
    refine this.trans ?_
    norm_num [q1]
  -- a near-optimal license at w
  set q0 : ℝ := 24017 / 10000
  have hr0 : 0 ≤ q0 ^ 2 - 1 / 1000000 := by norm_num [q0]
  have hf0 : 0 ≤ M0.surplus 0 0 (q0 ^ 2 - 1 / 1000000) := by
    rw [S00 _ (by norm_num [q0])]; norm_num [q0]
  have hmem : M0.oemProfit (M0.surplus 0 0 (q0 ^ 2 - 1 / 1000000)) (q0 ^ 2 - 1 / 1000000)
      ∈ M0.validProfits := ⟨_, _, hf0, hr0, rfl⟩
  have hval : 98293403 / 100000 < M0.oemProfit (M0.surplus 0 0 (q0 ^ 2 - 1 / 1000000))
      (q0 ^ 2 - 1 / 1000000) := by
    rw [oemProfit_two, surplus_sub M0 0, surplus_sub M0 1, sub_self, if_pos le_rfl,
      if_neg (by rw [S00 _ (by norm_num [q0]), S01 _ (by norm_num [q0])]; norm_num [q0])]
    rw [S00 _ (by norm_num [q0])]
    have hw : M0.w = 289 / 10000 := rfl
    have hc : M0.c = -1965 / 2 := rfl
    have hl0 : M0.lam 0 = 1 / 2500 := rfl
    have hl1 : M0.lam 1 = 1 := rfl
    rw [hw, hc, hl0, hl1]
    norm_num [q0]
  have ne1 : M1.validProfits.Nonempty := ⟨M1.oemProfit 0 0, 0, 0, le_rfl, le_rfl, rfl⟩
  have key := Hm (sSup M0.validProfits) (sSup M1.validProfits) (isLUB_csSup ne0 bdd0)
    (isLUB_csSup ne1 ⟨_, bdd1⟩)
  have h1 : sSup M1.validProfits ≤ 98293402 / 100000 := csSup_le ne1 bdd1
  have h2 := le_csSup bdd0 hmem
  linarith
