-- Prove2me | solution 1 for HuangYin.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T05:37:36.349188+00:00
-- url     : https://prove2.me/submissions/09972450-72d6-4aea-9db3-52cf21c174f1

import Mathlib
import Definitions.Def_HuangYin_IsOptimal
import Definitions.Def_HuangYin_Region1
import Definitions.Def_HuangYin_Region2

set_option autoImplicit false

namespace HYAux
open HuangYin

/-! ### Pure real arithmetic (profits divided by `cH - cL`, `r = (vHL - cL)/(cH - cL)`) -/

theorem G_le_int (α r ξ1 ξ2 : ℝ) (hD : 0 < 4 - 4*α - α^2) :
    ξ1*(r-ξ1) + (α*ξ1+(1-α)*ξ2)*(r-ξ2) ≤ 2*(1-α)*r^2/(4-4*α-α^2) := by
  have key : (4-4*α-α^2)*(2*(1-α)*r^2 - (4-4*α-α^2)*(ξ1*(r-ξ1) + (α*ξ1+(1-α)*ξ2)*(r-ξ2)))
      = ((4-4*α-α^2)*ξ1 - (2-α-α^2)*r + α*((4-4*α-α^2)*ξ2 - (2-3*α-α^2)*r)/2)^2
        + (4-4*α-α^2)/4*((4-4*α-α^2)*ξ2 - (2-3*α-α^2)*r)^2 := by ring
  have h0 : 0 ≤ (4-4*α-α^2)*(2*(1-α)*r^2 - (4-4*α-α^2)*(ξ1*(r-ξ1) + (α*ξ1+(1-α)*ξ2)*(r-ξ2))) := by
    rw [key]; exact add_nonneg (sq_nonneg _) (mul_nonneg (by linarith) (sq_nonneg _))
  have h1 : 0 ≤ 2*(1-α)*r^2 - (4-4*α-α^2)*(ξ1*(r-ξ1) + (α*ξ1+(1-α)*ξ2)*(r-ξ2)) := by
    by_contra hn
    push_neg at hn
    nlinarith [mul_pos_of_neg_of_neg (neg_neg_of_pos hD) hn]
  rw [le_div_iff₀ hD]
  linarith

theorem G_le_r2 (α r ξ1 ξ2 : ℝ) (hA : 0 ≤ α^2+3*α-2) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (h1 : 0 ≤ ξ1) (h2 : 0 ≤ ξ2) :
    ξ1*(r-ξ1) + (α*ξ1+(1-α)*ξ2)*(r-ξ2) ≤ (1+α)^2*r^2/4 := by
  rcases le_or_gt (α*ξ2) ((1+α)*r) with hc | hc
  · have hk0 : 0 ≤ (1+α)*((4-4*α-α^2)*ξ2 + 2*(α^2+3*α-2)*r) := by
      nlinarith [mul_le_mul_of_nonneg_left hc hA,
        mul_nonneg h2 (add_nonneg (sq_nonneg (2-α)) (pow_nonneg hα0 3))]
    have hk : 0 ≤ (4-4*α-α^2)*ξ2 + 2*(α^2+3*α-2)*r := by
      by_contra hneg
      push_neg at hneg
      nlinarith [mul_pos (by linarith : (0:ℝ) < 1+α) (neg_pos.2 hneg)]
    have e : (1+α)^2*r^2/4 - (ξ1*(r-ξ1) + (α*ξ1+(1-α)*ξ2)*(r-ξ2))
        = (ξ1 - ((1+α)*r - α*ξ2)/2)^2 + ξ2*((4-4*α-α^2)*ξ2 + 2*(α^2+3*α-2)*r)/4 := by ring
    nlinarith [sq_nonneg (ξ1 - ((1+α)*r - α*ξ2)/2), mul_nonneg h2 hk]
  · nlinarith [mul_nonneg h1 (by linarith : 0 ≤ ξ1 + α*ξ2 - (1+α)*r),
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 - α) (sq_nonneg (ξ2 - r/2)),
      mul_nonneg (by nlinarith : (0:ℝ) ≤ α^2+3*α) (sq_nonneg r)]

theorem G_le_C (α r ξ1 ξ2 : ℝ) (hα0 : 0 ≤ α) (hα23 : α < 2/3)
    (h1 : 0 ≤ ξ1) (h1' : ξ1 ≤ 1) (h2 : 0 ≤ ξ2) (h2' : ξ2 ≤ 1)
    (hrE : 4-4*α-α^2 ≤ r*(2-α-α^2)) :
    ξ1*(r-ξ1) + (α*ξ1+(1-α)*ξ2)*(r-ξ2) ≤ 2*r - 1 := by
  have hE : 0 < 2-α-α^2 := by nlinarith
  have hD : 0 < 4-4*α-α^2 := by nlinarith
  have hE' : (2-α-α^2) ≠ 0 := hE.ne'
  have hD' : (4-4*α-α^2) ≠ 0 := hD.ne'
  have g1 := G_le_int α ((4-4*α-α^2)/(2-α-α^2)) ξ1 ξ2 hD
  have a2 : α^2 ≤ 4/9 := by nlinarith
  have a3 : α^3 ≤ 8/27 := by nlinarith [mul_le_mul_of_nonneg_left a2 hα0]
  have g2 : 2*(1-α)*((4-4*α-α^2)/(2-α-α^2))^2/(4-4*α-α^2)
      ≤ 2*((4-4*α-α^2)/(2-α-α^2)) - 1 := by
    rw [div_le_iff₀ hD, ← sub_nonneg]
    have e : (2*((4-4*α-α^2)/(2-α-α^2)) - 1)*(4-4*α-α^2)
        - 2*(1-α)*((4-4*α-α^2)/(2-α-α^2))^2
        = (4-4*α-α^2)*((1-α)*(4-7*α^2-α^3))/(2-α-α^2)^2 := by
      field_simp
      ring
    rw [e]
    apply div_nonneg _ (sq_nonneg _)
    apply mul_nonneg hD.le
    apply mul_nonneg (by linarith)
    nlinarith
  have hR : (4-4*α-α^2)/(2-α-α^2) ≤ r := by rw [div_le_iff₀ hE]; linarith
  have hq : ξ1 + (α*ξ1+(1-α)*ξ2) ≤ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h1' hα0, mul_le_mul_of_nonneg_left h2' (by linarith : (0:ℝ) ≤ 1-α)]
  generalize (4-4*α-α^2)/(2-α-α^2) = R at g1 g2 hR
  have lin : (ξ1*(r-ξ1) + (α*ξ1+(1-α)*ξ2)*(r-ξ2))
      - (ξ1*(R-ξ1) + (α*ξ1+(1-α)*ξ2)*(R-ξ2))
      = (r - R)*(ξ1 + (α*ξ1+(1-α)*ξ2)) := by ring
  nlinarith [mul_le_mul_of_nonneg_left hq (sub_nonneg.2 hR)]

theorem G_le_D (α r ξ1 ξ2 : ℝ) (hA : 0 ≤ α^2+3*α-2) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (h1 : 0 ≤ ξ1) (h1' : ξ1 ≤ 1) (h2 : 0 ≤ ξ2) (h2' : ξ2 ≤ 1)
    (hr : 2 ≤ r*(1+α)) :
    ξ1*(r-ξ1) + (α*ξ1+(1-α)*ξ2)*(r-ξ2) ≤ 2*r - 1 := by
  have hp : 0 < 1+α := by linarith
  have g1 := G_le_r2 α (2/(1+α)) ξ1 ξ2 hA hα0 hα1 h1 h2
  have e1 : (1+α)^2*(2/(1+α))^2/4 = 1 := by field_simp; ring
  rw [e1] at g1
  have hR : 2/(1+α) ≤ r := by rw [div_le_iff₀ hp]; linarith
  have hR1 : 1 ≤ 2/(1+α) := by rw [le_div_iff₀ hp]; linarith
  have hq : ξ1 + (α*ξ1+(1-α)*ξ2) ≤ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h1' hα0, mul_le_mul_of_nonneg_left h2' (by linarith : (0:ℝ) ≤ 1-α)]
  generalize 2/(1+α) = R at g1 hR hR1
  have lin : (ξ1*(r-ξ1) + (α*ξ1+(1-α)*ξ2)*(r-ξ2))
      - (ξ1*(R-ξ1) + (α*ξ1+(1-α)*ξ2)*(R-ξ2))
      = (r - R)*(ξ1 + (α*ξ1+(1-α)*ξ2)) := by ring
  nlinarith [mul_le_mul_of_nonneg_left hq (sub_nonneg.2 hR)]

theorem LH_le (α r m ξ1 ξ2 : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (h1 : 0 ≤ ξ1) (h1' : ξ1 ≤ 1) (h2 : 0 ≤ ξ2) (h2' : ξ2 ≤ 1)
    (hφ : ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 → ξ*(r-ξ) ≤ m) (h : α*r ≤ 1 ∨ r - 1/2 ≤ m) :
    (α*ξ1+(1-α)*ξ2)*(r-ξ2) - ξ1 ≤ m := by
  have hm0 : 0 ≤ m := by have := hφ 0 le_rfl zero_le_one; linarith
  have hφ2 := hφ ξ2 h2 h2'
  by_cases hc : α*r ≤ 1
  · have a1 : α*ξ1*(r-ξ2) ≤ ξ1 := by
      nlinarith [mul_le_mul_of_nonneg_left hc h1, mul_nonneg (mul_nonneg hα0 h1) h2]
    have a2 : (1-α)*(ξ2*(r-ξ2)) ≤ m := by
      nlinarith [mul_le_mul_of_nonneg_left hφ2 (by linarith : (0:ℝ) ≤ 1-α), mul_nonneg hα0 hm0]
    nlinarith
  · push_neg at hc
    have hm : r - 1/2 ≤ m := h.resolve_left (not_le.2 hc)
    have hr1 : 1 < r := by
      by_contra hr
      push_neg at hr
      nlinarith [mul_le_mul_of_nonneg_left hr hα0]
    have a1 : α*ξ1*(r-ξ2) - ξ1 ≤ α*r - 1 := by
      nlinarith [mul_le_mul_of_nonneg_right h1' (by linarith : (0:ℝ) ≤ α*r - 1),
        mul_nonneg (mul_nonneg hα0 h1) h2]
    have a2 : ξ2*(r-ξ2) ≤ r - 1/2 := by
      nlinarith [sq_nonneg (ξ2 - 1/2), mul_le_mul_of_nonneg_right hr1.le (by linarith : (0:ℝ) ≤ 1 - ξ2)]
    have a3 : (1-α)*(ξ2*(r-ξ2)) ≤ (1-α)*(r-1/2) :=
      mul_le_mul_of_nonneg_left a2 (by linarith)
    nlinarith

theorem combos (α r L m b ξ1 ξ2 : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (h1 : 0 ≤ ξ1) (h1' : ξ1 ≤ 1) (h2 : 0 ≤ ξ2) (h2' : ξ2 ≤ 1)
    (hG : ξ1*(r-ξ1) + (α*ξ1+(1-α)*ξ2)*(r-ξ2) ≤ b)
    (hLm : L ≤ m) (hφ : ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 → ξ*(r-ξ) ≤ m)
    (hLH : α*r ≤ 1 ∨ r - 1/2 ≤ m) (hmb : 2*m ≤ b) :
    ξ1*(r-ξ1) + (α*ξ1+(1-α)*ξ2)*(r-ξ2) ≤ b ∧ ξ1*(r-ξ1) + (L-ξ2) ≤ b ∧ ξ1*(r-ξ1) ≤ b ∧
    (L-ξ1) + (α*ξ1+(1-α)*ξ2)*(r-ξ2) ≤ b ∧ (L-ξ1) + (L-ξ2) ≤ b ∧ L-ξ1 ≤ b := by
  have hm0 : 0 ≤ m := by have := hφ 0 le_rfl zero_le_one; linarith
  have a := hφ ξ1 h1 h1'
  have c := LH_le α r m ξ1 ξ2 hα0 hα1 h1 h1' h2 h2' hφ hLH
  refine ⟨hG, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem alpha_lt (α : ℝ) (hα0 : 0 ≤ α) (h : α < (Real.sqrt 17 - 3)/2) : α^2 + 3*α - 2 < 0 := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hs0 := Real.sqrt_nonneg 17
  have key : α^2+3*α-2 = (α - (Real.sqrt 17 - 3)/2)*(α + (Real.sqrt 17 - 3)/2 + 3) := by
    linear_combination (1/4 : ℝ) * hs
  rw [key]
  exact mul_neg_of_neg_of_pos (by linarith) (by linarith)

theorem alpha_ge (α : ℝ) (hα0 : 0 ≤ α) (h : (Real.sqrt 17 - 3)/2 ≤ α) : 0 ≤ α^2 + 3*α - 2 := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hs0 := Real.sqrt_nonneg 17
  have key : α^2+3*α-2 = (α - (Real.sqrt 17 - 3)/2)*(α + (Real.sqrt 17 - 3)/2 + 3) := by
    linear_combination (1/4 : ℝ) * hs
  rw [key]
  exact mul_nonneg (by linarith) (by linarith)

/-! ### The model -/

theorem vL_lt (P : Params) : P.vL < vHL P := by unfold vHL; linarith [P.hv]

theorem buys_true (P : Params) (p : ℝ) : Buys P p true ↔ p ≤ vHL P := by
  unfold Buys estimate vHL
  constructor <;> intro h <;> norm_num at h ⊢ <;> linarith

theorem buys_false (P : Params) (p : ℝ) : Buys P p false ↔ p ≤ P.vL := by
  unfold Buys estimate
  norm_num

theorem demand_vHL (P : Params) (q : ℝ) : demand P (vHL P) q = q := by
  have hf : ¬ Buys P (vHL P) false := by rw [buys_false]; have := vL_lt P; linarith
  have ht : Buys P (vHL P) true := (buys_true P _).2 le_rfl
  simp only [demand, if_neg hf, if_pos ht]
  ring

theorem per1 (P : Params) (p ξ : ℝ) (hξ : 0 ≤ ξ) (hp : p ≤ vHL P) :
    demand P p ξ * (p - cost P ξ) ≤ P.vL - cost P ξ ∨
    demand P p ξ * (p - cost P ξ) ≤ ξ * (vHL P - cost P ξ) := by
  by_cases ha : p ≤ P.vL
  · left
    simp only [demand, if_pos ((buys_false P p).2 ha), if_pos ((buys_true P p).2 hp)]
    nlinarith
  · right
    simp only [demand, if_neg (fun h => ha ((buys_false P p).1 h)), if_pos ((buys_true P p).2 hp)]
    nlinarith [mul_le_mul_of_nonneg_left hp hξ]

theorem per2 (P : Params) (p q ξ : ℝ) (hq : 0 ≤ q) :
    demand P p q * (p - cost P ξ) ≤ P.vL - cost P ξ ∨
    demand P p q * (p - cost P ξ) ≤ q * (vHL P - cost P ξ) ∨
    demand P p q * (p - cost P ξ) ≤ 0 := by
  have hv := vL_lt P
  by_cases ha : p ≤ P.vL
  · have hb : p ≤ vHL P := by linarith
    left
    simp only [demand, if_pos ((buys_false P p).2 ha), if_pos ((buys_true P p).2 hb)]
    nlinarith
  · by_cases hb : p ≤ vHL P
    · right; left
      simp only [demand, if_neg (fun h => ha ((buys_false P p).1 h)),
        if_pos ((buys_true P p).2 hb)]
      nlinarith [mul_le_mul_of_nonneg_left hb hq]
    · right; right
      simp only [demand, if_neg (fun h => ha ((buys_false P p).1 h)),
        if_neg (fun h => hb ((buys_true P p).1 h))]
      simp

theorem opaque_le (P : Params) (p1 p2 ξ1 ξ2 B : ℝ) (h1 : 0 ≤ ξ1) (h2 : 0 ≤ ξ2)
    (hp1 : p1 ≤ vHL P)
    (hHH : ξ1*(vHL P - cost P ξ1) + (P.α*ξ1+(1-P.α)*ξ2)*(vHL P - cost P ξ2) ≤ B)
    (hHL : ξ1*(vHL P - cost P ξ1) + (P.vL - cost P ξ2) ≤ B)
    (hH0 : ξ1*(vHL P - cost P ξ1) ≤ B)
    (hLH : (P.vL - cost P ξ1) + (P.α*ξ1+(1-P.α)*ξ2)*(vHL P - cost P ξ2) ≤ B)
    (hLL : (P.vL - cost P ξ1) + (P.vL - cost P ξ2) ≤ B)
    (hL0 : P.vL - cost P ξ1 ≤ B) : opaqueProfit P p1 p2 ξ1 ξ2 ≤ B := by
  have hq : 0 ≤ P.α*ξ1+(1-P.α)*ξ2 := by
    nlinarith [mul_nonneg P.hα0 h1, mul_nonneg (sub_nonneg.2 P.hα1) h2]
  unfold opaqueProfit
  rcases per1 P p1 ξ1 h1 hp1 with a | a <;>
  rcases per2 P p2 (P.α*ξ1+(1-P.α)*ξ2) ξ2 hq with b | b | b <;> linarith

set_option maxHeartbeats 1000000 in
theorem opaque_scaled (P : Params) (r L b : ℝ)
    (hx : vHL P - P.cL = (P.cH - P.cL) * r) (hL : P.vL - P.cL = (P.cH - P.cL) * L)
    (H : ∀ ξ1 ξ2 : ℝ, 0 ≤ ξ1 → ξ1 ≤ 1 → 0 ≤ ξ2 → ξ2 ≤ 1 →
      ξ1*(r-ξ1) + (P.α*ξ1+(1-P.α)*ξ2)*(r-ξ2) ≤ b ∧ ξ1*(r-ξ1) + (L-ξ2) ≤ b ∧
      ξ1*(r-ξ1) ≤ b ∧ (L-ξ1) + (P.α*ξ1+(1-P.α)*ξ2)*(r-ξ2) ≤ b ∧
      (L-ξ1) + (L-ξ2) ≤ b ∧ L-ξ1 ≤ b)
    (p1 p2 ξ1 ξ2 : ℝ) (hf : (Policy.opaque p1 p2 ξ1 ξ2).Feasible P) :
    opaqueProfit P p1 p2 ξ1 ξ2 ≤ (P.cH - P.cL) * b := by
  simp only [Policy.Feasible, Set.mem_Icc] at hf
  obtain ⟨⟨h1, h1'⟩, ⟨h2, h2'⟩, hp1⟩ := hf
  have hΔ : 0 < P.cH - P.cL := sub_pos.2 P.hc
  have e1 : ∀ ξ, vHL P - cost P ξ = (P.cH - P.cL) * (r - ξ) := by
    intro ξ; unfold cost; linear_combination hx
  have e2 : ∀ ξ, P.vL - cost P ξ = (P.cH - P.cL) * (L - ξ) := by
    intro ξ; unfold cost; linear_combination hL
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := H ξ1 ξ2 h1 h1' h2 h2'
  apply opaque_le P p1 p2 ξ1 ξ2 _ h1 h2 hp1 <;> simp only [e1, e2] <;>
    linarith [mul_le_mul_of_nonneg_left a1 hΔ.le, mul_le_mul_of_nonneg_left a2 hΔ.le,
      mul_le_mul_of_nonneg_left a3 hΔ.le, mul_le_mul_of_nonneg_left a4 hΔ.le,
      mul_le_mul_of_nonneg_left a5 hΔ.le, mul_le_mul_of_nonneg_left a6 hΔ.le]

theorem transparent_le (P : Params) (m1 m2 : Product) (p1 p2 K : ℝ) (hK : 0 ≤ K)
    (hH : P.vH - P.cH ≤ K) (hL : P.vL - P.cL ≤ K) :
    transparentProfit P m1 m2 p1 p2 ≤ 2*K := by
  have per : ∀ (m : Product) (p : ℝ),
      (if p ≤ m.value P then (1:ℝ) else 0) * (p - m.unitCost P) ≤ K := by
    intro m p
    split_ifs with h
    · cases m <;> simp only [Product.value, Product.unitCost] at h ⊢ <;> linarith
    · rw [zero_mul]; exact hK
  unfold transparentProfit
  linarith [per m1 p1, per m2 p2]

set_option maxHeartbeats 1000000 in
theorem opt_of (P : Params) (π : Policy) (hf : π.Feasible P) (r L b : ℝ)
    (hx : vHL P - P.cL = (P.cH - P.cL) * r) (hL : P.vL - P.cL = (P.cH - P.cL) * L)
    (H : ∀ ξ1 ξ2 : ℝ, 0 ≤ ξ1 → ξ1 ≤ 1 → 0 ≤ ξ2 → ξ2 ≤ 1 →
      ξ1*(r-ξ1) + (P.α*ξ1+(1-P.α)*ξ2)*(r-ξ2) ≤ b ∧ ξ1*(r-ξ1) + (L-ξ2) ≤ b ∧
      ξ1*(r-ξ1) ≤ b ∧ (L-ξ1) + (P.α*ξ1+(1-P.α)*ξ2)*(r-ξ2) ≤ b ∧
      (L-ξ1) + (L-ξ2) ≤ b ∧ L-ξ1 ≤ b)
    (hprof : π.profit P = (P.cH - P.cL) * b) (hb0 : 0 ≤ b)
    (hHb : P.vH - P.cH ≤ (P.cH - P.cL) * (b/2)) (hLb : P.vL - P.cL ≤ (P.cH - P.cL) * (b/2)) :
    IsOptimal P π := by
  have hΔ : 0 < P.cH - P.cL := sub_pos.2 P.hc
  refine ⟨hf, ?_⟩
  intro π' hf'
  rw [hprof]
  rcases π' with ⟨p1, p2, ξ1, ξ2⟩ | ⟨m1, m2, p1, p2⟩
  · exact opaque_scaled P r L b hx hL H p1 p2 ξ1 ξ2 hf'
  · have := transparent_le P m1 m2 p1 p2 ((P.cH - P.cL) * (b/2))
      (mul_nonneg hΔ.le (by linarith)) hHb hLb
    show transparentProfit P m1 m2 p1 p2 ≤ _
    linarith

theorem setup (P : Params) : ∃ r L m1 : ℝ, r = (vHL P - P.cL)/(P.cH - P.cL) ∧
    vHL P - P.cL = (P.cH - P.cL)*r ∧ P.vL - P.cL = (P.cH - P.cL)*L ∧
    max (P.vH - P.cH) (P.vL - P.cL) = (P.cH - P.cL)*m1 ∧ L ≤ m1 ∧ r - 1/2 ≤ m1 := by
  have hΔ : 0 < P.cH - P.cL := sub_pos.2 P.hc
  have hΔ' : P.cH - P.cL ≠ 0 := hΔ.ne'
  refine ⟨(vHL P - P.cL)/(P.cH - P.cL), (P.vL - P.cL)/(P.cH - P.cL),
    max (P.vH - P.cH) (P.vL - P.cL)/(P.cH - P.cL), rfl, ?_, ?_, ?_, ?_, ?_⟩
  · field_simp
  · field_simp
  · field_simp
  · exact div_le_div_of_nonneg_right (le_max_right _ _) hΔ.le
  · have h1 := le_max_left (P.vH - P.cH) (P.vL - P.cL)
    have h2 := le_max_right (P.vH - P.cH) (P.vL - P.cL)
    have key : (vHL P - P.cL)/(P.cH - P.cL) - 1/2
        = ((P.vH - P.cH) + (P.vL - P.cL))/(2*(P.cH - P.cL)) := by
      unfold vHL; field_simp; ring
    rw [key, div_le_div_iff₀ (by linarith) hΔ]
    nlinarith [mul_le_mul_of_nonneg_right h1 hΔ.le, mul_le_mul_of_nonneg_right h2 hΔ.le]

set_option maxHeartbeats 1000000 in
theorem H_iii (P : Params) (r m1 : ℝ) (hr : r = (vHL P - P.cL)/(P.cH - P.cL))
    (hx : vHL P - P.cL = (P.cH - P.cL)*r)
    (hM : max (P.vH - P.cH) (P.vL - P.cL) = (P.cH - P.cL)*m1)
    (hrm : r - 1/2 ≤ m1) (n1 : ¬ Region1 P) (n2 : ¬ Region2 P) :
    (∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 → ξ*(r-ξ) ≤ m1) ∧
    (∀ ξ1 ξ2 : ℝ, 0 ≤ ξ1 → ξ1 ≤ 1 → 0 ≤ ξ2 → ξ2 ≤ 1 →
      ξ1*(r-ξ1) + (P.α*ξ1+(1-P.α)*ξ2)*(r-ξ2) ≤ 2*m1) := by
  have hΔ : 0 < P.cH - P.cL := sub_pos.2 P.hc
  have hΔ' : P.cH - P.cL ≠ 0 := hΔ.ne'
  have hα0 := P.hα0
  have hα1 := P.hα1
  have big : 1 ≤ r → ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 → ξ*(r-ξ) ≤ m1 := by
    intro h1r ξ h0 h1
    nlinarith [sq_nonneg (ξ - 1/2), mul_le_mul_of_nonneg_right h1r (by linarith : (0:ℝ) ≤ 1 - ξ)]
  rcases lt_or_ge P.α ((Real.sqrt 17 - 3)/2) with hαlt | hαge
  · have hA := alpha_lt P.α hα0 hαlt
    have hα23 : P.α < 2/3 := by nlinarith
    have hE : 0 < 2 - P.α - P.α^2 := by nlinarith
    have hD : 0 < 4 - 4*P.α - P.α^2 := by nlinarith
    have hD' : 4 - 4*P.α - P.α^2 ≠ 0 := hD.ne'
    unfold Region1 at n1
    rw [← hr] at n1
    push_neg at n1
    have n1' := n1 hα0 hαlt
    by_cases hrr : r < (4 - 4 * P.α - P.α ^ 2) / (2 - P.α - P.α ^ 2)
    · have h3 := n1' hrr
      have e3 : (1 - P.α) * (vHL P - P.cL) ^ 2 / ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL))
          = (P.cH - P.cL)*((1-P.α)*r^2/(4 - 4 * P.α - P.α ^ 2)) := by
        rw [hx]; field_simp; try ring
      rw [e3, hM] at h3
      have hm := le_of_mul_le_mul_left h3 hΔ
      have h4 : r^2/4 ≤ (1-P.α)*r^2/(4-4*P.α-P.α^2) := by
        rw [div_le_div_iff₀ (by norm_num) hD]; nlinarith [sq_nonneg (P.α*r)]
      refine ⟨fun ξ _ _ => by nlinarith [sq_nonneg (ξ - r/2)], fun ξ1 ξ2 _ _ _ _ => ?_⟩
      have := G_le_int P.α r ξ1 ξ2 hD
      have : 2*(1-P.α)*r^2/(4-4*P.α-P.α^2) = 2*((1-P.α)*r^2/(4-4*P.α-P.α^2)) := by ring
      linarith
    · push_neg at hrr
      have hrE : 4-4*P.α-P.α^2 ≤ r*(2-P.α-P.α^2) := (div_le_iff₀ hE).1 hrr
      have hR1 : 1 ≤ (4-4*P.α-P.α^2)/(2-P.α-P.α^2) := by rw [le_div_iff₀ hE]; nlinarith
      have h1r : 1 ≤ r := by linarith
      refine ⟨big h1r, fun ξ1 ξ2 h1 h1' h2 h2' => ?_⟩
      have := G_le_C P.α r ξ1 ξ2 hα0 hα23 h1 h1' h2 h2' hrE
      linarith
  · have hA := alpha_ge P.α hα0 hαge
    unfold Region2 at n2
    rw [← hr] at n2
    push_neg at n2
    have n2' := n2 hαge hα1
    have hp : 0 < 1 + P.α := by linarith
    by_cases hrr : r < 2 / (1 + P.α)
    · have h3 := n2' hrr
      have e3 : (1 + P.α) ^ 2 * (vHL P - P.cL) ^ 2 / (8 * (P.cH - P.cL))
          = (P.cH - P.cL)*((1+P.α)^2*r^2/8) := by
        rw [hx]; field_simp; try ring
      rw [e3, hM] at h3
      have hm := le_of_mul_le_mul_left h3 hΔ
      have h2' : 0 ≤ (1+P.α)^2 - 2 := by nlinarith
      refine ⟨fun ξ _ _ => by nlinarith [sq_nonneg (ξ - r/2), mul_nonneg h2' (sq_nonneg r)],
        fun ξ1 ξ2 h1 _ h2 _ => ?_⟩
      have := G_le_r2 P.α r ξ1 ξ2 hA hα0 hα1 h1 h2
      linarith
    · push_neg at hrr
      have hr2 : 2 ≤ r*(1+P.α) := (div_le_iff₀ hp).1 hrr
      have hr0 : 0 ≤ r := by nlinarith
      have h1r : 1 ≤ r := by nlinarith [mul_le_mul_of_nonneg_left hα1 hr0]
      refine ⟨big h1r, fun ξ1 ξ2 h1 h1' h2 h2' => ?_⟩
      have := G_le_D P.α r ξ1 ξ2 hA hα0 hα1 h1 h1' h2 h2' hr2
      linarith

set_option maxHeartbeats 1000000 in
theorem clause1 (P : Params) (hcl : P.cL ≤ vHL P) (hR : Region1 P) :
      IsOptimal P (.opaque (vHL P) (vHL P)
        ((2 - P.α - P.α ^ 2) * (vHL P - P.cL) / ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL)))
        ((2 - 3 * P.α - P.α ^ 2) * (vHL P - P.cL) / ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL)))) ∧
      (Policy.opaque (vHL P) (vHL P)
        ((2 - P.α - P.α ^ 2) * (vHL P - P.cL) / ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL)))
        ((2 - 3 * P.α - P.α ^ 2) * (vHL P - P.cL) /
          ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL)))).profit P =
        2 * (1 - P.α) * (vHL P - P.cL) ^ 2 / ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL)) := by
  obtain ⟨r, L, m1, hr, hx, hL, hM, hLm, hrm⟩ := setup P
  have hΔ : 0 < P.cH - P.cL := sub_pos.2 P.hc
  have hΔ' : P.cH - P.cL ≠ 0 := hΔ.ne'
  have hα0 := P.hα0
  have hα1 := P.hα1
  obtain ⟨-, hαlt, h2, h3⟩ := hR
  rw [← hr] at h2
  have hA := alpha_lt P.α hα0 hαlt
  have hα23 : P.α < 2/3 := by nlinarith
  have hE : 0 < 2 - P.α - P.α^2 := by nlinarith
  have hD : 0 < 4 - 4*P.α - P.α^2 := by nlinarith
  have hD' : 4 - 4*P.α - P.α^2 ≠ 0 := hD.ne'
  have hr0 : 0 ≤ r := by
    by_contra h
    push_neg at h
    nlinarith [mul_neg_of_pos_of_neg hΔ h]
  have hrE : r * (2 - P.α - P.α^2) < 4 - 4*P.α - P.α^2 := (lt_div_iff₀ hE).1 h2
  have hαr : P.α * r ≤ 1 := by
    have a1 : P.α * (r * (2 - P.α - P.α^2)) ≤ P.α * (4 - 4*P.α - P.α^2) :=
      mul_le_mul_of_nonneg_left hrE.le hα0
    have a2 : P.α * (4 - 4*P.α - P.α^2) ≤ 2 - P.α - P.α^2 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - P.α) (by linarith : (0:ℝ) ≤ 2 - 3*P.α),
        pow_nonneg hα0 3]
    by_contra h
    push_neg at h
    nlinarith [mul_lt_mul_of_pos_right h hE]
  have e3 : (1 - P.α) * (vHL P - P.cL) ^ 2 / ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL))
      = (P.cH - P.cL)*((1-P.α)*r^2/(4 - 4 * P.α - P.α ^ 2)) := by
    rw [hx]; field_simp; try ring
  rw [e3, hM] at h3
  have hm1 : m1 < (1-P.α)*r^2/(4 - 4 * P.α - P.α ^ 2) := lt_of_mul_lt_mul_left h3 hΔ.le
  have h4 : r^2/4 ≤ (1-P.α)*r^2/(4-4*P.α-P.α^2) := by
    rw [div_le_div_iff₀ (by norm_num) hD]; nlinarith [sq_nonneg (P.α*r)]
  have hq4 : ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 → ξ*(r-ξ) ≤ (1-P.α)*r^2/(4-4*P.α-P.α^2) :=
    fun ξ _ _ => by nlinarith [sq_nonneg (ξ - r/2)]
  have H := fun ξ1 ξ2 (h1 : 0 ≤ ξ1) (h1' : ξ1 ≤ 1) (h2 : 0 ≤ ξ2) (h2' : ξ2 ≤ 1) =>
    combos P.α r L ((1-P.α)*r^2/(4-4*P.α-P.α^2)) (2*(1-P.α)*r^2/(4-4*P.α-P.α^2)) ξ1 ξ2
      hα0 hα1 h1 h1' h2 h2' (G_le_int P.α r ξ1 ξ2 hD) (by linarith) hq4 (Or.inl hαr)
      (le_of_eq (by ring))
  have ea : (2 - P.α - P.α ^ 2) * (vHL P - P.cL) / ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL))
      = (2 - P.α - P.α^2)*r/(4 - 4*P.α - P.α^2) := by
    rw [hx]; field_simp
  have eb : (2 - 3 * P.α - P.α ^ 2) * (vHL P - P.cL) / ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL))
      = (2 - 3 * P.α - P.α^2)*r/(4 - 4*P.α - P.α^2) := by
    rw [hx]; field_simp
  rw [ea, eb]
  have e1 : ∀ ξ, vHL P - cost P ξ = (P.cH - P.cL) * (r - ξ) := by
    intro ξ; unfold cost; linear_combination hx
  have hprof : (Policy.opaque (vHL P) (vHL P) ((2 - P.α - P.α^2)*r/(4 - 4*P.α - P.α^2))
      ((2 - 3 * P.α - P.α^2)*r/(4 - 4*P.α - P.α^2))).profit P
      = (P.cH - P.cL) * (2*(1-P.α)*r^2/(4-4*P.α-P.α^2)) := by
    show opaqueProfit P _ _ _ _ = _
    unfold opaqueProfit
    rw [demand_vHL, demand_vHL, e1, e1]
    have hu : (4 - 4*P.α - P.α^2) * (4 - 4*P.α - P.α^2)⁻¹ = 1 := mul_inv_cancel₀ hD'
    linear_combination (-(P.cH - P.cL)*(2-2*P.α)*r^2*(4 - 4*P.α - P.α^2)⁻¹) * hu
  refine ⟨opt_of P _ ?_ r L _ hx hL H hprof ?_ ?_ ?_, ?_⟩
  · simp only [Policy.Feasible, Set.mem_Icc]
    refine ⟨⟨div_nonneg (mul_nonneg hE.le hr0) hD.le, (div_le_one hD).2 (by nlinarith)⟩,
      ⟨div_nonneg (mul_nonneg (by linarith) hr0) hD.le,
        (div_le_one hD).2 (by nlinarith [mul_nonneg hα0 hr0])⟩, le_rfl⟩
  · exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (sq_nonneg r)) hD.le
  · have : (2*(1-P.α)*r^2/(4-4*P.α-P.α^2))/2 = (1-P.α)*r^2/(4-4*P.α-P.α^2) := by ring
    rw [this]
    have hmx := le_max_left (P.vH - P.cH) (P.vL - P.cL)
    rw [hM] at hmx
    linarith [mul_lt_mul_of_pos_left hm1 hΔ]
  · have : (2*(1-P.α)*r^2/(4-4*P.α-P.α^2))/2 = (1-P.α)*r^2/(4-4*P.α-P.α^2) := by ring
    rw [this]
    have hmx := le_max_right (P.vH - P.cH) (P.vL - P.cL)
    rw [hM] at hmx
    linarith [mul_lt_mul_of_pos_left hm1 hΔ]
  · rw [hprof, hx, eq_div_iff (mul_ne_zero hD' hΔ')]
    have hu : (4 - 4*P.α - P.α^2) * (4 - 4*P.α - P.α^2)⁻¹ = 1 := mul_inv_cancel₀ hD'
    linear_combination (2*(1-P.α)*r^2*(P.cH - P.cL)^2) * hu

set_option maxHeartbeats 1000000 in
theorem clause2 (P : Params) (hcl : P.cL ≤ vHL P) (hR : Region2 P) :
      IsOptimal P (.opaque (vHL P) (vHL P) ((1 + P.α) * (vHL P - P.cL) / (2 * (P.cH - P.cL))) 0) ∧
      (Policy.opaque (vHL P) (vHL P)
        ((1 + P.α) * (vHL P - P.cL) / (2 * (P.cH - P.cL))) 0).profit P =
        (1 + P.α) ^ 2 * (vHL P - P.cL) ^ 2 / (4 * (P.cH - P.cL)) := by
  obtain ⟨r, L, m1, hr, hx, hL, hM, hLm, hrm⟩ := setup P
  have hΔ : 0 < P.cH - P.cL := sub_pos.2 P.hc
  have hΔ' : P.cH - P.cL ≠ 0 := hΔ.ne'
  have hα0 := P.hα0
  have hα1 := P.hα1
  obtain ⟨hαge, -, h2, h3⟩ := hR
  rw [← hr] at h2
  have hA := alpha_ge P.α hα0 hαge
  have hp : 0 < 1 + P.α := by linarith
  have hr0 : 0 ≤ r := by
    by_contra h
    push_neg at h
    nlinarith [mul_neg_of_pos_of_neg hΔ h]
  have hr2 : r * (1 + P.α) < 2 := (lt_div_iff₀ hp).1 h2
  have hαr : P.α * r ≤ 1 := by
    by_contra h
    push_neg at h
    nlinarith [mul_le_mul_of_nonneg_left hr2.le hα0, mul_lt_mul_of_pos_right h hp]
  have e3 : (1 + P.α) ^ 2 * (vHL P - P.cL) ^ 2 / (8 * (P.cH - P.cL))
      = (P.cH - P.cL)*((1+P.α)^2*r^2/8) := by
    rw [hx]; field_simp; try ring
  rw [e3, hM] at h3
  have hm1 : m1 < (1+P.α)^2*r^2/8 := lt_of_mul_lt_mul_left h3 hΔ.le
  have h2' : 0 ≤ (1+P.α)^2 - 2 := by nlinarith
  have hq4 : ∀ ξ : ℝ, 0 ≤ ξ → ξ ≤ 1 → ξ*(r-ξ) ≤ (1+P.α)^2*r^2/8 :=
    fun ξ _ _ => by nlinarith [sq_nonneg (ξ - r/2), mul_nonneg h2' (sq_nonneg r)]
  have H := fun ξ1 ξ2 (h1 : 0 ≤ ξ1) (h1' : ξ1 ≤ 1) (h2 : 0 ≤ ξ2) (h2' : ξ2 ≤ 1) =>
    combos P.α r L ((1+P.α)^2*r^2/8) ((1+P.α)^2*r^2/4) ξ1 ξ2
      hα0 hα1 h1 h1' h2 h2' (G_le_r2 P.α r ξ1 ξ2 hA hα0 hα1 h1 h2) (by linarith) hq4
      (Or.inl hαr) (le_of_eq (by ring))
  have ea : (1 + P.α) * (vHL P - P.cL) / (2 * (P.cH - P.cL)) = (1 + P.α)*r/2 := by
    rw [hx]; field_simp
  rw [ea]
  have e1 : ∀ ξ, vHL P - cost P ξ = (P.cH - P.cL) * (r - ξ) := by
    intro ξ; unfold cost; linear_combination hx
  have hprof : (Policy.opaque (vHL P) (vHL P) ((1 + P.α)*r/2) 0).profit P
      = (P.cH - P.cL) * ((1+P.α)^2*r^2/4) := by
    show opaqueProfit P _ _ _ _ = _
    unfold opaqueProfit
    rw [demand_vHL, demand_vHL, e1, e1]
    ring
  refine ⟨opt_of P _ ?_ r L _ hx hL H hprof ?_ ?_ ?_, ?_⟩
  · simp only [Policy.Feasible, Set.mem_Icc]
    refine ⟨⟨by positivity, by nlinarith⟩, ⟨le_rfl, zero_le_one⟩, le_rfl⟩
  · positivity
  · have : (1+P.α)^2*r^2/4/2 = (1+P.α)^2*r^2/8 := by ring
    rw [this]
    have hmx := le_max_left (P.vH - P.cH) (P.vL - P.cL)
    rw [hM] at hmx
    linarith [mul_lt_mul_of_pos_left hm1 hΔ]
  · have : (1+P.α)^2*r^2/4/2 = (1+P.α)^2*r^2/8 := by ring
    rw [this]
    have hmx := le_max_right (P.vH - P.cH) (P.vL - P.cL)
    rw [hM] at hmx
    linarith [mul_lt_mul_of_pos_left hm1 hΔ]
  · rw [hprof, hx]
    field_simp
    try ring

set_option maxHeartbeats 1000000 in
theorem clause3 (P : Params) (n1 : ¬ Region1 P) (n2 : ¬ Region2 P) :
      (P.vL - P.cL ≤ P.vH - P.cH →
        IsOptimal P (.transparent .H .H P.vH P.vH) ∧
        (Policy.transparent .H .H P.vH P.vH).profit P = 2 * (P.vH - P.cH)) ∧
      (P.vH - P.cH ≤ P.vL - P.cL →
        IsOptimal P (.transparent .L .L P.vL P.vL) ∧
        (Policy.transparent .L .L P.vL P.vL).profit P = 2 * (P.vL - P.cL)) := by
  obtain ⟨r, L, m1, hr, hx, hL, hM, hLm, hrm⟩ := setup P
  have hα0 := P.hα0
  have hα1 := P.hα1
  obtain ⟨hφ, hG⟩ := H_iii P r m1 hr hx hM hrm n1 n2
  have hm0 : 0 ≤ m1 := by have := hφ 0 le_rfl zero_le_one; linarith
  have H := fun ξ1 ξ2 (h1 : 0 ≤ ξ1) (h1' : ξ1 ≤ 1) (h2 : 0 ≤ ξ2) (h2' : ξ2 ≤ 1) =>
    combos P.α r L m1 (2*m1) ξ1 ξ2 hα0 hα1 h1 h1' h2 h2' (hG ξ1 ξ2 h1 h1' h2 h2') hLm hφ
      (Or.inr hrm) le_rfl
  have hH := le_max_left (P.vH - P.cH) (P.vL - P.cL)
  have hLx := le_max_right (P.vH - P.cH) (P.vL - P.cL)
  have hb2 : (P.cH - P.cL) * (2*m1/2) = max (P.vH - P.cH) (P.vL - P.cL) := by rw [hM]; ring
  have pH : (Policy.transparent .H .H P.vH P.vH).profit P = 2 * (P.vH - P.cH) := by
    simp [Policy.profit, transparentProfit, Product.value, Product.unitCost] <;> ring
  have pL : (Policy.transparent .L .L P.vL P.vL).profit P = 2 * (P.vL - P.cL) := by
    simp [Policy.profit, transparentProfit, Product.value, Product.unitCost] <;> ring
  refine ⟨fun h => ⟨opt_of P _ trivial r L (2*m1) hx hL H ?_ (by linarith)
      (by rw [hb2]; exact hH) (by rw [hb2]; exact hLx), pH⟩,
    fun h => ⟨opt_of P _ trivial r L (2*m1) hx hL H ?_ (by linarith)
      (by rw [hb2]; exact hH) (by rw [hb2]; exact hLx), pL⟩⟩
  · rw [pH]
    have := hM
    rw [max_eq_left h] at this
    linarith
  · rw [pL]
    have := hM
    rw [max_eq_right h] at this
    linarith

end HYAux

open HuangYin in
theorem solution (P : Params) :
    (P.cL ≤ vHL P → Region1 P →
      IsOptimal P (.opaque (vHL P) (vHL P)
        ((2 - P.α - P.α ^ 2) * (vHL P - P.cL) / ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL)))
        ((2 - 3 * P.α - P.α ^ 2) * (vHL P - P.cL) / ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL)))) ∧
      (Policy.opaque (vHL P) (vHL P)
        ((2 - P.α - P.α ^ 2) * (vHL P - P.cL) / ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL)))
        ((2 - 3 * P.α - P.α ^ 2) * (vHL P - P.cL) /
          ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL)))).profit P =
        2 * (1 - P.α) * (vHL P - P.cL) ^ 2 / ((4 - 4 * P.α - P.α ^ 2) * (P.cH - P.cL))) ∧
    (P.cL ≤ vHL P → Region2 P →
      IsOptimal P (.opaque (vHL P) (vHL P) ((1 + P.α) * (vHL P - P.cL) / (2 * (P.cH - P.cL))) 0) ∧
      (Policy.opaque (vHL P) (vHL P)
        ((1 + P.α) * (vHL P - P.cL) / (2 * (P.cH - P.cL))) 0).profit P =
        (1 + P.α) ^ 2 * (vHL P - P.cL) ^ 2 / (4 * (P.cH - P.cL))) ∧
    (¬ Region1 P → ¬ Region2 P →
      (P.vL - P.cL ≤ P.vH - P.cH →
        IsOptimal P (.transparent .H .H P.vH P.vH) ∧
        (Policy.transparent .H .H P.vH P.vH).profit P = 2 * (P.vH - P.cH)) ∧
      (P.vH - P.cH ≤ P.vL - P.cL →
        IsOptimal P (.transparent .L .L P.vL P.vL) ∧
        (Policy.transparent .L .L P.vL P.vL).profit P = 2 * (P.vL - P.cL))) := by
  exact ⟨fun hc hR => HYAux.clause1 P hc hR, fun hc hR => HYAux.clause2 P hc hR,
    fun n1 n2 => HYAux.clause3 P n1 n2⟩
