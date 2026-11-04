-- Prove2me | solution 1 for InnovAlloc.Optimal.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T09:35:35.962061+00:00
-- url     : https://prove2.me/submissions/46f029d8-5979-4f61-ba96-fec48937ca08

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Model
import Theorems.Thm_InnovAlloc_Optimal_equations_2_3
import Theorems.Thm_InnovAlloc_Optimal_equation_8
import Theorems.Thm_InnovAlloc_Optimal_equations_10_11

open InnovAlloc.Optimal

namespace IASolT1

noncomputable def F (g b : ℝ) : ℝ := if g * b ≤ 1 then 0 else 1 - 1 / (g * b)
noncomputable def gp (α γ p : ℝ) : ℝ := γ * (α * p + (1 - p))

lemma succ_zero (x : ℝ) : succ 0 x = 0 := by simp [succ]

lemma succ_bounds {b x : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) : 0 ≤ succ b x ∧ succ b x < 1 := by
  unfold succ
  constructor
  · have : Real.exp (-(b * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    linarith
  · have := Real.exp_pos (-(b * x)); linarith

lemma gp_bounds {α γ p : ℝ} (hs : Standing α γ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    0 < gp α γ p ∧ gp α γ p < 1 ∧ gp α γ p ≤ γ := by
  obtain ⟨h1, h2, h3, h4⟩ := hs
  unfold gp
  have : 0 < α * p + (1 - p) := by nlinarith
  have : α * p + (1 - p) ≤ 1 := by nlinarith
  refine ⟨by positivity, by nlinarith, by nlinarith⟩

lemma payoff_eq (α γ bi xi bj xj : ℝ) :
    agentPayoff α γ bi xi bj xj = gp α γ (succ bj xj) * succ bi xi - xi := by
  unfold agentPayoff gp; ring

lemma effortStar_nonneg {g b : ℝ} (hb : 0 < b) : 0 ≤ effortStar g b := by
  unfold effortStar
  split_ifs with h
  · exact le_rfl
  · exact div_nonneg (Real.log_nonneg (by linarith)) hb.le

lemma br_succ {g b x : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (h : ∀ z : ℝ, 0 ≤ z → g * succ b z - z ≤ g * succ b x - x) :
    succ b x = F g b := by
  rcases hb.lt_or_eq with hb | hb
  · have H := equations_2_3 g b hg0 hg1 hb
    have hx' : x = effortStar g b := (H.1 x hx).1 h
    rw [hx', H.2.1]; rfl
  · subst hb; simp [succ_zero, F]

lemma br_exists {g b : ℝ} (hg0 : 0 < g) (hg1 : g < 1) (hb : 0 ≤ b) :
    ∃ x, 0 ≤ x ∧ ∀ z : ℝ, 0 ≤ z → g * succ b z - z ≤ g * succ b x - x := by
  rcases hb.lt_or_eq with hb | hb
  · have H := equations_2_3 g b hg0 hg1 hb
    exact ⟨effortStar g b, effortStar_nonneg hb, (H.1 _ (effortStar_nonneg hb)).2 rfl⟩
  · subst hb; exact ⟨0, le_rfl, fun z hz => by simp [succ_zero]; linarith⟩

lemma eq_succ {α γ b1 b2 x1 x2 : ℝ} (hs : Standing α γ) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (h : IsEquilibrium α γ b1 b2 x1 x2) :
    0 ≤ x1 ∧ 0 ≤ x2 ∧ succ b1 x1 = F (gp α γ (succ b2 x2)) b1 ∧
      succ b2 x2 = F (gp α γ (succ b1 x1)) b2 := by
  obtain ⟨v1, v2, rfl, rfl, h1, h2⟩ := h
  have hx1 := v1.2
  have hx2 := v2.2
  obtain ⟨p20, p21⟩ := succ_bounds hb2 hx2
  obtain ⟨p10, p11⟩ := succ_bounds hb1 hx1
  obtain ⟨g1a, g1b, -⟩ := gp_bounds hs p20 p21
  obtain ⟨g2a, g2b, -⟩ := gp_bounds hs p10 p11
  refine ⟨hx1, hx2, br_succ g1a g1b hb1 hx1 ?_, br_succ g2a g2b hb2 hx2 ?_⟩
  · intro z hz
    have := h1 ⟨z, hz⟩
    simpa [payoff_eq] using this
  · intro z hz
    have := h2 ⟨z, hz⟩
    simpa [payoff_eq] using this

lemma mk_eq {α γ b1 b2 x1 x2 : ℝ} (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2)
    (h1 : ∀ z, 0 ≤ z → gp α γ (succ b2 x2) * succ b1 z - z ≤
      gp α γ (succ b2 x2) * succ b1 x1 - x1)
    (h2 : ∀ z, 0 ≤ z → gp α γ (succ b1 x1) * succ b2 z - z ≤
      gp α γ (succ b1 x1) * succ b2 x2 - x2) :
    IsEquilibrium α γ b1 b2 x1 x2 :=
  ⟨⟨x1, hx1⟩, ⟨x2, hx2⟩, rfl, rfl, fun y => by simpa [payoff_eq] using h1 y.1 y.2,
    fun y => by simpa [payoff_eq] using h2 y.1 y.2⟩

lemma profitMono_F (γ B : ℝ) : profitMono γ B = (1 - γ) * F γ B := by
  unfold profitMono F; split_ifs <;> ring

lemma gp_zero (α γ : ℝ) : gp α γ 0 = γ := by unfold gp; ring

end IASolT1

namespace IASolT1

noncomputable def fD (α u : ℝ) : ℝ := α - 4 * u + Real.sqrt (α ^ 2 + 8 * (1 - α) * u)
def gq (α u : ℝ) : ℝ := 9 * u ^ 2 - 2 * (1 - α) * u + (1 - 2 * α)

lemma sq_arg {α u : ℝ} (hα1 : α ≤ 1) (hα0 : 0 ≤ α) (hu : 0 ≤ u) :
    Real.sqrt (α ^ 2 + 8 * (1 - α) * u) ^ 2 = α ^ 2 + 8 * (1 - α) * u :=
  Real.sq_sqrt (by have : 0 ≤ (1 - α) * u := mul_nonneg (by linarith) hu; nlinarith)

lemma comp1 {α u : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hu : 0 < u) :
    fD α u ≤ 1 - u ↔ 0 ≤ gq α u := by
  have hS := sq_arg hα1 hα0 hu.le
  have hS0 := Real.sqrt_nonneg (α ^ 2 + 8 * (1 - α) * u)
  set S := Real.sqrt (α ^ 2 + 8 * (1 - α) * u)
  unfold fD gq
  constructor
  · intro h
    have h' : S ≤ 1 - α + 3 * u := by linarith
    nlinarith [mul_le_mul h' h' hS0 (by linarith)]
  · intro h
    by_contra hc
    have h' : 1 - α + 3 * u < S := by linarith
    nlinarith [mul_lt_mul'' h' h' (by linarith) (by linarith)]

lemma comp2 {α u : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hu : 0 < u) :
    1 - u ≤ fD α u ↔ gq α u ≤ 0 := by
  have hS := sq_arg hα1 hα0 hu.le
  have hS0 := Real.sqrt_nonneg (α ^ 2 + 8 * (1 - α) * u)
  set S := Real.sqrt (α ^ 2 + 8 * (1 - α) * u)
  unfold fD gq
  constructor
  · intro h
    have h' : 1 - α + 3 * u ≤ S := by linarith
    nlinarith [mul_le_mul h' h' (by linarith) hS0]
  · intro h
    by_contra hc
    have h' : S < 1 - α + 3 * u := by linarith
    nlinarith [mul_self_lt_mul_self hS0 h']

lemma duo_mono {α u v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hu : 0 < u) (huv : u ≤ v)
    (hg : gq α u ≤ 0) : fD α v ≤ fD α u := by
  have hRu := (comp2 hα0 hα1 hu).2 hg
  have hSu := sq_arg hα1 hα0 hu.le
  have hSv := sq_arg hα1 hα0 (hu.le.trans huv)
  have hSu0 := Real.sqrt_nonneg (α ^ 2 + 8 * (1 - α) * u)
  have hSv0 := Real.sqrt_nonneg (α ^ 2 + 8 * (1 - α) * v)
  unfold fD at *
  set Su := Real.sqrt (α ^ 2 + 8 * (1 - α) * u)
  set Sv := Real.sqrt (α ^ 2 + 8 * (1 - α) * v)
  have hSu1 : 1 - α + 3 * u ≤ Su := by linarith
  have hge : Su ≤ Sv := by
    by_contra hc; push_neg at hc
    nlinarith [mul_self_lt_mul_self hSv0 hc, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - α) (by linarith : (0:ℝ) ≤ v - u)]
  by_contra hc
  have h1 : 4 * (v - u) < Sv - Su := by linarith
  have hpos : 0 < Sv + Su := by linarith
  have e : (Sv - Su) * (Sv + Su) = 8 * (1 - α) * (v - u) := by nlinarith
  nlinarith [mul_lt_mul_of_pos_right h1 hpos, mul_nonneg (by linarith : (0:ℝ) ≤ v - u) (by linarith : (0:ℝ) ≤ 1 - α)]

lemma mono_key {α u v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hu : 0 < u) (huv : u ≤ v)
    (hgu : 0 ≤ gq α u) (hgv : gq α v < 0) : fD α v ≤ 1 - u := by
  unfold gq at hgu hgv
  have hd : 0 < α ^ 2 + 16 * α - 8 := by nlinarith [sq_nonneg (9 * v - (1 - α))]
  have hs2 := Real.sq_sqrt hd.le
  have hs0 := Real.sqrt_nonneg (α ^ 2 + 16 * α - 8)
  set s := Real.sqrt (α ^ 2 + 16 * α - 8)
  have fac : ∀ w, 9 * (9 * w ^ 2 - 2 * (1 - α) * w + (1 - 2 * α)) =
      (9 * w - (1 - α) - s) * (9 * w - (1 - α) + s) := fun w => by nlinarith
  have fv := fac v
  have fu := fac u
  -- 9v - (1-α) - s < 0 < 9v - (1-α) + s
  have hv1 : 9 * v - (1 - α) - s < 0 := by
    by_contra hc; push_neg at hc
    nlinarith [mul_nonneg hc (by linarith : (0:ℝ) ≤ 9 * v - (1 - α) + s)]
  have hv2 : 0 < 9 * v - (1 - α) + s := by
    by_contra hc; push_neg at hc
    nlinarith [mul_nonneg_of_nonpos_of_nonpos hv1.le hc]
  have hu1 : 9 * u - (1 - α) - s < 0 := by linarith
  have hu2 : 9 * u - (1 - α) + s ≤ 0 := by
    by_contra hc; push_neg at hc
    nlinarith [mul_neg_of_neg_of_pos hu1 hc]
  set c := (1 - α - s) / 9 with hc
  have hcu : u ≤ c := by rw [hc]; linarith
  have hcv : c ≤ v := by rw [hc]; linarith
  set K := 1 - α + 3 * c with hK
  have hK0 : 0 < K := by rw [hK]; linarith
  have hK2 : K ^ 2 = α ^ 2 + 8 * (1 - α) * c := by
    rw [hK, hc]; nlinarith
  have hSv := sq_arg hα1 hα0 (hu.le.trans huv)
  have hSv0 := Real.sqrt_nonneg (α ^ 2 + 8 * (1 - α) * v)
  unfold fD
  set Sv := Real.sqrt (α ^ 2 + 8 * (1 - α) * v)
  have amgm : 2 * K * Sv ≤ Sv ^ 2 + K ^ 2 := by nlinarith [sq_nonneg (Sv - K)]
  have key : 2 * K * (α - 4 * v + Sv) ≤ 2 * K * (1 - c) := by
    have : 2 * K * (α - 4 * v) + (α ^ 2 + 8 * (1 - α) * v) + K ^ 2 - 2 * K * (1 - c)
        = -24 * c * (v - c) := by rw [hK2, hK]; ring_nf; nlinarith
    have hc0 : 0 ≤ c := hu.le.trans hcu
    nlinarith [mul_nonneg hc0 (by linarith : (0:ℝ) ≤ v - c)]
  have : α - 4 * v + Sv ≤ 1 - c := le_of_mul_le_mul_left key (by linarith)
  linarith

lemma alphaLow_pos : 0 < alphaLow := by
  unfold alphaLow
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have := Real.sqrt_nonneg 2
  nlinarith

lemma regA {α : ℝ} (hα0 : 0 ≤ α) (ha : α ≤ alphaLow) (u : ℝ) : 0 ≤ gq α u := by
  unfold alphaLow at ha
  have h2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have h0 := Real.sqrt_nonneg 2
  have hd : α ^ 2 + 16 * α - 8 ≤ 0 := by
    have : (α - (6 * Real.sqrt 2 - 8)) * (α + 6 * Real.sqrt 2 + 8) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    nlinarith
  unfold gq
  nlinarith [sq_nonneg (9 * u - (1 - α))]

lemma regC {α t : ℝ} (hα : 1 / 2 ≤ α) (hα1 : α ≤ 1) (ht : 0 < t) :
    gq α (1 / t) ≤ 0 ↔ cThreshold α ≤ t := by
  have key : gq α (1 / t) = ((1 - 2 * α) * t ^ 2 - 2 * (1 - α) * t + 9) / t ^ 2 := by
    unfold gq; field_simp; ring
  have ht2 : 0 < t ^ 2 := by positivity
  rw [key, div_le_iff₀ ht2, zero_mul]
  unfold cThreshold
  split_ifs with h
  · subst h; constructor <;> intro h' <;> nlinarith
  · have hα' : 1 / 2 < α := lt_of_le_of_ne hα (Ne.symm h)
    have hd : 0 < α ^ 2 + 16 * α - 8 := by nlinarith
    have hs2 := Real.sq_sqrt hd.le
    have hs0 := Real.sqrt_nonneg (α ^ 2 + 16 * α - 8)
    unfold bandLow
    set s := Real.sqrt (α ^ 2 + 16 * α - 8)
    have hsgt : 1 - α < s := by nlinarith
    set d := 2 * α - 1
    have hdpos : 0 < d := by simp only [d]; linarith
    have e1 : (1 - α - s) / (1 - 2 * α) = (s - (1 - α)) / d := by
      rw [show 1 - 2 * α = -d by simp only [d]; ring, div_neg, ← neg_div]; ring_nf
    rw [e1, div_le_iff₀ hdpos]
    have fac : d * ((1 - 2 * α) * t ^ 2 - 2 * (1 - α) * t + 9) =
        -((d * t + (1 - α) - s) * (d * t + (1 - α) + s)) := by
      simp only [d]; nlinarith
    have hp : 0 < d * t + (1 - α) + s := by nlinarith
    constructor
    · intro h'
      by_contra hc; push_neg at hc
      have hneg : d * t + (1 - α) - s < 0 := by linarith
      nlinarith [mul_neg_of_neg_of_pos hneg hp, mul_nonpos_of_nonneg_of_nonpos hdpos.le h']
    · intro h'
      have hnn : 0 ≤ d * t + (1 - α) - s := by linarith
      have := mul_nonneg hnn hp.le
      nlinarith
end IASolT1
namespace IASolT1

lemma profitMono_nonneg {γ B : ℝ} (hγ1 : γ < 1) : 0 ≤ profitMono γ B := by
  unfold profitMono; split_ifs with h
  · exact le_rfl
  · push_neg at h
    have : 1 / (γ * B) < 1 := by rw [div_lt_one (by linarith)]; exact h
    have : 0 < 1 - γ := by linarith
    nlinarith

lemma profitMono_mono {γ B' B : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) (hB' : 0 < B') (h : B' ≤ B) :
    profitMono γ B' ≤ profitMono γ B := by
  have hm : γ * B' ≤ γ * B := mul_le_mul_of_nonneg_left h hγ.le
  unfold profitMono
  split_ifs with h1 h2 h2
  · exact le_rfl
  · have := profitMono_nonneg (B := B) hγ1
    unfold profitMono at this; rwa [if_neg h2] at this
  · exfalso; linarith
  · have : 1 / (γ * B) ≤ 1 / (γ * B') := one_div_le_one_div_of_le (by positivity) hm
    nlinarith

lemma profitDuo_eq {α γ B : ℝ} (h : 2 < γ * B) :
    profitDuo α γ B = (1 - γ) * fD α (1 / (γ * B)) := by
  unfold profitDuo fD
  rw [if_neg (by linarith)]
  have hne : γ * B ≠ 0 := by intro h'; rw [h'] at h; linarith
  have hγn : γ ≠ 0 := left_ne_zero_of_mul hne
  have hBn : B ≠ 0 := right_ne_zero_of_mul hne
  congr 2
  · ring
  · congr 1; field_simp; ring

lemma profitMono_eq {γ B : ℝ} (h : 1 < γ * B) :
    profitMono γ B = (1 - γ) * (1 - 1 / (γ * B)) := by
  unfold profitMono; rw [if_neg (by linarith)]

end IASolT1

namespace IAP1

/-- a ≥ 1/2 : the combination E is nonpositive. -/
lemma E_nonpos {t m P : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1/2) (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (hP : 0 ≤ P) (hP1 : P ≤ 1) :
    8*P^2*t^4*(P - 1) - P*m*t*(-2*P + 6*m + 5) - 4*P*t^3*(-2*P^2 + 6*P*m + P - m + 1)
      + P*t^2*(2*P^2 - 8*P*m + 18*m^2 - 15*m - 2) + m*(2*P*m - P - 4*m)/4 ≤ 0 := by
  have h1 : 0 ≤ 2*P*(1-P)*t^2*(2*t+1)*(2*P*t+P+1) := by
    have : 0 ≤ 1 - P := by linarith
    have : 0 ≤ 2*P*t+P+1 := by positivity
    positivity
  have hc : 0 ≤ P*(1-2*m) + 4*m := by nlinarith
  have hR : 0 ≤ 4*P*(6*P-1)*t^3 + P*(15+8*P-18*m)*t^2 + P*(5+6*m-2*P)*t + (P*(1-2*m)+4*m)/4 := by
    have ht2 : t^2 ≤ t/2 := by nlinarith
    have ht3 : t^3 ≤ t/4 := by nlinarith
    have a1 : -(P*t) ≤ 4*P*(6*P-1)*t^3 := by
      have : 4*P*(6*P-1)*t^3 ≥ -4*P*t^3 := by
        have : 0 ≤ 24*P^2*t^3 := by positivity
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left ht3 hP]
    have a2 : -(3/2)*(P*t) ≤ P*(15+8*P-18*m)*t^2 := by
      have : P*(15+8*P-18*m)*t^2 ≥ -3*P*t^2 := by
        have : 0 ≤ P*(18 + 8*P - 18*m)*t^2 := by
          have : 0 ≤ 18 + 8*P - 18*m := by linarith
          positivity
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left ht2 hP]
    have a3 : 3*(P*t) ≤ P*(5+6*m-2*P)*t := by
      have : 0 ≤ P*(2+6*m-2*P)*t := by
        have : 0 ≤ 2+6*m-2*P := by linarith
        positivity
      nlinarith
    have : 0 ≤ P*t := mul_nonneg hP ht0
    nlinarith
  have key : 8*P^2*t^4*(P - 1) - P*m*t*(-2*P + 6*m + 5) - 4*P*t^3*(-2*P^2 + 6*P*m + P - m + 1)
      + P*t^2*(2*P^2 - 8*P*m + 18*m^2 - 15*m - 2) + m*(2*P*m - P - 4*m)/4
      = -(2*P*(1-P)*t^2*(2*t+1)*(2*P*t+P+1)) - m*(4*P*(6*P-1)*t^3 + P*(15+8*P-18*m)*t^2
          + P*(5+6*m-2*P)*t + (P*(1-2*m)+4*m)/4) := by ring
  rw [key]
  nlinarith [mul_nonneg hm hR]

/-- a ≤ 9/20 : M ≤ 0. Here s = x + y and P = (1-x)(1-y). -/
lemma M_nonpos_low {a s P : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 9/20) (hP : 0 ≤ P)
    (hPs : 1 - s ≤ P) (hPu : 4 * P ≤ (2 - s)^2) (hs : s ≤ 2) (hs0 : 0 ≤ s) :
    -(s-1)^2 - (1-a)*(4-a)*(s-1)*P - 3*(1-a)^2*P^2 - a*(1-2*a)*P ≤ 0 := by
  have hq : 0 ≤ a*(1-2*a) := mul_nonneg ha0 (by linarith)
  have h4 : 0 ≤ (1-a)*(4-a) := mul_nonneg (by linarith) (by linarith)
  rcases le_or_gt 1 s with h | h
  · have : 0 ≤ (s-1)*P := mul_nonneg (by linarith) hP
    nlinarith [mul_nonneg h4 this, mul_nonneg hq hP, sq_nonneg ((1-a)*P)]
  · set k := 1 - s with hk
    set w := P - k with hw
    have hk0 : 0 < k := by rw [hk]; linarith
    have hw0 : 0 ≤ w := by rw [hw]; linarith
    have hwu : w ≤ (1-k)^2/4 := by rw [hw, hk]; nlinarith
    have hk1 : k ≤ 1 := by rw [hk]; linarith
    have expand : -(s-1)^2 - (1-a)*(4-a)*(s-1)*P - 3*(1-a)^2*P^2 - a*(1-2*a)*P
        = a*(1-2*a)*k*(k-1) + ((1-a)*k*(5*a-2) - a*(1-2*a))*w - 3*(1-a)^2*w^2 := by
      have hs' : s = 1 - k := by rw [hk]; ring
      have hP' : P = w + k := by rw [hw]; ring
      rw [hs', hP']; ring
    rw [expand]
    have hMk : a*(1-2*a)*k*(k-1) ≤ 0 := by
      have : 0 ≤ a*(1-2*a)*k*(1-k) := by
        have := mul_nonneg hq hk0.le
        exact mul_nonneg this (by linarith)
      nlinarith
    have hw2 : 0 ≤ 3*(1-a)^2*w^2 := by positivity
    rcases le_or_gt ((1-a)*k*(5*a-2) - a*(1-2*a)) 0 with hd | hd
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hd hw0]
    · have h5 : 0 ≤ 5*a - 2 := by
        by_contra hc; push_neg at hc
        have : (1-a)*k*(5*a-2) ≤ 0 := by
          have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - a) hk0.le
          nlinarith
        linarith
      have hstep : ((1-a)*k*(5*a-2) - a*(1-2*a))*w ≤ ((1-a)*k*(5*a-2) - a*(1-2*a))*((1-k)^2/4) :=
        mul_le_mul_of_nonneg_left hwu hd.le
      have hfin : a*(1-2*a)*k*(k-1) + ((1-a)*k*(5*a-2) - a*(1-2*a))*((1-k)^2/4) ≤ 0 := by
        have e : a*(1-2*a)*k*(k-1) + ((1-a)*k*(5*a-2) - a*(1-2*a))*((1-k)^2/4)
            = (1-k)/4 * (((1-a)*(5*a-2)*k - a*(1-2*a))*(1-k) - 4*a*(1-2*a)*k) := by ring
        rw [e]
        have hin : ((1-a)*(5*a-2)*k - a*(1-2*a))*(1-k) - 4*a*(1-2*a)*k ≤ 0 := by
          nlinarith [mul_nonneg h5 hk0.le, mul_nonneg (mul_nonneg h5 hk0.le) (by linarith : (0:ℝ) ≤ 1 - k),
            mul_nonneg (sub_nonneg.2 ha1) hk0.le, mul_nonneg (mul_nonneg (sub_nonneg.2 ha1) hk0.le) (by linarith : (0:ℝ) ≤ 1 - k),
            mul_nonneg hk0.le (by linarith : (0:ℝ) ≤ 1 - k), mul_nonneg (mul_nonneg h5 h5) hk0.le]
        exact mul_nonpos_of_nonneg_of_nonpos (by linarith) hin
      nlinarith

noncomputable def Wf (a s m : ℝ) : ℝ :=
  4*(1-a)^4*m*(1-s) - 4*a*(2*a^3*s - a^3 - 5*a^2*s + 3*a^2 + 4*a*s - a - s)*(1-s)
    + a*((5*a^2*s - 3*a^2 - 7*a*s + 6*a + 2*s - 2) - 3*(1-a)^2*m)*(2*a+s-2*a*s)

lemma W_nonpos {a s m : ℝ} (ha0 : 9/20 ≤ a) (ha1 : a ≤ 1/2) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hm0 : 0 ≤ m) (hm1 : m ≤ s^2/4) : Wf a s m ≤ 0 := by
  have hW0 : -a*(2*a^3*s^2 - 4*a^3*s + 2*a^3 + a^2*s^2 - 3*a^2*s - 5*a*s^2 + 6*a*s + 2*s^2 - 2*s) ≤ 0 := by
    have hv : 0 ≤ 1 - s := by linarith
    have he : 0 ≤ 1/2 - a := by linarith
    have hp : 0 ≤ 2*a^3*s^2 - 4*a^3*s + 2*a^3 + a^2*s^2 - 3*a^2*s - 5*a*s^2 + 6*a*s + 2*s^2 - 2*s := by
      nlinarith [mul_nonneg hv (sub_nonneg.2 ha0), mul_nonneg he (by linarith : (0:ℝ) ≤ a), mul_nonneg he (sq_nonneg (1-s)),
        mul_nonneg (mul_nonneg (sq_nonneg (1/2-a)) (sq_nonneg (1-s))) (by linarith : (0:ℝ) ≤ a + 1/2), mul_nonneg (mul_nonneg he he) hv]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ a) hp]
  have hWq : (a*s - 2*a - s)*(2*a^3*s^2 - 6*a^3*s + 4*a^3 + 3*a^2*s^2 - 8*a^2*s - 9*a*s^2 + 12*a*s + 4*s^2 - 4*s)/4 ≤ 0 := by
    have h1 : 0 ≤ s * (1 - s) := mul_nonneg hs0 (by linarith)
    have hneg : a*s - 2*a - s ≤ 0 := by nlinarith
    have : 0 ≤ 2*a^3*s^2 - 6*a^3*s + 4*a^3 + 3*a^2*s^2 - 8*a^2*s - 9*a*s^2 + 12*a*s + 4*s^2 - 4*s := by
      nlinarith [mul_nonneg h1 (sub_nonneg.2 ha0), mul_nonneg h1 (sub_nonneg.2 ha1), mul_nonneg (mul_nonneg h1 (sub_nonneg.2 ha0)) (sub_nonneg.2 ha1),
      mul_nonneg (sq_nonneg (1-s)) (sub_nonneg.2 ha0), mul_nonneg (sq_nonneg (1-s)) (sub_nonneg.2 ha1)]
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hneg this]
  have hsplit : Wf a s m = -a*(2*a^3*s^2 - 4*a^3*s + 2*a^3 + a^2*s^2 - 3*a^2*s - 5*a*s^2 + 6*a*s + 2*s^2 - 2*s)
      + m * ((1-a)^2*(2*a^2*s - 2*a^2 + 5*a*s - 8*a - 4*s + 4)) := by unfold Wf; ring
  have hq : -a*(2*a^3*s^2 - 4*a^3*s + 2*a^3 + a^2*s^2 - 3*a^2*s - 5*a*s^2 + 6*a*s + 2*s^2 - 2*s)
      + s^2/4 * ((1-a)^2*(2*a^2*s - 2*a^2 + 5*a*s - 8*a - 4*s + 4))
      = (a*s - 2*a - s)*(2*a^3*s^2 - 6*a^3*s + 4*a^3 + 3*a^2*s^2 - 8*a^2*s - 9*a*s^2 + 12*a*s + 4*s^2 - 4*s)/4 := by ring
  rw [hsplit]
  rcases le_or_gt ((1-a)^2*(2*a^2*s - 2*a^2 + 5*a*s - 8*a - 4*s + 4)) 0 with hc | hc
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos hm0 hc]
  · nlinarith [mul_le_mul_of_nonneg_right hm1 hc.le]

noncomputable def Mf (a s m : ℝ) : ℝ :=
  -a*s*(2*a - 1)*(s - 1) - 3*m^2*(a - 1)^2 + m*(5*a^2*s - 3*a^2 - 7*a*s + 6*a + 2*s - 2)
noncomputable def Kf (a s m : ℝ) : ℝ :=
  a^2*s*(2*a - 1)*(2*a*s - 2*a - s) - 4*a*m*(2*a^3*s - a^3 - 5*a^2*s + 3*a^2 + 4*a*s - a - s)
    + 4*m^2*(a - 1)^4

lemma key {a x y : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : Mf a (x+y) (x*y) ≤ 0 ∨ Kf a (x+y) (x*y) ≤ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨hM, hK⟩ := hc
  have hm0 : 0 ≤ x*y := mul_nonneg hx0 hy0
  have hP0 : 0 ≤ (1-x)*(1-y) := mul_nonneg (by linarith) (by linarith)
  have hM2 : Mf a (x+y) (x*y) = -((x+y)-1)^2 - (1-a)*(4-a)*((x+y)-1)*((1-x)*(1-y))
      - 3*(1-a)^2*((1-x)*(1-y))^2 - a*(1-2*a)*((1-x)*(1-y)) := by unfold Mf; ring
  rcases le_or_gt (1/2) a with h12 | h12
  · have hE := E_nonpos (t := a - 1/2) (m := x*y) (P := (1-x)*(1-y)) (by linarith) (by linarith) hm0
      (by nlinarith) hP0 (by nlinarith)
    have hid : Mf a (x+y) (x*y) + 2*((1-x)*(1-y))*Kf a (x+y) (x*y) =
      8*((1-x)*(1-y))^2*(a-1/2)^4*(((1-x)*(1-y)) - 1) - ((1-x)*(1-y))*(x*y)*(a-1/2)*(-2*((1-x)*(1-y)) + 6*(x*y) + 5)
      - 4*((1-x)*(1-y))*(a-1/2)^3*(-2*((1-x)*(1-y))^2 + 6*((1-x)*(1-y))*(x*y) + ((1-x)*(1-y)) - (x*y) + 1)
      + ((1-x)*(1-y))*(a-1/2)^2*(2*((1-x)*(1-y))^2 - 8*((1-x)*(1-y))*(x*y) + 18*(x*y)^2 - 15*(x*y) - 2)
      + (x*y)*(2*((1-x)*(1-y))*(x*y) - ((1-x)*(1-y)) - 4*(x*y))/4 := by unfold Mf Kf; ring
    nlinarith [mul_nonneg hP0 hK.le]
  rcases le_or_gt a (9/20) with hlo | hlo
  · have := M_nonpos_low (s := x+y) (P := (1-x)*(1-y)) ha0 hlo hP0 (by nlinarith) (by nlinarith [sq_nonneg (x-y)])
      (by linarith) (by linarith)
    linarith
  rcases le_or_gt 1 (x+y) with hs | hs
  · have h1 : 0 ≤ (1-a)*(4-a)*((x+y)-1)*((1-x)*(1-y)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) hP0
    have h2 : 0 ≤ a*(1-2*a)*((1-x)*(1-y)) := mul_nonneg (mul_nonneg ha0 (by linarith)) hP0
    nlinarith [sq_nonneg ((x+y)-1), sq_nonneg ((1-a)*((1-x)*(1-y)))]
  · have hW := W_nonpos (s := x+y) (m := x*y) hlo.le h12.le (by linarith) hs.le hm0 (by nlinarith [sq_nonneg (x-y)])
    have hid : Kf a (x+y) (x*y) * (1-(x+y)) + a*(2*a+(x+y)-2*a*(x+y))*Mf a (x+y) (x*y)
        = (x*y) * Wf a (x+y) (x*y) := by unfold Kf Mf Wf; ring
    have hpos : 0 < a*(2*a+(x+y)-2*a*(x+y)) := by
      have : 0 < 2*a+(x+y)-2*a*(x+y) := by nlinarith
      exact mul_pos (by linarith) this
    nlinarith [mul_pos hpos hM, mul_pos hK (by linarith : (0:ℝ) < 1 - (x+y)), mul_nonpos_of_nonneg_of_nonpos hm0 hW]

end IAP1
namespace IASolT1

lemma both_bound {α x y : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hy0 : 0 < y) (hy1 : y ≤ 1) :
    2*α*(1-x)*(1-y) + (1-x)*y + (1-y)*x ≤
        1 - 1 / (1 / (x*(α+(1-α)*y)) + 1 / (y*(α+(1-α)*x))) ∨
    2*α*(1-x)*(1-y) + (1-x)*y + (1-y)*x ≤
        fD α (1 / (1 / (x*(α+(1-α)*y)) + 1 / (y*(α+(1-α)*x)))) := by
  have hA1 : 0 < α + (1-α)*y := by nlinarith
  have hA2 : 0 < α + (1-α)*x := by nlinarith
  set w1 := x*(α+(1-α)*y) with hw1
  set w2 := y*(α+(1-α)*x) with hw2
  have hw1p : 0 < w1 := mul_pos hx0 hA1
  have hw2p : 0 < w2 := mul_pos hy0 hA2
  set Φ := 2*α*(1-x)*(1-y) + (1-x)*y + (1-y)*x with hΦ
  set S := w1 + w2 with hS
  set U := w1 * w2 with hU
  have hSp : 0 < S := by rw [hS]; linarith
  have hu : 1 / (1 / w1 + 1 / w2) = U / S := by
    rw [hU, hS]; field_simp; ring
  rw [hu]
  have hMid : (Φ - 1) * S + U = IAP1.Mf α (x+y) (x*y) := by
    rw [hΦ, hS, hU, hw1, hw2]; unfold IAP1.Mf; ring
  have hNid : ((Φ - α) * S + 4 * U)^2 - (α^2 * S^2 + 8 * (1-α) * U * S)
      = (x - y)^2 * IAP1.Kf α (x+y) (x*y) := by
    rw [hΦ, hS, hU, hw1, hw2]; unfold IAP1.Kf; ring
  rcases IAP1.key hα0 hα1 hx0.le hx1 hy0.le hy1 with hM | hK
  · left
    have e : Φ - (1 - U / S) = ((Φ - 1) * S + U) / S := by field_simp; ring
    have : ((Φ - 1) * S + U) / S ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by rw [hMid]; exact hM) hSp.le
    linarith
  · right
    unfold fD
    set u := U / S with hudef
    have hsq : (Φ - α + 4 * u)^2 ≤ α^2 + 8*(1-α)*u := by
      have hN : ((Φ - α) * S + 4 * U)^2 - (α^2 * S^2 + 8 * (1-α) * U * S) ≤ 0 := by
        rw [hNid]; exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hK
      have e : (Φ - α + 4 * u)^2 - (α^2 + 8*(1-α)*u) =
          (((Φ - α) * S + 4 * U)^2 - (α^2 * S^2 + 8 * (1-α) * U * S)) / S^2 := by
        rw [hudef]; field_simp; (try ring)
      have : (((Φ - α) * S + 4 * U)^2 - (α^2 * S^2 + 8 * (1-α) * U * S)) / S^2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hN (sq_nonneg _)
      linarith
    have : Φ - α + 4 * u ≤ Real.sqrt (α^2 + 8*(1-α)*u) := by
      calc Φ - α + 4 * u ≤ |Φ - α + 4 * u| := le_abs_self _
        _ = Real.sqrt ((Φ - α + 4 * u)^2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (α^2 + 8*(1-α)*u) := Real.sqrt_le_sqrt hsq
    linarith

theorem prop1 (α γ B : ℝ) (hs : Standing α γ) (hB : 0 < B)
    (b2 : ℝ) (hb2 : 0 ≤ b2) (hb2B : b2 ≤ B / 2)
    (x1 x2 : ℝ) (heq : IsEquilibrium α γ (B - b2) b2 x1 x2) :
    (∃ z1 z2, IsEquilibrium α γ B 0 z1 z2 ∧
      principalProfit α γ (B - b2) b2 x1 x2 ≤
        principalProfit α γ B 0 z1 z2) ∨
    (∃ z1 z2, IsEquilibrium α γ (B / 2) (B / 2) z1 z2 ∧
      principalProfit α γ (B - b2) b2 x1 x2 ≤
        principalProfit α γ (B / 2) (B / 2) z1 z2) := by
  have hs' := hs
  obtain ⟨hγ0, hγ1, hα0, hα1⟩ := hs'
  have hb1 : 0 < B - b2 := by linarith
  obtain ⟨⟨z1, z2, hz⟩, E8val⟩ := equation_8 α γ B hs hB
  have hzval := E8val z1 z2 hz
  have L : principalProfit α γ (B - b2) b2 x1 x2 ≤ profitMono γ B →
      (∃ z1 z2, IsEquilibrium α γ B 0 z1 z2 ∧
        principalProfit α γ (B - b2) b2 x1 x2 ≤ principalProfit α γ B 0 z1 z2) ∨
      (∃ z1 z2, IsEquilibrium α γ (B / 2) (B / 2) z1 z2 ∧
        principalProfit α γ (B - b2) b2 x1 x2 ≤ principalProfit α γ (B / 2) (B / 2) z1 z2) :=
    fun h => Or.inl ⟨z1, z2, hz, by rw [hzval]; exact h⟩
  obtain ⟨hx1, hx2, e1, e2⟩ := eq_succ hs hb1.le hb2 heq
  have hprof : principalProfit α γ (B - b2) b2 x1 x2 =
      (1 - γ) * (2 * α * succ (B - b2) x1 * succ b2 x2 + succ (B - b2) x1 * (1 - succ b2 x2)
        + succ b2 x2 * (1 - succ (B - b2) x1)) := rfl
  obtain ⟨p10, p11⟩ := succ_bounds hb1.le hx1
  obtain ⟨p20, p21⟩ := succ_bounds hb2 hx2
  set p1 := succ (B - b2) x1 with hp1def
  set p2 := succ b2 x2 with hp2def
  have hγ' : 0 < 1 - γ := by linarith
  by_cases hp2 : p2 = 0
  · apply L
    rw [hp2, gp_zero] at e1
    rw [hprof, hp2]
    have : (1 - γ) * (2 * α * p1 * 0 + p1 * (1 - 0) + 0 * (1 - p1)) = profitMono γ (B - b2) := by
      rw [profitMono_F, ← e1]; ring
    rw [this]; exact profitMono_mono hγ0 hγ1 hb1 (by linarith)
  by_cases hp1 : p1 = 0
  · apply L
    rw [hp1, gp_zero] at e2
    rw [hprof, hp1]
    have hb2p : 0 < b2 := by
      rcases hb2.lt_or_eq with h | h
      · exact h
      · exfalso; apply hp2; rw [hp2def, ← h, succ_zero]
    have : (1 - γ) * (2 * α * 0 * p2 + 0 * (1 - p2) + p2 * (1 - 0)) = profitMono γ b2 := by
      rw [profitMono_F, ← e2]; ring
    rw [this]; exact profitMono_mono hγ0 hγ1 hb2p (by linarith)
  -- both agents active
  obtain ⟨g1a, -, g1c⟩ := gp_bounds hs p20 p21
  obtain ⟨g2a, -, g2c⟩ := gp_bounds hs p10 p11
  unfold F at e1 e2
  split_ifs at e1 with A1
  · exact absurd e1 hp1
  split_ifs at e2 with A2
  · exact absurd e2 hp2
  push_neg at A1 A2
  set x := 1 - p1 with hx
  set y := 1 - p2 with hy
  have hx0 : 0 < x := by rw [hx]; linarith
  have hy0 : 0 < y := by rw [hy]; linarith
  have hx1' : x ≤ 1 := by rw [hx]; linarith
  have hy1' : y ≤ 1 := by rw [hy]; linarith
  have hg1 : gp α γ p2 = γ * (α + (1 - α) * y) := by rw [hy]; unfold gp; ring
  have hg2 : gp α γ p1 = γ * (α + (1 - α) * x) := by rw [hx]; unfold gp; ring
  have hne1 : gp α γ p2 * (B - b2) ≠ 0 := by linarith
  have hne2 : gp α γ p1 * b2 ≠ 0 := by linarith
  have hAy : 0 < α + (1 - α) * y := by nlinarith
  have hAx : 0 < α + (1 - α) * x := by nlinarith
  have k1 : x * (α + (1 - α) * y) * (γ * (B - b2)) = 1 := by
    have : x = 1 / (γ * (α + (1 - α) * y) * (B - b2)) := by rw [← hg1, hx]; linarith
    rw [this]
    have := hAy.ne'; have := hγ0.ne'; have := hb1.ne'
    field_simp
  have k2 : y * (α + (1 - α) * x) * (γ * b2) = 1 := by
    have : y = 1 / (γ * (α + (1 - α) * x) * b2) := by rw [← hg2, hy]; linarith
    rw [this]
    have hb2n : b2 ≠ 0 := by intro h0; rw [h0] at hne2; simp at hne2
    have := hAx.ne'; have := hγ0.ne'
    field_simp
  have hT1 : 1 < γ * (B - b2) := by nlinarith
  have hT2 : 1 < γ * b2 := by nlinarith
  have hTB : γ * B = 1 / (x * (α + (1 - α) * y)) + 1 / (y * (α + (1 - α) * x)) := by
    have e1' : 1 / (x * (α + (1 - α) * y)) = γ * (B - b2) := by
      rw [eq_comm, eq_div_iff (by intro h0; rw [h0] at k1; linarith)]; linarith
    have e2' : 1 / (y * (α + (1 - α) * x)) = γ * b2 := by
      rw [eq_comm, eq_div_iff (by intro h0; rw [h0] at k2; linarith)]; linarith
    rw [e1', e2']; ring
  have h2B : 2 < γ * B := by
    have : γ * B = γ * (B - b2) + γ * b2 := by ring
    linarith
  have hpr : principalProfit α γ (B - b2) b2 x1 x2 =
      (1 - γ) * (2*α*(1-x)*(1-y) + (1-x)*y + (1-y)*x) := by
    rw [hprof, hx, hy]; ring
  rcases both_bound hα0 hα1 hx0 hx1' hy0 hy1' with h | h
  · apply L
    rw [hpr, profitMono_eq (by linarith), hTB]
    exact mul_le_mul_of_nonneg_left h hγ'.le
  · right
    obtain ⟨w1, w2, hw, -, -, hval⟩ := (equations_10_11 α γ B hs h2B).1
    refine ⟨w1, w2, hw, ?_⟩
    rw [hval, profitDuo_eq h2B, hpr, hTB]
    exact mul_le_mul_of_nonneg_left h hγ'.le

end IASolT1

open InnovAlloc.Optimal in
theorem solution (α γ B : ℝ) (hs : Standing α γ) (hB : 0 < B)
    (b2 : ℝ) (hb2 : 0 ≤ b2) (hb2B : b2 ≤ B / 2)
    (x1 x2 : ℝ) (heq : IsEquilibrium α γ (B - b2) b2 x1 x2) :
    (∃ z1 z2, IsEquilibrium α γ B 0 z1 z2 ∧
      principalProfit α γ (B - b2) b2 x1 x2 ≤
        principalProfit α γ B 0 z1 z2) ∨
    (∃ z1 z2, IsEquilibrium α γ (B / 2) (B / 2) z1 z2 ∧
      principalProfit α γ (B - b2) b2 x1 x2 ≤
        principalProfit α γ (B / 2) (B / 2) z1 z2) :=
  IASolT1.prop1 α γ B hs hB b2 hb2 hb2B x1 x2 heq
