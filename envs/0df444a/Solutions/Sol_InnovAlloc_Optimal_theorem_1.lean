-- Prove2me | solution 1 for InnovAlloc.Optimal.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T09:01:20.370436+00:00
-- url     : https://prove2.me/submissions/532a1886-9480-463d-a0af-34986fca534f

import Mathlib
import Definitions.Def_InnovAlloc_Optimal_Model
import Theorems.Thm_InnovAlloc_Optimal_equations_2_3
import Theorems.Thm_InnovAlloc_Optimal_equation_8
import Theorems.Thm_InnovAlloc_Optimal_equations_10_11
import Theorems.Thm_InnovAlloc_Optimal_proposition_1
import Theorems.Thm_InnovAlloc_Optimal_prop3_region_b

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

lemma eq_swap {α γ b1 b2 x1 x2 : ℝ} (h : IsEquilibrium α γ b1 b2 x1 x2) :
    IsEquilibrium α γ b2 b1 x2 x1 := by
  obtain ⟨v1, v2, e1, e2, h1, h2⟩ := h
  exact ⟨v2, v1, e2, e1, h2, h1⟩

lemma profit_swap (α γ b1 b2 x1 x2 : ℝ) :
    principalProfit α γ b1 b2 x1 x2 = principalProfit α γ b2 b1 x2 x1 := by
  unfold principalProfit; ring

lemma F_zero {g b γ : ℝ} (hg : 0 < g) (hgγ : g ≤ γ) (hb : 0 ≤ b) (h : γ * b ≤ 1) :
    F g b = 0 := by
  unfold F; rw [if_pos (by nlinarith)]

lemma profit_zero {α γ b1 b2 x1 x2 : ℝ} (hs : Standing α γ) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2)
    (h1 : γ * b1 ≤ 1) (h2 : γ * b2 ≤ 1) (h : IsEquilibrium α γ b1 b2 x1 x2) :
    principalProfit α γ b1 b2 x1 x2 = 0 := by
  obtain ⟨hx1, hx2, e1, e2⟩ := eq_succ hs hb1 hb2 h
  obtain ⟨p10, p11⟩ := succ_bounds hb1 hx1
  obtain ⟨p20, p21⟩ := succ_bounds hb2 hx2
  obtain ⟨g1a, -, g1c⟩ := gp_bounds hs p20 p21
  obtain ⟨g2a, -, g2c⟩ := gp_bounds hs p10 p11
  have z1 : succ b1 x1 = 0 := by rw [e1]; exact F_zero g1a g1c hb1 h1
  have z2 : succ b2 x2 = 0 := by rw [e2]; exact F_zero g2a g2c hb2 h2
  unfold principalProfit; rw [z1, z2]; ring

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

lemma sym_alpha0 {γ c z1 z2 : ℝ} (hs : Standing 0 γ) (hc : 0 < c)
    (h : IsEquilibrium 0 γ c c z1 z2) : principalProfit 0 γ c c z1 z2 ≤ profitMono γ c := by
  obtain ⟨hx1, hx2, e1, e2⟩ := eq_succ hs hc.le hc.le h
  obtain ⟨p10, p11⟩ := succ_bounds hc.le hx1
  obtain ⟨p20, p21⟩ := succ_bounds hc.le hx2
  obtain ⟨hγ0, hγ1, -, -⟩ := hs
  have hγ' : (0:ℝ) < 1 - γ := by linarith
  have hmn := profitMono_nonneg (B := c) hγ1
  unfold principalProfit
  set p1 := succ c z1
  set p2 := succ c z2
  have g0 : ∀ p, gp 0 γ p = γ * (1 - p) := fun p => by unfold gp; ring
  rw [g0] at e1 e2
  unfold F at e1 e2
  split_ifs at e1 with A1 <;> split_ifs at e2 with A2
  · rw [e1, e2]; simpa using hmn
  · -- p1 = 0
    rw [e1] at A2 e2 ⊢
    rw [profitMono_F]
    simp only [sub_zero, mul_one] at A2 e2 ⊢
    unfold F; rw [if_neg A2, ← e2]; ring_nf; nlinarith
  · rw [e2] at A1 e1 ⊢
    rw [profitMono_F]
    simp only [sub_zero, mul_one] at A1 e1 ⊢
    unfold F; rw [if_neg A1, ← e1]; ring_nf; nlinarith
  · push_neg at A1 A2
    have hgc : 1 < γ * c := by nlinarith
    have hne2 : (1 - p2) ≠ 0 := by intro h0; linarith
    have hne3 : γ * (1 - p2) * c ≠ 0 := by intro h0; linarith
    have k1 : (1 - p1) * (γ * (1 - p2) * c) = 1 := by
      rw [e1]; field_simp; ring
    unfold profitMono; rw [if_neg (by linarith)]
    have hk : 1 / (γ * c) = (1 - p1) * (1 - p2) := by
      field_simp; nlinarith
    rw [hk]
    have : p1 * (1 - p2) + p2 * (1 - p1) ≤ 1 - (1 - p1) * (1 - p2) := by nlinarith [mul_nonneg p10 p20]
    nlinarith

lemma optimal_of {α γ Bbar b1 b2 V : ℝ} (hs : Standing α γ)
    (hfeas : Feasible Bbar b1 b2)
    (hex : ∃ x1 x2, IsEquilibrium α γ b1 b2 x1 x2)
    (hval : ∀ x1 x2, IsEquilibrium α γ b1 b2 x1 x2 → principalProfit α γ b1 b2 x1 x2 = V)
    (hV0 : 0 ≤ V)
    (hV1 : ∀ B', 0 < B' → B' ≤ Bbar → profitMono γ B' ≤ V)
    (hV2 : ∀ B', 0 < B' → B' ≤ Bbar → ∀ z1 z2, IsEquilibrium α γ (B' / 2) (B' / 2) z1 z2 →
      principalProfit α γ (B' / 2) (B' / 2) z1 z2 ≤ V) :
    IsOptimal α γ Bbar b1 b2 := by
  have bound : ∀ c1 c2, c2 ≤ c1 → Feasible Bbar c1 c2 → ∀ z1 z2,
      IsEquilibrium α γ c1 c2 z1 z2 → principalProfit α γ c1 c2 z1 z2 ≤ V := by
    intro c1 c2 hle hc z1 z2 hz
    obtain ⟨hc1, hc2, hcB⟩ := hc
    rcases (add_nonneg hc1 hc2).lt_or_eq with hpos | hzero
    · have e : c1 = (c1 + c2) - c2 := by ring
      rw [e] at hz ⊢
      rcases proposition_1 α γ (c1 + c2) hs hpos c2 hc2 (by linarith) z1 z2 hz with
        ⟨w1, w2, hw, hle'⟩ | ⟨w1, w2, hw, hle'⟩
      · rw [(equation_8 α γ (c1 + c2) hs hpos).2 w1 w2 hw] at hle'
        exact hle'.trans (hV1 _ hpos hcB)
      · exact hle'.trans (hV2 _ hpos hcB w1 w2 hw)
    · have h1 : c1 = 0 := by linarith
      have h2 : c2 = 0 := by linarith
      subst h1 h2
      unfold principalProfit; simp [succ_zero]; exact hV0
  refine ⟨hfeas, hex, fun x1 x2 hx c1 c2 hc z1 z2 hz => ?_⟩
  rw [hval x1 x2 hx]
  rcases le_total c2 c1 with h | h
  · exact bound c1 c2 h hc z1 z2 hz
  · rw [profit_swap]
    obtain ⟨a, b, c⟩ := hc
    exact bound c2 c1 h ⟨b, a, by linarith⟩ z2 z1 (eq_swap hz)

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

lemma u_le {γ B' B : ℝ} (hγ : 0 < γ) (hB' : 0 < B') (h : B' ≤ B) :
    1 / (γ * B) ≤ 1 / (γ * B') :=
  one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left h hγ.le)

lemma monoOpt {α γ Bbar : ℝ} (hs : Standing α γ) (hB : 0 < Bbar) (h1 : 1 < γ * Bbar)
    (hcond : 2 < γ * Bbar → 0 ≤ gq α (1 / (γ * Bbar))) : IsOptimal α γ Bbar Bbar 0 := by
  obtain ⟨hγ0, hγ1, hα0, hα1⟩ := hs
  have E := equation_8 α γ Bbar ⟨hγ0, hγ1, hα0, hα1⟩ hB
  refine optimal_of ⟨hγ0, hγ1, hα0, hα1⟩ ⟨hB.le, le_rfl, by linarith⟩ E.1 E.2
    (profitMono_nonneg hγ1) (fun B' hB' hle => profitMono_mono hγ0 hγ1 hB' hle) ?_
  intro B' hB' hle z1 z2 hz
  have hm : γ * B' ≤ γ * Bbar := mul_le_mul_of_nonneg_left hle hγ0.le
  by_cases h2 : γ * B' ≤ 2
  · rw [profit_zero ⟨hγ0, hγ1, hα0, hα1⟩ (by linarith) (by linarith) (by linarith) (by linarith) hz]
    exact profitMono_nonneg hγ1
  push_neg at h2
  rcases hα0.lt_or_eq with hα | hα
  · rw [((equations_10_11 α γ B' ⟨hγ0, hγ1, hα0, hα1⟩ h2).2 hα z1 z2 hz).2.2,
      profitDuo_eq h2, profitMono_eq h1]
    have hγ' : 0 ≤ 1 - γ := by linarith
    apply mul_le_mul_of_nonneg_left _ hγ'
    have hu : 0 < 1 / (γ * Bbar) := by positivity
    have huv := u_le hγ0 hB' hle
    have hc := hcond (by linarith)
    by_cases hg : 0 ≤ gq α (1 / (γ * B'))
    · have := (comp1 hα0 hα1 (hu.trans_le huv)).2 hg
      linarith
    · push_neg at hg
      exact mono_key hα0 hα1 hu huv hc hg
  · subst hα
    have := sym_alpha0 ⟨hγ0, hγ1, le_rfl, hα1⟩ (by linarith) hz
    exact this.trans (profitMono_mono hγ0 hγ1 (by linarith) (by linarith))

lemma duoOpt {α γ Bbar : ℝ} (hs : Standing α γ) (hα : 0 < α) (hB : 2 < γ * Bbar)
    (hcond : gq α (1 / (γ * Bbar)) ≤ 0) : IsOptimal α γ Bbar (Bbar / 2) (Bbar / 2) := by
  obtain ⟨hγ0, hγ1, hα0, hα1⟩ := hs
  have hs : Standing α γ := ⟨hγ0, hγ1, hα0, hα1⟩
  have hBp : 0 < Bbar := by
    by_contra hc; push_neg at hc; nlinarith
  have E := equations_10_11 α γ Bbar hs hB
  have hu : 0 < 1 / (γ * Bbar) := by positivity
  have hγ' : 0 < 1 - γ := by linarith
  have hDM : profitMono γ Bbar ≤ profitDuo α γ Bbar := by
    rw [profitDuo_eq hB, profitMono_eq (by linarith)]
    exact mul_le_mul_of_nonneg_left ((comp2 hα0 hα1 hu).2 hcond) hγ'.le
  have hM0 : 0 ≤ profitDuo α γ Bbar := (profitMono_nonneg hγ1).trans hDM
  obtain ⟨x1, x2, hx, -⟩ := E.1
  refine optimal_of hs ⟨by linarith, by linarith, by linarith⟩ ⟨x1, x2, hx⟩
    (fun y1 y2 hy => ((E.2 hα y1 y2 hy)).2.2) hM0
    (fun B' hB' hle => (profitMono_mono hγ0 hγ1 hB' hle).trans hDM) ?_
  intro B' hB' hle z1 z2 hz
  by_cases h2 : γ * B' ≤ 2
  · rw [profit_zero hs (by linarith) (by linarith) (by linarith) (by linarith) hz]
    exact hM0
  push_neg at h2
  rw [((equations_10_11 α γ B' hs h2).2 hα z1 z2 hz).2.2, profitDuo_eq h2, profitDuo_eq hB]
  exact mul_le_mul_of_nonneg_left (duo_mono hα0 hα1 hu (u_le hγ0 hB' hle) hcond) hγ'.le

lemma comp_profit1 {α γ B : ℝ} (hs : Standing α γ) (h : 2 < γ * B) :
    profitDuo α γ B ≤ profitMono γ B ↔ 0 ≤ gq α (1 / (γ * B)) := by
  obtain ⟨hγ0, hγ1, hα0, hα1⟩ := hs
  have hu : 0 < 1 / (γ * B) := by
    have : 0 < γ * B := by linarith
    positivity
  rw [profitDuo_eq h, profitMono_eq (by linarith), mul_le_mul_iff_right₀ (by linarith)]
  exact comp1 hα0 hα1 hu

theorem main (α γ Bbar : ℝ) (hs : Standing α γ) (hB : 0 < Bbar) :
    (γ * Bbar ≤ 1 → IsOptimal α γ Bbar 0 0 ∧
      ∀ x1 x2, IsEquilibrium α γ 0 0 x1 x2 →
        principalProfit α γ 0 0 x1 x2 = 0) ∧
    (1 < γ * Bbar → γ * Bbar ≤ 2 →
      IsOptimal α γ Bbar Bbar 0) ∧
    (2 < γ * Bbar →
      (α ≤ alphaLow → IsOptimal α γ Bbar Bbar 0) ∧
      (alphaLow < α → α < 1 / 2 →
        (γ * Bbar ∈ Set.Icc (bandLow α) (bandHigh α) →
          IsOptimal α γ Bbar (Bbar / 2) (Bbar / 2)) ∧
        (γ * Bbar ∉ Set.Icc (bandLow α) (bandHigh α) →
          IsOptimal α γ Bbar Bbar 0)) ∧
      (1 / 2 ≤ α →
        (cThreshold α ≤ γ * Bbar →
          IsOptimal α γ Bbar (Bbar / 2) (Bbar / 2)) ∧
        (γ * Bbar < cThreshold α →
          IsOptimal α γ Bbar Bbar 0))) := by
  have hs' := hs
  obtain ⟨hγ0, hγ1, hα0, hα1⟩ := hs'
  have zero00 : ∀ x1 x2, IsEquilibrium α γ 0 0 x1 x2 → principalProfit α γ 0 0 x1 x2 = 0 :=
    fun x1 x2 hx => by unfold principalProfit; simp [succ_zero]
  refine ⟨fun h1 => ⟨?_, zero00⟩, fun h1 h2 => monoOpt hs hB h1 (fun h => by linarith),
    fun h2 => ⟨fun ha => monoOpt hs hB (by linarith) (fun _ => regA hα0 ha _),
      fun ha1 ha2 => ?_, fun ha => ?_⟩⟩
  · -- invest nothing
    have g0 : 0 < gp α γ 0 ∧ gp α γ 0 < 1 := by rw [gp_zero]; exact ⟨hγ0, hγ1⟩
    have hex : IsEquilibrium α γ 0 0 0 0 :=
      mk_eq le_rfl le_rfl (fun z hz => by simp [succ_zero]; linarith)
        (fun z hz => by simp [succ_zero]; linarith)
    refine optimal_of hs ⟨le_rfl, le_rfl, by linarith⟩ ⟨0, 0, hex⟩ zero00 le_rfl ?_ ?_
    · intro B' hB' hle
      have : γ * B' ≤ 1 := by nlinarith
      unfold profitMono; rw [if_pos this]
    · intro B' hB' hle z1 z2 hz
      have : γ * B' ≤ 1 := by nlinarith
      rw [profit_zero hs (by linarith) (by linarith) (by nlinarith) (by nlinarith) hz]
  · have hb := prop3_region_b α γ Bbar hs ha1.le ha2 h2
    have hαp : 0 < α := alphaLow_pos.trans ha1
    constructor
    · intro hin
      have hle := hb.2 hin
      rw [profitDuo_eq h2, profitMono_eq (by linarith), mul_le_mul_iff_right₀ (by linarith)] at hle
      have hu : 0 < 1 / (γ * Bbar) := by
        have : 0 < γ * Bbar := by linarith
        positivity
      exact duoOpt hs hαp h2 ((comp2 hα0 hα1 hu).1 hle)
    · intro hout
      have hlt : ¬ profitMono γ Bbar ≤ profitDuo α γ Bbar := fun h => hout (hb.1 h)
      push_neg at hlt
      exact monoOpt hs hB (by linarith) (fun _ => (comp_profit1 hs h2).1 hlt.le)
  · have ht : 0 < γ * Bbar := by linarith
    have hC := regC (t := γ * Bbar) ha hα1 ht
    constructor
    · intro hc
      exact duoOpt hs (by linarith) h2 (hC.2 hc)
    · intro hc
      refine monoOpt hs hB (by linarith) (fun _ => ?_)
      by_contra hn; push_neg at hn
      exact absurd (hC.1 hn.le) (not_le.2 hc)

end IASolT1

open InnovAlloc.Optimal in
theorem solution (α γ Bbar : ℝ) (hs : Standing α γ) (hB : 0 < Bbar) :
    (γ * Bbar ≤ 1 → IsOptimal α γ Bbar 0 0 ∧
      ∀ x1 x2, IsEquilibrium α γ 0 0 x1 x2 →
        principalProfit α γ 0 0 x1 x2 = 0) ∧
    (1 < γ * Bbar → γ * Bbar ≤ 2 →
      IsOptimal α γ Bbar Bbar 0) ∧
    (2 < γ * Bbar →
      (α ≤ alphaLow → IsOptimal α γ Bbar Bbar 0) ∧
      (alphaLow < α → α < 1 / 2 →
        (γ * Bbar ∈ Set.Icc (bandLow α) (bandHigh α) →
          IsOptimal α γ Bbar (Bbar / 2) (Bbar / 2)) ∧
        (γ * Bbar ∉ Set.Icc (bandLow α) (bandHigh α) →
          IsOptimal α γ Bbar Bbar 0)) ∧
      (1 / 2 ≤ α →
        (cThreshold α ≤ γ * Bbar →
          IsOptimal α γ Bbar (Bbar / 2) (Bbar / 2)) ∧
        (γ * Bbar < cThreshold α →
          IsOptimal α γ Bbar Bbar 0))) :=
  IASolT1.main α γ Bbar hs hB
