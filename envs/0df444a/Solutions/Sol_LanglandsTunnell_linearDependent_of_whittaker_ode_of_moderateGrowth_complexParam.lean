-- Prove2me | solution 1 for LanglandsTunnell.linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/87811cfb-7d47-52fe-b323-3365933dc1a5

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.MonotoneConvergence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam

set_option autoImplicit false

open scoped Real NNReal
open Filter Topology Set

namespace ComplexWhittakerDependenceAux

private theorem monoOn {φ φ' : ℝ → ℝ} {y₁ : ℝ}
    (hφ : ∀ y, y₁ ≤ y → HasDerivAt φ (φ' y) y) (hnn : ∀ y, y₁ ≤ y → 0 ≤ φ' y) :
    ∀ y, y₁ ≤ y → φ y₁ ≤ φ y := by
  have hm : MonotoneOn φ (Ici y₁) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici y₁) ?_ ?_ ?_
    · intro y hy
      exact (hφ y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact (hφ y (le_of_lt hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hφ y (le_of_lt hy)).deriv]
      exact hnn y (le_of_lt hy)
  intro y hy
  exact hm (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy) hy

private theorem antiOn {φ φ' : ℝ → ℝ} {y₁ : ℝ}
    (hφ : ∀ y, y₁ ≤ y → HasDerivAt φ (φ' y) y) (hnp : ∀ y, y₁ ≤ y → φ' y ≤ 0) :
    ∀ y z, y₁ ≤ y → y ≤ z → φ z ≤ φ y := by
  have hm : AntitoneOn φ (Ici y₁) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici y₁) ?_ ?_ ?_
    · intro y hy
      exact (hφ y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact (hφ y (le_of_lt hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hφ y (le_of_lt hy)).deriv]
      exact hnp y (le_of_lt hy)
  intro y z hy hyz
  exact hm (Set.mem_Ici.2 hy) (Set.mem_Ici.2 (le_trans hy hyz)) hyz

private theorem blowup {h h' h'' : ℝ → ℝ} {a y₁ C : ℝ} {n : ℕ} (ha : 0 < a)
    (hh : ∀ y, y₁ ≤ y → HasDerivAt h (h' y) y) (hh' : ∀ y, y₁ ≤ y → HasDerivAt h' (h'' y) y)
    (hconv : ∀ y, y₁ ≤ y → a ^ 2 * h y ≤ h'' y) (hstart : 0 < h' y₁ + a * h y₁)
    (hbd : ∀ y, y₁ ≤ y → h y ≤ C * y ^ n) : False := by

  have hd1 : ∀ y, y₁ ≤ y → HasDerivAt (fun y => Real.exp (-(a * y)) * (h' y + a * h y))
      (Real.exp (-(a * y)) * (h'' y - a ^ 2 * h y)) y := by
    intro y hy
    have he : HasDerivAt (fun y => Real.exp (-(a * y))) (Real.exp (-(a * y)) * (-a)) y := by
      have := ((hasDerivAt_id y).const_mul (-a)).exp
      simpa using this
    have := he.mul ((hh' y hy).add ((hh y hy).const_mul a))
    refine this.congr_deriv ?_
    simp only [Pi.add_apply]
    ring
  have hm1 := monoOn hd1 (fun y hy => mul_nonneg (Real.exp_pos _).le (sub_nonneg.2 (hconv y hy)))
  have hm1' : ∀ y, y₁ ≤ y →
      Real.exp (-(a * y₁)) * (h' y₁ + a * h y₁) ≤ Real.exp (-(a * y)) * (h' y + a * h y) :=
    fun y hy => hm1 y hy
  have hm_pos : 0 < Real.exp (-(a * y₁)) * (h' y₁ + a * h y₁) := mul_pos (Real.exp_pos _) hstart
  generalize hm : Real.exp (-(a * y₁)) * (h' y₁ + a * h y₁) = m at hm_pos hm1'

  have hlow : ∀ y, y₁ ≤ y → m * Real.exp (a * y) ≤ h' y + a * h y := by
    intro y hy
    have e1 : Real.exp (a * y) * Real.exp (-(a * y)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h2 := mul_le_mul_of_nonneg_left (hm1' y hy) (Real.exp_pos (a * y)).le
    calc m * Real.exp (a * y) = Real.exp (a * y) * m := by ring
      _ ≤ Real.exp (a * y) * (Real.exp (-(a * y)) * (h' y + a * h y)) := h2
      _ = (Real.exp (a * y) * Real.exp (-(a * y))) * (h' y + a * h y) := by ring
      _ = h' y + a * h y := by rw [e1, one_mul]

  have hd2 : ∀ y, y₁ ≤ y → HasDerivAt
      (fun y => 2 * a * (Real.exp (a * y) * h y) - m * (Real.exp (a * y) * Real.exp (a * y)))
      (2 * a * Real.exp (a * y) * (h' y + a * h y - m * Real.exp (a * y))) y := by
    intro y hy
    have he : HasDerivAt (fun y => Real.exp (a * y)) (Real.exp (a * y) * a) y := by
      have := ((hasDerivAt_id y).const_mul a).exp
      simpa using this
    have hA := (he.mul (hh y hy)).const_mul (2 * a)
    have hB := (he.mul he).const_mul m
    have := hA.sub hB
    refine this.congr_deriv ?_
    ring
  have hm2 := monoOn hd2 (fun y hy =>
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two ha.le) (Real.exp_pos _).le) (sub_nonneg.2 (hlow y hy)))
  have hm2' : ∀ y, y₁ ≤ y →
      2 * a * (Real.exp (a * y₁) * h y₁) - m * (Real.exp (a * y₁) * Real.exp (a * y₁))
        ≤ 2 * a * (Real.exp (a * y) * h y) - m * (Real.exp (a * y) * Real.exp (a * y)) :=
    fun y hy => hm2 y hy
  generalize hq : 2 * a * (Real.exp (a * y₁) * h y₁) - m * (Real.exp (a * y₁) * Real.exp (a * y₁)) = q₀
    at hm2'

  have hq2 : ∀ y, y₁ ≤ y → m + q₀ * (Real.exp (-(a * y)) * Real.exp (-(a * y)))
      ≤ 2 * a * C * (y ^ n * Real.exp (-(a * y))) := by
    intro y hy
    have e1 : Real.exp (a * y) * Real.exp (-(a * y)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hE : 0 < Real.exp (a * y) := Real.exp_pos _
    have hD : 0 ≤ Real.exp (-(a * y)) := (Real.exp_pos _).le
    have h2 := hm2' y hy
    have h3 : 2 * a * (Real.exp (a * y) * h y) ≤ 2 * a * (Real.exp (a * y) * (C * y ^ n)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hbd y hy) hE.le) (mul_nonneg zero_le_two ha.le)
    have h4 : q₀ + m * (Real.exp (a * y) * Real.exp (a * y))
        ≤ 2 * a * (Real.exp (a * y) * (C * y ^ n)) := by linarith
    have h5 := mul_le_mul_of_nonneg_right h4 (mul_nonneg hD hD)
    calc m + q₀ * (Real.exp (-(a * y)) * Real.exp (-(a * y)))
        = (q₀ + m * (Real.exp (a * y) * Real.exp (a * y)))
            * (Real.exp (-(a * y)) * Real.exp (-(a * y))) := by
          have : (q₀ + m * (Real.exp (a * y) * Real.exp (a * y)))
              * (Real.exp (-(a * y)) * Real.exp (-(a * y)))
              = q₀ * (Real.exp (-(a * y)) * Real.exp (-(a * y)))
                + m * ((Real.exp (a * y) * Real.exp (-(a * y)))
                  * (Real.exp (a * y) * Real.exp (-(a * y)))) := by ring
          rw [this, e1]; ring
      _ ≤ 2 * a * (Real.exp (a * y) * (C * y ^ n)) * (Real.exp (-(a * y)) * Real.exp (-(a * y))) := h5
      _ = 2 * a * C * (y ^ n * Real.exp (-(a * y))) := by
          have : 2 * a * (Real.exp (a * y) * (C * y ^ n)) * (Real.exp (-(a * y)) * Real.exp (-(a * y)))
              = 2 * a * C * (y ^ n * Real.exp (-(a * y)))
                * (Real.exp (a * y) * Real.exp (-(a * y))) := by ring
          rw [this, e1, mul_one]

  have T1 : Tendsto (fun y : ℝ => y ^ n * Real.exp (-(a * y))) atTop (𝓝 0) := by
    have := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) a ha
    refine this.congr' (Eventually.of_forall fun y => ?_)
    rw [Real.rpow_natCast, neg_mul]
  have T2 : Tendsto (fun y : ℝ => Real.exp (-(a * y))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => a * y) atTop atTop := Tendsto.const_mul_atTop ha tendsto_id
    exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  have T : Tendsto (fun y : ℝ => 2 * a * C * (y ^ n * Real.exp (-(a * y)))
      - q₀ * (Real.exp (-(a * y)) * Real.exp (-(a * y)))) atTop (𝓝 (2 * a * C * 0 - q₀ * (0 * 0))) :=
    (T1.const_mul (2 * a * C)).sub ((T2.mul T2).const_mul q₀)
  simp only [mul_zero, sub_zero] at T
  have ev := T.eventually_lt_const hm_pos
  obtain ⟨y, hy₁, hy⟩ := ((eventually_ge_atTop y₁).and ev).exists
  have := hq2 y hy₁
  linarith

private theorem derivSmall {w w' q m : ℝ → ℝ} {y₀ Q : ℝ}
    (hw : ∀ y, y₀ ≤ y → HasDerivAt w (w' y) y) (hw' : ∀ y, y₀ ≤ y → HasDerivAt w' (q y) y)
    (hQ : 0 ≤ Q) (hq : ∀ y, y₀ ≤ y → |q y| ≤ Q * m y)
    (hw0 : Tendsto w atTop (𝓝 0)) (hm : Tendsto m atTop (𝓝 0)) :
    Tendsto w' atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have hε' : 0 < ε / (Q + 3) := div_pos hε (by linarith)
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 hw0 (ε / (Q + 3)) hε'
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 hm (ε / (Q + 3)) hε'
  refine ⟨max (max N₁ N₂) y₀, fun y hy => ?_⟩
  have hyN₁ : N₁ ≤ y := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hy)
  have hyN₂ : N₂ ≤ y := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hy)
  have hyy₀ : y₀ ≤ y := le_trans (le_max_right _ _) hy
  have hsmall : ∀ z, y ≤ z → |w z| < ε / (Q + 3) := by
    intro z hz
    have := hN₁ z (le_trans hyN₁ hz)
    rwa [Real.dist_eq, sub_zero] at this
  have hmsmall : ∀ z, y ≤ z → m z < ε / (Q + 3) := by
    intro z hz
    have := hN₂ z (le_trans hyN₂ hz)
    rw [Real.dist_eq, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope w w' (by linarith : y < y + 1)
    (fun z hz => (hw z (le_trans hyy₀ hz.1)).continuousAt.continuousWithinAt)
    (fun z hz => hw z (le_trans hyy₀ (le_of_lt hz.1)))
  obtain ⟨η, hη, hηeq⟩ := exists_hasDerivAt_eq_slope w' q hξ.1
    (fun z hz => (hw' z (le_trans hyy₀ hz.1)).continuousAt.continuousWithinAt)
    (fun z hz => hw' z (le_trans hyy₀ (le_of_lt hz.1)))
  rw [Real.dist_eq, sub_zero]
  have hξ1 : w' ξ = w (y + 1) - w y := by
    rw [hξeq, add_sub_cancel_left, div_one]
  have hne : ξ - y ≠ 0 := (sub_pos.2 hξ.1).ne'
  have e : w' y = w' ξ - q η * (ξ - y) := by
    have h1 : q η * (ξ - y) = w' ξ - w' y := by
      rw [hηeq, div_mul_cancel₀ _ hne]
    linarith
  have b1 : |w' ξ| ≤ |w (y + 1)| + |w y| := by rw [hξ1]; exact abs_sub _ _
  have b2 : |w (y + 1)| < ε / (Q + 3) := hsmall (y + 1) (by linarith)
  have b3 : |w y| < ε / (Q + 3) := hsmall y le_rfl
  have hη₀ : y₀ ≤ η := le_trans hyy₀ (le_of_lt hη.1)
  have b4 : |q η| ≤ Q * (ε / (Q + 3)) :=
    (hq η hη₀).trans (mul_le_mul_of_nonneg_left (hmsmall η (le_of_lt hη.1)).le hQ)
  have b6 : |ξ - y| ≤ 1 := by
    rw [abs_of_pos (sub_pos.2 hξ.1)]
    linarith [hξ.2]
  have b7 : |q η| * |ξ - y| ≤ Q * (ε / (Q + 3)) * 1 :=
    mul_le_mul b4 b6 (abs_nonneg _) (mul_nonneg hQ hε'.le)
  have s1 : |w' y| ≤ |w' ξ| + |q η| * |ξ - y| := by
    rw [e, ← abs_mul]
    exact abs_sub _ _
  have s2 : (Q + 3) * (ε / (Q + 3)) = ε := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (by linarith : (0 : ℝ) < Q + 3).ne']
  linarith [s1, b1, b2, b3, b7, s2, hε']

private theorem decay2 {u u' v v' p s : ℝ → ℝ} {y₀ c P S C : ℝ} {n : ℕ} (hc : 0 < c)
    (hu : ∀ y, y₀ ≤ y → HasDerivAt u (u' y) y)
    (hu' : ∀ y, y₀ ≤ y → HasDerivAt u' (p y * u y - s y * v y) y)
    (hv : ∀ y, y₀ ≤ y → HasDerivAt v (v' y) y)
    (hv' : ∀ y, y₀ ≤ y → HasDerivAt v' (p y * v y + s y * u y) y)
    (hcp : ∀ y, y₀ ≤ y → c ≤ p y) (hpP : ∀ y, y₀ ≤ y → p y ≤ P) (hsS : ∀ y, y₀ ≤ y → |s y| ≤ S)
    (hbd : ∀ y, y₀ ≤ y → u y * u y + v y * v y ≤ C * y ^ n) :
    Tendsto u atTop (𝓝 0) ∧ Tendsto v atTop (𝓝 0)
      ∧ Tendsto u' atTop (𝓝 0) ∧ Tendsto v' atTop (𝓝 0) := by

  have hh : ∀ y, y₀ ≤ y → HasDerivAt (fun y => u y * u y + v y * v y)
      (2 * (u y * u' y + v y * v' y)) y := fun y hy =>
    (((hu y hy).mul (hu y hy)).add ((hv y hy).mul (hv y hy))).congr_deriv (by ring)
  have hh' : ∀ y, y₀ ≤ y → HasDerivAt (fun y => 2 * (u y * u' y + v y * v' y))
      (2 * (u' y * u' y + v' y * v' y + p y * (u y * u y + v y * v y))) y := fun y hy =>
    ((((hu y hy).mul (hu' y hy)).add ((hv y hy).mul (hv' y hy))).const_mul 2).congr_deriv (by ring)
  have hsqnn : ∀ y, 0 ≤ u y * u y + v y * v y := fun y =>
    add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

  have hneg : ∀ y₁, y₀ ≤ y₁ → 2 * (u y₁ * u' y₁ + v y₁ * v' y₁) ≤ 0 := by
    intro y₁ hy₁
    by_contra hpos
    rw [not_le] at hpos
    have ha : 0 < Real.sqrt (2 * c) := Real.sqrt_pos.2 (mul_pos two_pos hc)
    refine blowup (h := fun y => u y * u y + v y * v y) (h' := fun y => 2 * (u y * u' y + v y * v' y))
      (h'' := fun y => 2 * (u' y * u' y + v' y * v' y + p y * (u y * u y + v y * v y)))
      (a := Real.sqrt (2 * c)) (y₁ := y₁) (C := C) (n := n) ha
      (fun y hy => hh y (le_trans hy₁ hy)) (fun y hy => hh' y (le_trans hy₁ hy)) ?_ ?_ ?_
    · intro y hy
      have hy' := le_trans hy₁ hy
      show Real.sqrt (2 * c) ^ 2 * (u y * u y + v y * v y)
        ≤ 2 * (u' y * u' y + v' y * v' y + p y * (u y * u y + v y * v y))
      have hsq : Real.sqrt (2 * c) ^ 2 = 2 * c := Real.sq_sqrt (mul_pos two_pos hc).le
      rw [hsq]
      have h1 : 0 ≤ (p y - c) * (u y * u y + v y * v y) :=
        mul_nonneg (sub_nonneg.2 (hcp y hy')) (hsqnn y)
      nlinarith [mul_self_nonneg (u' y), mul_self_nonneg (v' y), h1]
    · show 0 < 2 * (u y₁ * u' y₁ + v y₁ * v' y₁) + Real.sqrt (2 * c) * (u y₁ * u y₁ + v y₁ * v y₁)
      have : 0 ≤ Real.sqrt (2 * c) * (u y₁ * u y₁ + v y₁ * v y₁) := mul_nonneg ha.le (hsqnn y₁)
      linarith
    · intro y hy
      exact hbd y (le_trans hy₁ hy)

  have hanti := antiOn hh hneg
  set H : ℝ → ℝ := fun y => u (max y y₀) * u (max y y₀) + v (max y y₀) * v (max y y₀) with hH
  have hHanti : Antitone H := by
    intro y z hyz
    exact hanti (max y y₀) (max z y₀) (le_max_right _ _) (max_le_max hyz le_rfl)
  have hHbdd : BddBelow (range H) := ⟨0, by rintro _ ⟨y, rfl⟩; exact hsqnn _⟩
  have hHlim : Tendsto H atTop (𝓝 (⨅ y, H y)) := tendsto_atTop_ciInf hHanti hHbdd
  have hL0 : 0 ≤ ⨅ y, H y := le_ciInf fun y => hsqnn _
  have hLle : ∀ y, y₀ ≤ y → (⨅ y, H y) ≤ u y * u y + v y * v y := by
    intro y hy
    have h1 : (⨅ y, H y) ≤ H y := ciInf_le hHbdd y
    have h2 : H y = u y * u y + v y * v y := by simp only [hH, max_eq_left hy]
    exact h1.trans (le_of_eq h2)
  have hsq_lim : Tendsto (fun y => u y * u y + v y * v y) atTop (𝓝 (⨅ y, H y)) := by
    refine hHlim.congr' ?_
    filter_upwards [eventually_ge_atTop y₀] with y hy
    simp only [hH, max_eq_left hy]

  have hiInf0 : (⨅ y, H y) = 0 := by
    by_contra hne
    have hLpos : 0 < ⨅ y, H y := lt_of_le_of_ne hL0 (Ne.symm hne)
    have hconv2 : ∀ y, y₀ ≤ y → 2 * c * (⨅ y, H y)
        ≤ 2 * (u' y * u' y + v' y * v' y + p y * (u y * u y + v y * v y)) := by
      intro y hy
      have h1 := hLle y hy
      have h2 : 0 ≤ (p y - c) * (u y * u y + v y * v y) :=
        mul_nonneg (sub_nonneg.2 (hcp y hy)) (hsqnn y)
      nlinarith [mul_self_nonneg (u' y), mul_self_nonneg (v' y), h1, h2, hc]
    generalize hm₂ : 2 * c * (⨅ y, H y) = m₂ at hconv2
    have hm₂pos : 0 < m₂ := by
      rw [← hm₂]
      exact mul_pos (mul_pos two_pos hc) hLpos
    have hd : ∀ y, y₀ ≤ y → HasDerivAt (fun y => 2 * (u y * u' y + v y * v' y) - m₂ * y)
        (2 * (u' y * u' y + v' y * v' y + p y * (u y * u y + v y * v y)) - m₂) y := by
      intro y hy
      have := (hh' y hy).sub ((hasDerivAt_id y).const_mul m₂)
      simp at this
      exact this
    have hmono := monoOn hd (fun y hy => sub_nonneg.2 (hconv2 y hy))
    set D₀ : ℝ := 2 * (u y₀ * u' y₀ + v y₀ * v' y₀) with hD₀
    have hY₀ : y₀ ≤ y₀ + (|D₀| + 1) / m₂ := by
      have : 0 ≤ (|D₀| + 1) / m₂ := div_nonneg (by positivity) hm₂pos.le
      linarith
    have h1 : D₀ - m₂ * y₀
        ≤ 2 * (u (y₀ + (|D₀| + 1) / m₂) * u' (y₀ + (|D₀| + 1) / m₂)
              + v (y₀ + (|D₀| + 1) / m₂) * v' (y₀ + (|D₀| + 1) / m₂))
          - m₂ * (y₀ + (|D₀| + 1) / m₂) := hmono _ hY₀
    have h2 := hneg _ hY₀
    have h3 : m₂ * ((|D₀| + 1) / m₂) = |D₀| + 1 := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hm₂pos.ne']
    have h4 : -D₀ ≤ |D₀| := neg_le_abs _
    have h5 : m₂ * (y₀ + (|D₀| + 1) / m₂) = m₂ * y₀ + (|D₀| + 1) := by rw [mul_add, h3]
    linarith

  have hsq0 : Tendsto (fun y => u y * u y + v y * v y) atTop (𝓝 0) := by
    rw [hiInf0] at hsq_lim
    exact hsq_lim
  have hroot : Tendsto (fun y => Real.sqrt (u y * u y + v y * v y)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hsq0
    simpa [Function.comp_def] using this
  have habs_u : Tendsto (fun y => |u y|) atTop (𝓝 0) := by
    refine squeeze_zero (fun y => abs_nonneg _) (fun y => ?_) hroot
    refine Real.abs_le_sqrt ?_
    nlinarith [mul_self_nonneg (v y)]
  have habs_v : Tendsto (fun y => |v y|) atTop (𝓝 0) := by
    refine squeeze_zero (fun y => abs_nonneg _) (fun y => ?_) hroot
    refine Real.abs_le_sqrt ?_
    nlinarith [mul_self_nonneg (u y)]
  have hu0 : Tendsto u atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 (by simpa [Real.norm_eq_abs] using habs_u)
  have hv0 : Tendsto v atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 (by simpa [Real.norm_eq_abs] using habs_v)

  have hm : Tendsto (fun y => |u y| + |v y|) atTop (𝓝 0) := by
    simpa using habs_u.add habs_v
  have hP0 : 0 < P := lt_of_lt_of_le hc (le_trans (hcp y₀ le_rfl) (hpP y₀ le_rfl))
  have hS0 : 0 ≤ S := le_trans (abs_nonneg _) (hsS y₀ le_rfl)
  have hpabs : ∀ y, y₀ ≤ y → |p y| ≤ P := fun y hy => by
    rw [abs_of_pos (lt_of_lt_of_le hc (hcp y hy))]
    exact hpP y hy
  have hbu : ∀ y, y₀ ≤ y → |p y * u y - s y * v y| ≤ (P + S) * (|u y| + |v y|) := by
    intro y hy
    calc |p y * u y - s y * v y| ≤ |p y * u y| + |s y * v y| := abs_sub _ _
      _ = |p y| * |u y| + |s y| * |v y| := by rw [abs_mul, abs_mul]
      _ ≤ P * |u y| + S * |v y| :=
          add_le_add (mul_le_mul_of_nonneg_right (hpabs y hy) (abs_nonneg _))
            (mul_le_mul_of_nonneg_right (hsS y hy) (abs_nonneg _))
      _ ≤ (P + S) * (|u y| + |v y|) := by nlinarith [abs_nonneg (u y), abs_nonneg (v y), hP0, hS0]
  have hbv : ∀ y, y₀ ≤ y → |p y * v y + s y * u y| ≤ (P + S) * (|u y| + |v y|) := by
    intro y hy
    calc |p y * v y + s y * u y| ≤ |p y * v y| + |s y * u y| := abs_add_le _ _
      _ = |p y| * |v y| + |s y| * |u y| := by rw [abs_mul, abs_mul]
      _ ≤ P * |v y| + S * |u y| :=
          add_le_add (mul_le_mul_of_nonneg_right (hpabs y hy) (abs_nonneg _))
            (mul_le_mul_of_nonneg_right (hsS y hy) (abs_nonneg _))
      _ ≤ (P + S) * (|u y| + |v y|) := by nlinarith [abs_nonneg (u y), abs_nonneg (v y), hP0, hS0]
  have hQ : 0 ≤ P + S := by linarith
  exact ⟨hu0, hv0, derivSmall hu hu' hQ hbu hu0 hm,
    derivSmall hv hv' hQ hbv hv0 hm⟩

private theorem cdecay {ν : ℂ} {k : ℝ} {f : ℝ → ℂ}
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (hfgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N) :
    Tendsto f atTop (𝓝 0) ∧ Tendsto (deriv f) atTop (𝓝 0) := by
  have hd1 : ∀ y : ℝ, 0 < y → HasDerivAt f (deriv f y) y := fun y hy =>
    (hf.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
  have hd2 : ∀ y : ℝ, 0 < y → HasDerivAt (deriv f) (deriv (deriv f) y) y := fun y hy =>
    (hf'.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt

  set r : ℝ := (ν ^ 2).re with hr
  set σ : ℝ := (ν ^ 2).im with hσ
  have hsplit : ν ^ 2 = (r : ℂ) + (σ : ℂ) * Complex.I := (Complex.re_add_im (ν ^ 2)).symm
  set p : ℝ → ℝ := fun y => 4 * π ^ 2 - 2 * π * k / y - (1 / 4 - r) / y ^ 2 with hp
  set s : ℝ → ℝ := fun y => σ / y ^ 2 with hs
  have hP : ∀ y : ℝ, 0 < y → deriv (deriv f) y = ((p y : ℂ) + (s y : ℂ) * Complex.I) * f y := by
    intro y hy
    have e := hfeq y hy
    rw [hsplit] at e
    have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hy.ne'
    have hmain : (y : ℂ) ^ 2 * (((p y : ℝ) : ℂ) + ((s y : ℝ) : ℂ) * Complex.I)
        = -(1 / 4 - ((r : ℂ) + (σ : ℂ) * Complex.I) + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ)
            - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) := by
      simp only [hp, hs]
      push_cast
      field_simp
      ring
    apply mul_left_cancel₀ (pow_ne_zero 2 hy0)
    rw [← mul_assoc, hmain]
    linear_combination e

  set A : ℝ := 2 * π * |k| + |1 / 4 - r| with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  set y₀ : ℝ := 1 + A / (2 * π ^ 2) with hy₀
  have hy₀1 : 1 ≤ y₀ := by
    have : 0 ≤ A / (2 * π ^ 2) := div_nonneg hA0 (by positivity)
    linarith
  have hy₀pos : 0 < y₀ := by linarith
  have hbound : ∀ y : ℝ, y₀ ≤ y → |2 * π * k / y + (1 / 4 - r) / y ^ 2| ≤ 2 * π ^ 2 := by
    intro y hy
    have hy1 : 1 ≤ y := le_trans hy₀1 hy
    have hypos : 0 < y := by linarith
    have h1 : |2 * π * k / y| ≤ 2 * π * |k| / y₀ := by
      rw [abs_div, abs_of_pos hypos, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      exact div_le_div_of_nonneg_left (by positivity) hy₀pos hy
    have h2 : |(1 / 4 - r) / y ^ 2| ≤ |1 / 4 - r| / y₀ := by
      rw [abs_div, abs_of_pos (pow_pos hypos 2)]
      have : y₀ ≤ y ^ 2 := by nlinarith
      exact div_le_div_of_nonneg_left (abs_nonneg _) hy₀pos this
    have h3 : 2 * π * |k| / y₀ + |1 / 4 - r| / y₀ = A / y₀ := by
      rw [hA, add_div]
    have h4 : A / y₀ ≤ 2 * π ^ 2 := by
      have hπ2 : (0 : ℝ) < 2 * π ^ 2 := by positivity
      rw [div_le_iff₀ hy₀pos, hy₀, mul_add, mul_one, ← mul_div_assoc, mul_div_cancel_left₀ _ hπ2.ne']
      linarith
    calc |2 * π * k / y + (1 / 4 - r) / y ^ 2|
        ≤ |2 * π * k / y| + |(1 / 4 - r) / y ^ 2| := abs_add_le _ _
      _ ≤ 2 * π * |k| / y₀ + |1 / 4 - r| / y₀ := add_le_add h1 h2
      _ = A / y₀ := h3
      _ ≤ 2 * π ^ 2 := h4
  have hcp : ∀ y : ℝ, y₀ ≤ y → 2 * π ^ 2 ≤ p y := by
    intro y hy
    have := (abs_le.1 (hbound y hy)).2
    simp only [hp]
    linarith
  have hpP : ∀ y : ℝ, y₀ ≤ y → p y ≤ 6 * π ^ 2 := by
    intro y hy
    have := (abs_le.1 (hbound y hy)).1
    simp only [hp]
    linarith
  have hsS : ∀ y : ℝ, y₀ ≤ y → |s y| ≤ |σ| := by
    intro y hy
    have hy1 : 1 ≤ y := le_trans hy₀1 hy
    have hy2 : 1 ≤ y ^ 2 := one_le_pow₀ hy1
    simp only [hs]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < y ^ 2)]
    exact div_le_self (abs_nonneg _) hy2

  obtain ⟨C, N, hCN⟩ := hfgr
  set n : ℕ := ⌈N⌉₊ with hn
  have hgrow : ∀ y : ℝ, y₀ ≤ y → ‖f y‖ ≤ max C 0 * y ^ n := by
    intro y hy
    have hy1 : 1 ≤ y := le_trans hy₀1 hy
    have h1 := hCN y hy1
    have h2 : y ^ N ≤ y ^ n := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hy1 (Nat.le_ceil N)
    have h3 : C * y ^ N ≤ max C 0 * y ^ N :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
    have h4 : max C 0 * y ^ N ≤ max C 0 * y ^ n := mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
    linarith
  have hbd : ∀ y : ℝ, y₀ ≤ y →
      (f y).re * (f y).re + (f y).im * (f y).im ≤ (max C 0) ^ 2 * y ^ (2 * n) := by
    intro y hy
    have h1 := hgrow y hy
    have h2 : (f y).re * (f y).re + (f y).im * (f y).im = ‖f y‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
    rw [h2]
    calc ‖f y‖ ^ 2 ≤ (max C 0 * y ^ n) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = (max C 0) ^ 2 * y ^ (2 * n) := by ring

  have hre : ∀ y : ℝ, y₀ ≤ y → HasDerivAt (fun y => (f y).re) ((deriv f y).re) y := by
    intro y hy
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (hd1 y (by linarith))
    simpa [Function.comp_def] using h
  have hre' : ∀ y : ℝ, y₀ ≤ y →
      HasDerivAt (fun y => (deriv f y).re) (p y * (f y).re - s y * (f y).im) y := by
    intro y hy
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (hd2 y (by linarith))
    rw [hP y (by linarith)] at h
    simpa [Function.comp_def, add_mul, Complex.mul_re, Complex.add_re, Complex.mul_im,
      sub_eq_add_neg] using h
  have him : ∀ y : ℝ, y₀ ≤ y → HasDerivAt (fun y => (f y).im) ((deriv f y).im) y := by
    intro y hy
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y (hd1 y (by linarith))
    simpa [Function.comp_def] using h
  have him' : ∀ y : ℝ, y₀ ≤ y →
      HasDerivAt (fun y => (deriv f y).im) (p y * (f y).im + s y * (f y).re) y := by
    intro y hy
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y (hd2 y (by linarith))
    rw [hP y (by linarith)] at h
    simpa [Function.comp_def, add_mul, Complex.mul_re, Complex.add_im, Complex.mul_im,
      add_comm] using h
  have hc : (0 : ℝ) < 2 * π ^ 2 := by positivity
  obtain ⟨Tre, Tim, Tre', Tim'⟩ := decay2 (u := fun y => (f y).re) (u' := fun y => (deriv f y).re)
    (v := fun y => (f y).im) (v' := fun y => (deriv f y).im) (p := p) (s := s)
    (C := (max C 0) ^ 2) (n := 2 * n) hc hre hre' him him' hcp hpP hsS hbd
  have absT : ∀ {w : ℝ → ℝ}, Tendsto w atTop (𝓝 0) → Tendsto (fun y => |w y|) atTop (𝓝 0) := by
    intro w hw
    have := (continuous_abs.tendsto (0 : ℝ)).comp hw
    simp at this
    exact this
  constructor
  · refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    refine squeeze_zero (fun y => norm_nonneg _) (fun y => Complex.norm_le_abs_re_add_abs_im _) ?_
    simpa using (absT Tre).add (absT Tim)
  · refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    refine squeeze_zero (fun y => norm_nonneg _) (fun y => Complex.norm_le_abs_re_add_abs_im _) ?_
    simpa using (absT Tre').add (absT Tim')

end ComplexWhittakerDependenceAux

open ComplexWhittakerDependenceAux in

theorem solution (ν : ℂ)
    (k : ℝ) (f g : ℝ → ℂ)
    (hf : DifferentiableOn ℝ f (Set.Ioi 0)) (hf' : DifferentiableOn ℝ (deriv f) (Set.Ioi 0))
    (hfeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv f) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * f y = 0)
    (hfgr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖f y‖ ≤ C * y ^ N)
    (hg : DifferentiableOn ℝ g (Set.Ioi 0)) (hg' : DifferentiableOn ℝ (deriv g) (Set.Ioi 0))
    (hgeq : ∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv g) y
            + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) * g y = 0)
    (hggr : ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖g y‖ ≤ C * y ^ N) :
    ∃ c₁ c₂ : ℂ, (c₁, c₂) ≠ 0 ∧ ∀ y : ℝ, 0 < y → c₁ * f y + c₂ * g y = 0 := by

  obtain ⟨hf0, hf'0⟩ := cdecay hf hf' hfeq hfgr
  obtain ⟨hg0, hg'0⟩ := cdecay hg hg' hgeq hggr

  have hd1 : ∀ y : ℝ, 0 < y → HasDerivAt f (deriv f y) y := fun y hy =>
    (hf.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
  have hd2 : ∀ y : ℝ, 0 < y → HasDerivAt (deriv f) (deriv (deriv f) y) y := fun y hy =>
    (hf'.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
  have he1 : ∀ y : ℝ, 0 < y → HasDerivAt g (deriv g y) y := fun y hy =>
    (hg.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
  have he2 : ∀ y : ℝ, 0 < y → HasDerivAt (deriv g) (deriv (deriv g) y) y := fun y hy =>
    (hg'.differentiableAt (Ioi_mem_nhds hy)).hasDerivAt

  set M : ℝ → ℂ := fun y =>
    -(1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2) / (y : ℂ) ^ 2
    with hM
  have hMf : ∀ y : ℝ, 0 < y → deriv (deriv f) y = M y * f y := by
    intro y hy
    have e := hfeq y hy
    have hy2 : (y : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.2 hy.ne')
    simp only [hM]
    rw [div_mul_eq_mul_div, eq_div_iff hy2]
    linear_combination e
  have hMg : ∀ y : ℝ, 0 < y → deriv (deriv g) y = M y * g y := by
    intro y hy
    have e := hgeq y hy
    have hy2 : (y : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.2 hy.ne')
    simp only [hM]
    rw [div_mul_eq_mul_div, eq_div_iff hy2]
    linear_combination e

  set w : ℝ → ℂ := fun y => f y * deriv g y - deriv f y * g y with hw
  have hwd : ∀ y : ℝ, 0 < y → HasDerivAt w 0 y := by
    intro y hy
    have h := ((hd1 y hy).mul (he2 y hy)).sub ((hd2 y hy).mul (he1 y hy))
    refine h.congr_deriv ?_
    rw [hMf y hy, hMg y hy]
    ring
  have hwc : ∀ y₁ y₂ : ℝ, 0 < y₁ → 0 < y₂ → w y₁ = w y₂ := by
    intro y₁ y₂ h1 h2
    have hmain := Convex.norm_image_sub_le_of_norm_deriv_le (f := w) (C := 0)
      (fun x hx => (hwd x hx).differentiableAt)
      (fun x hx => by simp [(hwd x hx).deriv]) (convex_Ioi (0 : ℝ)) h1 h2
    rw [zero_mul] at hmain
    have : w y₂ - w y₁ = 0 := norm_le_zero_iff.1 hmain
    exact (sub_eq_zero.1 this).symm
  have hwt : Tendsto w atTop (𝓝 0) := by
    have := (hf0.mul hg'0).sub (hf'0.mul hg0)
    simp only [mul_zero, sub_zero] at this
    exact this
  have hw0 : ∀ y : ℝ, 0 < y → w y = 0 := by
    intro y hy
    have hconst : Tendsto w atTop (𝓝 (w y)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
      exact hwc y z hy hz
    exact tendsto_nhds_unique hconst hwt

  have huniq : ∀ α β : ℂ, α * f 1 + β * g 1 = 0 → α * deriv f 1 + β * deriv g 1 = 0 →
      ∀ y : ℝ, 0 < y → α * f y + β * g y = 0 := by
    intro α β h0 h0' y hy

    set a : ℝ := min 1 y / 2 with ha
    set b : ℝ := max 1 y + 1 with hb
    have hmin : 0 < min 1 y := lt_min one_pos hy
    have ha0 : 0 < a := by rw [ha]; linarith
    have ha1 : a < 1 := by
      have : min 1 y ≤ 1 := min_le_left _ _
      rw [ha]; linarith
    have hay : a < y := by
      have : min 1 y ≤ y := min_le_right _ _
      rw [ha]; linarith
    have h1b : 1 < b := by
      have : 1 ≤ max 1 y := le_max_left _ _
      rw [hb]; linarith
    have hyb : y < b := by
      have : y ≤ max 1 y := le_max_right _ _
      rw [hb]; linarith
    have hb0 : 0 < b := by linarith

    set Mb : ℝ := (1 / 4 + ‖ν ^ 2‖ + 2 * π * |k| * b + 4 * π ^ 2 * b ^ 2) / a ^ 2 with hMb
    have hN0 : 0 ≤ 1 / 4 + ‖ν ^ 2‖ + 2 * π * |k| * b + 4 * π ^ 2 * b ^ 2 :=
      add_nonneg (add_nonneg (add_nonneg (by norm_num) (norm_nonneg _)) (mul_nonneg (by positivity) hb0.le))
        (by positivity)
    have hMb0 : 0 ≤ Mb := by
      rw [hMb]
      exact div_nonneg hN0 (sq_nonneg a)
    have hMbound : ∀ t : ℝ, t ∈ Set.Ioo a b → ‖M t‖ ≤ Mb := by
      intro t ht
      have ht0 : 0 < t := lt_trans ha0 ht.1
      have htb : t ≤ b := le_of_lt ht.2
      have hnum : ‖(1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (t : ℂ) - 4 * (π : ℂ) ^ 2 * (t : ℂ) ^ 2)‖
          ≤ 1 / 4 + ‖ν ^ 2‖ + 2 * π * |k| * b + 4 * π ^ 2 * b ^ 2 := by
        have n1 : ‖(1 / 4 : ℂ) - ν ^ 2‖ ≤ 1 / 4 + ‖ν ^ 2‖ := by
          refine (norm_sub_le _ _).trans ?_
          norm_num
        have n2 : ‖2 * (π : ℂ) * (k : ℂ) * (t : ℂ)‖ = 2 * π * |k| * t := by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
            abs_of_pos ht0, Complex.norm_ofNat]
        have n3 : ‖4 * (π : ℂ) ^ 2 * (t : ℂ) ^ 2‖ = 4 * π ^ 2 * t ^ 2 := by
          simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
            abs_of_pos ht0, Complex.norm_ofNat]
        have n4 : 2 * π * |k| * t ≤ 2 * π * |k| * b :=
          mul_le_mul_of_nonneg_left htb (by positivity)
        have n5 : 4 * π ^ 2 * t ^ 2 ≤ 4 * π ^ 2 * b ^ 2 := by
          have : t ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ht0.le htb 2
          exact mul_le_mul_of_nonneg_left this (by positivity)
        calc ‖(1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (t : ℂ) - 4 * (π : ℂ) ^ 2 * (t : ℂ) ^ 2)‖
            ≤ ‖(1 / 4 : ℂ) - ν ^ 2 + 2 * (π : ℂ) * (k : ℂ) * (t : ℂ)‖ + ‖4 * (π : ℂ) ^ 2 * (t : ℂ) ^ 2‖ :=
              norm_sub_le _ _
          _ ≤ (‖(1 / 4 : ℂ) - ν ^ 2‖ + ‖2 * (π : ℂ) * (k : ℂ) * (t : ℂ)‖) + ‖4 * (π : ℂ) ^ 2 * (t : ℂ) ^ 2‖ :=
              add_le_add (norm_add_le _ _) le_rfl
          _ ≤ 1 / 4 + ‖ν ^ 2‖ + 2 * π * |k| * b + 4 * π ^ 2 * b ^ 2 := by
              rw [n2, n3]; linarith
      have hden : ‖(t : ℂ) ^ 2‖ = t ^ 2 := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      have hat : a ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ ha0.le (le_of_lt ht.1) 2
      simp only [hM]
      rw [norm_div, norm_neg, hden, hMb]
      exact div_le_div₀ hN0 hnum (pow_pos ha0 2) hat

    set v : ℝ → ℂ × ℂ → ℂ × ℂ := fun t x => (x.2, M t * x.1) with hv
    have hK0 : 0 ≤ max 1 Mb := le_trans zero_le_one (le_max_left _ _)
    set K : ℝ≥0 := ⟨max 1 Mb, hK0⟩ with hK
    have hvK : ∀ t : ℝ, t ∈ Set.Ioo a b →
        LipschitzOnWith K (v t) ((fun _ : ℝ => (Set.univ : Set (ℂ × ℂ))) t) := by
      intro t ht
      refine LipschitzOnWith.of_dist_le_mul fun x _ z _ => ?_
      have hMt := hMbound t ht
      show dist (x.2, M t * x.1) (z.2, M t * z.1) ≤ (max 1 Mb : ℝ) * dist x z
      rw [Prod.dist_eq, Prod.dist_eq]
      have d1 : dist (M t * x.1) (M t * z.1) = ‖M t‖ * dist x.1 z.1 := by
        rw [dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul]
      show max (dist x.2 z.2) (dist (M t * x.1) (M t * z.1))
          ≤ (max 1 Mb : ℝ) * max (dist x.1 z.1) (dist x.2 z.2)
      rw [d1]
      refine max_le ?_ ?_
      · calc dist x.2 z.2 ≤ max (dist x.1 z.1) (dist x.2 z.2) := le_max_right _ _
          _ ≤ (max 1 Mb : ℝ) * max (dist x.1 z.1) (dist x.2 z.2) :=
              le_mul_of_one_le_left (le_trans dist_nonneg (le_max_left _ _)) (le_max_left _ _)
      · calc ‖M t‖ * dist x.1 z.1 ≤ Mb * max (dist x.1 z.1) (dist x.2 z.2) :=
              mul_le_mul hMt (le_max_left _ _) dist_nonneg hMb0
          _ ≤ (max 1 Mb : ℝ) * max (dist x.1 z.1) (dist x.2 z.2) :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (le_trans dist_nonneg (le_max_left _ _))

    set X : ℝ → ℂ × ℂ := fun t => (α * f t + β * g t, α * deriv f t + β * deriv g t) with hX
    set X₀ : ℝ → ℂ × ℂ := fun _ => ((0 : ℂ), (0 : ℂ)) with hX₀
    have hXd : ∀ t : ℝ, t ∈ Set.Ioo a b →
        HasDerivAt X (v t (X t)) t ∧ X t ∈ (fun _ : ℝ => (Set.univ : Set (ℂ × ℂ))) t := by
      intro t ht
      have ht0 : 0 < t := lt_trans ha0 ht.1
      refine ⟨?_, Set.mem_univ _⟩
      have d1 : HasDerivAt (fun t => α * f t + β * g t) (α * deriv f t + β * deriv g t) t :=
        ((hd1 t ht0).const_mul α).add ((he1 t ht0).const_mul β)
      have d2 : HasDerivAt (fun t => α * deriv f t + β * deriv g t)
          (M t * (α * f t + β * g t)) t := by
        have := ((hd2 t ht0).const_mul α).add ((he2 t ht0).const_mul β)
        refine this.congr_deriv ?_
        rw [hMf t ht0, hMg t ht0]
        ring
      show HasDerivAt (fun t => (α * f t + β * g t, α * deriv f t + β * deriv g t))
        (α * deriv f t + β * deriv g t, M t * (α * f t + β * g t)) t
      exact d1.prodMk d2
    have hX₀d : ∀ t : ℝ, t ∈ Set.Ioo a b →
        HasDerivAt X₀ (v t (X₀ t)) t ∧ X₀ t ∈ (fun _ : ℝ => (Set.univ : Set (ℂ × ℂ))) t := by
      intro t ht
      refine ⟨?_, Set.mem_univ _⟩
      show HasDerivAt (fun _ : ℝ => ((0 : ℂ), (0 : ℂ))) ((0 : ℂ), M t * 0) t
      rw [mul_zero]
      exact hasDerivAt_const t _
    have heq : X 1 = X₀ 1 := by
      show (α * f 1 + β * g 1, α * deriv f 1 + β * deriv g 1) = ((0 : ℂ), (0 : ℂ))
      rw [h0, h0']
    have hmain := ODE_solution_unique_of_mem_Ioo (t₀ := (1 : ℝ)) hvK
      (show (1 : ℝ) ∈ Set.Ioo a b from ⟨ha1, h1b⟩) hXd hX₀d heq (show y ∈ Set.Ioo a b from ⟨hay, hyb⟩)
    have := congrArg Prod.fst hmain
    simpa [hX, hX₀] using this

  have hw1 : f 1 * deriv g 1 - deriv f 1 * g 1 = 0 := hw0 1 one_pos
  by_cases hgz : g 1 = 0 ∧ deriv g 1 = 0
  · refine ⟨0, 1, by simp [Prod.ext_iff], ?_⟩
    intro y hy
    have := huniq 0 1 (by rw [hgz.1]; ring) (by rw [hgz.2]; ring) y hy
    simpa using this
  · by_cases hg1 : g 1 = 0
    · have hg1' : deriv g 1 ≠ 0 := fun h => hgz ⟨hg1, h⟩
      have hf1 : f 1 = 0 := by
        rw [hg1, mul_zero, sub_zero] at hw1
        exact (mul_eq_zero.1 hw1).resolve_right hg1'
      refine ⟨1, -(deriv f 1 / deriv g 1), by simp [Prod.ext_iff], ?_⟩
      refine huniq 1 (-(deriv f 1 / deriv g 1)) ?_ ?_
      · rw [hf1, hg1]; ring
      · rw [neg_mul, div_mul_cancel₀ _ hg1']
        ring
    · refine ⟨1, -(f 1 / g 1), by simp [Prod.ext_iff], ?_⟩
      refine huniq 1 (-(f 1 / g 1)) ?_ ?_
      · rw [neg_mul, div_mul_cancel₀ _ hg1]
        ring
      · have hq : f 1 / g 1 * deriv g 1 = deriv f 1 := by
          rw [div_mul_eq_mul_div, div_eq_iff hg1]
          linear_combination hw1
        rw [neg_mul, hq]
        ring

end S_LanglandsTunnell_linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam
end P2MW
export P2MW.S_LanglandsTunnell_linearDependent_of_whittaker_ode_of_moderateGrowth_complexParam (solution)
