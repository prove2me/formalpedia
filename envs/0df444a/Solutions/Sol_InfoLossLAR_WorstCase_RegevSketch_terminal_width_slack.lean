-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.terminal_width_slack
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T09:17:04.837701+00:00
-- url     : https://prove2.me/submissions/b4d96a71-cad9-4bdf-8005-afa6827feaad

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option maxHeartbeats 800000
open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch
noncomputable section

private theorem algebraic_terminal_width_slack (n : ℕ) (q sigma eta requested : ℝ)
    (hn : 0 < n) (hsigma : 0 < sigma) (hrequested : 0 < requested)
    (hthreshold : (16*q*Real.sqrt n/sigma)*eta ≤ requested) :
    let source := requested*sigma/(Real.sqrt 2 * Real.sqrt n)
    0 < source ∧ 8*Real.sqrt 2*q*eta ≤ source ∧
      1/(Real.sqrt 2*(sigma/(2*source)/Real.sqrt n)) = requested ∧
      source^2 = requested^2*sigma^2/(2*(n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hb : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hb2 : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hbound : 16*q*Real.sqrt n*eta ≤ requested*sigma := by
    apply (div_le_iff₀ hsigma).mp
    calc
      (16*q*Real.sqrt n*eta)/sigma = (16*q*Real.sqrt n/sigma)*eta := by ring
      _ ≤ requested := hthreshold
  dsimp only
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ (mul_pos hb ha)).mpr
    calc
      8*Real.sqrt 2*q*eta*(Real.sqrt 2*Real.sqrt n) =
          (8*(Real.sqrt (2 : ℝ))^2)*q*Real.sqrt n*eta := by ring
      _ = 16*q*Real.sqrt n*eta := by rw [hb2]; norm_num
      _ ≤ requested*sigma := hbound
  · field_simp
    nlinarith [hb2]
  · simp only [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt hnR.le]

/-- Terminal-width algebra under the exact `DGSAt` threshold. -/
theorem solution {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (r : ℚ) (hn : 0 < n) (hr : 0 < r)
    (hthreshold : dgsThreshold B ≤ (r : ℝ)) :
    let eta := RegevLWE.GaussConv.smoothingParam (inputModule B) (smoothingError n)
    let source := (r : ℝ)*(famσ n : ℝ)/(Real.sqrt 2*Real.sqrt n)
    0 < source ∧ 8*Real.sqrt 2*(famq n : ℝ)*eta ≤ source ∧
      (0 < eta → Real.sqrt 2*(famq n : ℝ)*eta < source) ∧
      1/(Real.sqrt 2*((famσ n : ℝ)/(2*source)/Real.sqrt n)) = (r : ℝ) ∧
      source^2 = (r : ℝ)^2*(famσ n : ℝ)^2/(2*(n : ℝ)) := by
  have hs : (0 : ℝ) < famσ n := by
    have hnat : 0 < famσ n := by change 0 < n+2; omega
    exact_mod_cast hnat
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have h := algebraic_terminal_width_slack n (famq n) (famσ n)
    (RegevLWE.GaussConv.smoothingParam (inputModule B) (smoothingError n))
    (r : ℝ) hn hs hrR hthreshold
  rcases h with ⟨hpos,hslack,heq,hsquare⟩
  refine ⟨hpos,hslack,?_,heq,hsquare⟩
  intro heta
  have hq : (0 : ℝ) < famq n := by exact_mod_cast NeZero.pos (famq n)
  have hpositive : 0 < Real.sqrt 2*(famq n : ℝ)*
      RegevLWE.GaussConv.smoothingParam (inputModule B) (smoothingError n) := by positivity
  nlinarith

end
