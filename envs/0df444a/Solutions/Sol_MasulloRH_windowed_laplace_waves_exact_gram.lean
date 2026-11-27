-- Prove2me | solution 1 for MasulloRH.windowed_laplace_waves_exact_gram
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T01:14:44.511269+00:00
-- url     : https://prove2.me/submissions/8eec3a85-a6b7-4c3b-b024-f08cda0b9306

import Definitions.Def_MasulloRH_WindowLaplaceGram
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set MasulloRH.WindowLaplaceGram
open scoped ComplexConjugate

theorem solution (c b : ℝ) (s z : ℂ) (hs : |s.re-c| < b) (hz : |z.re-c| < b) :
    Integrable (fun x : ℝ => wave c b s x * conj (wave c b z x)) ∧
    (∫ x : ℝ, wave c b s x * conj (wave c b z x)) = kernel c b s z := by
  let f (x : ℝ) := wave c b s x * conj (wave c b z x)
  let l : ℂ := s + conj z - ((2*(c-b) : ℝ) : ℂ)
  let r : ℂ := s + conj z - ((2*(c+b) : ℝ) : ℂ)
  have hl : 0 < l.re := by
    simp only [l,Complex.sub_re,Complex.add_re,Complex.conj_re,Complex.ofReal_re]
    linarith [(abs_lt.mp hs).1,(abs_lt.mp hz).1]
  have hr : r.re < 0 := by
    simp only [r,Complex.sub_re,Complex.add_re,Complex.conj_re,Complex.ofReal_re]
    linarith [(abs_lt.mp hs).2,(abs_lt.mp hz).2]
  have left (x : ℝ) (hx : x ∈ Iic (0 : ℝ)) : f x = Complex.exp (l*x) := by
    change x ≤ 0 at hx
    dsimp only [f,wave,l]
    rw [← Complex.exp_conj,← Complex.exp_add]
    simp only [map_sub,map_mul,Complex.conj_ofReal,abs_of_nonpos hx]
    push_cast
    congr 1;ring
  have right (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) : f x = Complex.exp (r*x) := by
    change 0 < x at hx
    dsimp only [f,wave,r]
    rw [← Complex.exp_conj,← Complex.exp_add]
    simp only [map_sub,map_mul,Complex.conj_ofReal,abs_of_nonneg (le_of_lt hx)]
    push_cast
    congr 1;ring
  have hi₁ := (integrableOn_congr_fun left measurableSet_Iic).2 (integrableOn_exp_mul_complex_Iic hl 0)
  have hi₂ := (integrableOn_congr_fun right measurableSet_Ioi).2 (integrableOn_exp_mul_complex_Ioi hr 0)
  have hi : Integrable f := by simpa using integrableOn_union.mpr ⟨hi₁,hi₂⟩
  refine ⟨hi,?_⟩
  change (∫ x : ℝ, f x) = _
  rw [← integral_add_compl measurableSet_Iic hi,compl_Iic,
    setIntegral_congr_fun measurableSet_Iic left,setIntegral_congr_fun measurableSet_Ioi right,
    integral_exp_mul_complex_Iic hl,integral_exp_mul_complex_Ioi hr]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,kernel]
  have h : ((2*(c+b) : ℝ) : ℂ) - (s+conj z) = -r := by dsimp only [r];ring
  rw [h,div_neg,neg_div]
