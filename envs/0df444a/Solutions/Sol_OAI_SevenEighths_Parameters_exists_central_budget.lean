-- Prove2me | solution 1 for OAI.SevenEighths.Parameters.exists_central_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:23:57.296191+00:00
-- url     : https://prove2.me/submissions/396d979a-d758-4d3d-82f3-7baa8729eded

import Definitions.Def_OAI_NumberTheory_DirichletL_ParametersDetectorScales
import Definitions.Def_OAI_NumberTheory_DirichletL_ParametersCentralBudget

set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.Parameters
namespace OAI.SevenEighths.Parameters
theorem _root_.solution (Δ : ℝ) (hΔ : 0<Δ) :
    ∃ t : ℝ,0<t ∧ t<Δ/4 ∧ t≤1/100000000 ∧
      (0:ℝ)<1/200 ∧ (1/200:ℝ)<1/100 ∧
      (13/16:ℝ)+t+2*t≤7/8 ∧ (7/8:ℝ)≤37/42 ∧ t≤3/16 ∧
      0<Δ-t/4 ∧ Δ-t/4<Δ ∧
      (3/16+Δ-t+t/8+t/8 : ℝ)≤3/16+(Δ-t/4) ∧
      ∀N : ℕ,∃allowance : ℝ,0<allowance ∧
      ∀ε e eps : ℝ,0≤ε → ε≤allowance → 0≤e → e≤allowance →
        0≤eps → eps≤allowance →
        159*ε+t+t+7*t≤1/32 ∧
        (13/16)*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
          (26*e+(N+8)*eps+t+t/6)+(t+t+t)+t≤49/440640 := by
  let t := min (Δ/8) (1/100000000)
  have ht : 0<t := lt_min (by positivity) (by norm_num)
  have htΔ : t≤Δ/8 := min_le_left _ _
  have ht1 : t≤1/100000000 := min_le_right _ _
  refine ⟨t,ht,by linarith,ht1,by norm_num,by norm_num,by linarith,
    by norm_num,by linarith,by linarith,by linarith,by linarith,?_⟩
  intro N
  let allowance := t/((N:ℝ)+2000)
  have hden : 0<(N:ℝ)+2000 := by positivity
  have ha : 0<allowance := div_pos ht hden
  have ha0 : allowance≤t/2000 := div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N])
  have hap : allowance*((N:ℝ)+2000)=t := by dsimp [allowance];field_simp
  refine ⟨allowance,ha,?_⟩
  intro ε e eps hε hεa he hea heps hepsa
  have hεt : 2000*ε≤t := by linarith
  have het : 2000*e≤t := by linarith
  have hepsN : ((N:ℝ)+2000)*eps≤t := by
    have h := mul_le_mul_of_nonneg_left hepsa hden.le
    nlinarith
  have heps8 : ((N:ℝ)+8)*eps≤t := by nlinarith
  constructor <;> nlinarith
end OAI.SevenEighths.Parameters
