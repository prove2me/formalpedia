-- Prove2me | solution 1 for OAI.MetricKMedian.Preparation.exists_rational_all_parameters_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:11:17.778143+00:00
-- url     : https://prove2.me/submissions/0ba03f37-df9c-4d07-ae47-15ba0f12cf79

import Mathlib
import Definitions.Def_OAIQ035K011
import Definitions.Def_OAIQ035K033
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_le_half_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.Analytic

theorem texp_integrable (x : ℝ) :
    IntervalIntegrable (fun t : ℝ => t * Real.exp (-t * x)) MeasureTheory.volume 0 1 := by
  apply Continuous.intervalIntegrable
  fun_prop

theorem exp_neg_half_le_P {x : ℝ} (hx : 0 ≤ x) : Real.exp (-x) / 2 ≤ P x := by
  have hint : IntervalIntegrable (fun t : ℝ => t * Real.exp (-x))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (a := (0 : ℝ)) (b := 1) (by norm_num) hint (texp_integrable x) (fun t ht =>
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [ht.2])) ht.1)
  rw [intervalIntegral.integral_mul_const] at h
  norm_num at h
  unfold P
  simp only [neg_mul]
  linarith

theorem P_pos {x : ℝ} (hx : 0 ≤ x) : 0 < P x := by
  exact lt_of_lt_of_le (div_pos (Real.exp_pos _) (by norm_num)) (exp_neg_half_le_P hx)

end MetricKMedian.Analytic


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparationParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation

theorem parameter_envelope_bounds {a g : ℝ} (ha : 0 < a) (ha32 : a ≤ 1/32)
    (hg : 0 < g) (hg14 : g ≤ a^14) :
    shortfallFactor (1-a) (a^6) g ≤ 9*a^6 ∧
    failureFactor (a^6) g ≤ 8*a^8 ∧
    failureFactor (a^6) g < 1/2 ∧
    nearFactor (1-a) ((a^2+1+a)/a^4) (a^6) g ≤ parameterEnvelopeNear a := by
  have ha1 : a ≤ 1 := by linarith only [ha32]
  have hp0 : 0 < 1-a := by linarith only [ha32]
  have hp2 : (1/2:ℝ) ≤ 1-a := by linarith only [ha32]
  have ha6 : a^6 ≤ 1 := pow_le_one₀ ha.le ha1
  have ha76 : a^7 ≤ a^6 := pow_le_pow_of_le_one ha.le ha1 (by decide)
  have ha8 : a^8 ≤ a := by simpa only [pow_one] using
    (pow_le_pow_of_le_one ha.le ha1 (show 1 ≤ 8 by decide))
  have hroot : Real.sqrt g ≤ a^7 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    simpa only [← pow_mul] using hg14
  have hrootp : Real.sqrt (g/(1-a)) ≤ 2*a^7 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [show (2*a^7)^2=4*a^14 by ring]
    apply (div_le_iff₀ hp0).mpr
    have he := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ a^14 by positivity)
    nlinarith only [he,hg14,pow_nonneg ha.le 14]
  have hrootγ : Real.sqrt (g*(1+a^6)) ≤ 2*a^7 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [show (2*a^7)^2=4*a^14 by ring]
    have he := mul_le_mul_of_nonneg_left ha6 hg.le
    nlinarith only [he,hg14,hg.le]
  have hdiv : (a^6+Real.sqrt (g*(1+a^6)))/(1-a) ≤ 2*(a^6+2*a^7) := by
    apply (div_le_iff₀ hp0).mpr
    have he := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ a^6+2*a^7 by positivity)
    nlinarith only [he,hrootγ]
  have hH : shortfallFactor (1-a) (a^6) g ≤ 9*a^6 := by
    dsimp only [shortfallFactor]
    linarith only [hroot,hrootp,hdiv,ha76]
  have hρ : failureFactor (a^6) g ≤ 8*a^8 := by
    dsimp only [failureFactor]
    apply (div_le_iff₀ (show 0 < a^6 by positivity)).mpr
    have he := mul_le_mul_of_nonneg_left ha6 hg.le
    have hid : 8*a^8*a^6=8*a^14 := by ring
    rw [hid]
    nlinarith only [he,hg14]
  refine ⟨hH,hρ,by linarith only [hρ,ha8,ha32],?_⟩
  dsimp only [nearFactor,parameterEnvelopeNear]
  apply add_le_add le_rfl
  have he := mul_le_mul_of_nonneg_left hH (show 0 ≤ (a^2+1+a)/a^4 by positivity)
  apply he.trans_eq
  field_simp

theorem parameter_envelope_continuous : ContinuousAt parameterEnvelope 0 := by
  unfold parameterEnvelope parameterEnvelopeFar parameterEnvelopeNear
  fun_prop (disch := norm_num)

theorem parameter_envelope_zero : parameterEnvelope 0=1 := by
  norm_num [parameterEnvelope,parameterEnvelopeFar,parameterEnvelopeNear]

theorem exists_preparation_parameters {η : ℝ} (hη : 0 < η) :
    ∃ δ M T₁ γ : ℚ,
      0 < (δ:ℝ) ∧ (δ:ℝ) ≤ 1/4 ∧ 0 < (M:ℝ) ∧ 0 < (T₁:ℝ) ∧
      0 < (γ:ℝ) ∧ (γ:ℝ) ≤ 1 ∧
      1/((M:ℝ)*(δ:ℝ)) ≤ 1/8 ∧
      (M:ℝ)/((δ:ℝ)*(T₁:ℝ)) ≤ 1/4 ∧
      ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ g : ℝ, 0 < g → g ≤ g₀ →
        failureFactor (γ:ℝ) g < 1/2 ∧
        max (farFactor (δ:ℝ) (1-1/((M:ℝ)*(δ:ℝ)))
              ((M:ℝ)/((δ:ℝ)*(T₁:ℝ))) ((M:ℝ)/(T₁:ℝ)) (γ:ℝ))
          (nearFactor (1-1/((M:ℝ)*(δ:ℝ))) ((M:ℝ)+(1+(δ:ℝ))*(T₁:ℝ)) (γ:ℝ) g)
          /(1-failureFactor (γ:ℝ) g) ≤ 1+η := by
  have hev := parameter_envelope_continuous.eventually_lt
    (continuousAt_const (y := 1+η)) (by rw [parameter_envelope_zero]; linarith only [hη])
  obtain ⟨r,hr,hev⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨a,ha,har⟩ := exists_rat_btwn (lt_min hr (show (0:ℝ) < 1/32 by norm_num))
  have ha32 : (a:ℝ) ≤ 1/32 := (har.trans_le (min_le_right _ _)).le
  have hclose : parameterEnvelope (a:ℝ) < 1+η := hev (by
    rw [Real.dist_eq,sub_zero,abs_of_pos ha]
    exact har.trans_le (min_le_left _ _))
  have hanz : (a:ℝ) ≠ 0 := ha.ne'
  have ha1 : (a:ℝ) ≤ 1 := by linarith only [ha32]
  have htheta : 1/((1/(a:ℝ)^2)*(a:ℝ))=(a:ℝ) := by field_simp
  have halpha : (1/(a:ℝ)^2)/((a:ℝ)*(1/(a:ℝ)^4))=(a:ℝ) := by field_simp
  have hbeta : (1/(a:ℝ)^2)/(1/(a:ℝ)^4)=(a:ℝ)^2 := by field_simp
  have hQ : (1/(a:ℝ)^2)+(1+(a:ℝ))*(1/(a:ℝ)^4)=
      ((a:ℝ)^2+1+(a:ℝ))/(a:ℝ)^4 := by field_simp; ring
  refine ⟨a,1/a^2,1/a^4,a^6,?_⟩
  push_cast
  rw [htheta,halpha,hbeta,hQ]
  refine ⟨ha,by linarith only [ha32],by positivity,by positivity,by positivity,
    pow_le_one₀ ha.le ha1,by linarith only [ha32],by linarith only [ha32],
    (a:ℝ)^14,by positivity,?_⟩
  intro g hg hg14
  obtain ⟨_,hρ,hρhalf,hnear⟩ := parameter_envelope_bounds ha ha32 hg hg14
  refine ⟨hρhalf,?_⟩
  have hfar : farFactor (a:ℝ) (1-(a:ℝ)) (a:ℝ) ((a:ℝ)^2) ((a:ℝ)^6)=
      parameterEnvelopeFar (a:ℝ) := by
    unfold farFactor parameterEnvelopeFar
    congr 1
    field_simp
  have ha8 : (a:ℝ)^8 ≤ (a:ℝ) := by simpa only [pow_one] using
    (pow_le_pow_of_le_one ha.le ha1 (show 1 ≤ 8 by decide))
  have hden : 0 < 1-8*(a:ℝ)^8 := by linarith only [ha8,ha32]
  have hnonneg : 0 ≤ max (parameterEnvelopeFar (a:ℝ)) (parameterEnvelopeNear (a:ℝ)) := by
    apply le_trans _ (le_max_right _ _)
    unfold parameterEnvelopeNear
    have hp : 0 < 1-(a:ℝ) := by linarith only [ha32]
    positivity
  rw [hfar]
  calc
    _ ≤ max (parameterEnvelopeFar (a:ℝ)) (parameterEnvelopeNear (a:ℝ))/(1-failureFactor ((a:ℝ)^6) g) :=
      div_le_div_of_nonneg_right (max_le_max le_rfl hnear) (by linarith only [hρhalf])
    _ ≤ parameterEnvelope (a:ℝ) := div_le_div_of_nonneg_left hnonneg hden (by linarith only [hρ])
    _ ≤ 1+η := hclose.le

theorem all_fine_grids {g₀ : ℝ} (hg₀ : 0 < g₀) :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → 0 < Δ ∧ 0 < (1/(Δ:ℝ)) ∧ 1/(Δ:ℝ) ≤ g₀ := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 (1/g₀))
  refine ⟨N,?_⟩
  intro Δ hΔ
  have hD : 0 < (Δ:ℝ) := (lt_of_le_of_lt (le_max_left _ _) hN).trans_le (by exact_mod_cast hΔ)
  refine ⟨by exact_mod_cast hD,by positivity,?_⟩
  apply (div_le_iff₀ hD).mpr
  have hlarge : 1/g₀ < (Δ:ℝ) := (lt_of_le_of_lt (le_max_right _ _) hN).trans_le (by exact_mod_cast hΔ)
  exact ((div_lt_iff₀ hg₀).mp hlarge).le.trans_eq (mul_comm _ _)

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential

open Analytic

variable {I : Type*}

theorem savingsFraction_pos {g : ℝ} (hg : 0 < g) : 0 < savingsFraction g := by
  apply lt_min (by norm_num)
  exact div_pos (mul_pos (mul_pos (by norm_num) (P_pos (by norm_num))) hg)
    (by positivity)

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open PhysicalPotential

theorem horizon_error {N : ℝ} (hN : 0 < N) :
    (2*N)/(2*N^2)+5*(2*N^2)*Real.exp (-(2*N)/2) ≤ 61/N := by
  have he := Real.pow_div_factorial_le_exp N hN.le 3
  norm_num at he
  have ht : 5*(2*N^2)*Real.exp (-(2*N)/2) ≤ 60/N := by
    rw [show -(2*N)/2 = -N by ring,Real.exp_neg]
    apply (le_div_iff₀ hN).mpr
    have he' : N^3 ≤ 6*Real.exp N := by linarith only [he]
    have he'' := mul_le_mul_of_nonneg_right he' (inv_nonneg.mpr (Real.exp_pos N).le)
    rw [mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero N), mul_one] at he''
    nlinarith only [he'']
  have hid : (2*N)/(2*N^2)=1/N := by field_simp
  rw [hid]
  calc
    _ ≤ 1/N+60/N := add_le_add le_rfl ht
    _ = _ := by ring

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalRoundParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.FixedBatch
open PhysicalPotential

theorem exists_rational_grid_horizon {τ : ℝ} (hτ : 0 < τ) (D₀ : ℕ) :
    ∃ Δ : ℕ, ∃ Λ g : ℚ, D₀ ≤ Δ ∧ Even Δ ∧ 0 < Δ ∧ 0 < (Λ:ℝ) ∧
      0 < (g:ℝ) ∧ (g:ℝ) ≤ 1 ∧ (g:ℝ)*(Δ:ℝ)=1 ∧
      (Λ:ℝ)*(g:ℝ)+5*(Δ:ℝ)*Real.exp (-(Λ:ℝ)/2) ≤ τ/2 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max 1 (max (D₀:ℝ) (122/τ)))
  have hn1 : 1 < (n:ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hn0 : (0:ℝ) < n := by linarith only [hn1]
  have hnNat : 0 < n := by exact_mod_cast hn0
  have hnD : D₀ ≤ n := by
    have hh : (D₀:ℝ) < n := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hn
    exact_mod_cast hh.le
  have hnτ : 122/τ < n := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hn
  have hsmall : 61/(n:ℝ) ≤ τ/2 := by
    apply (div_le_iff₀ hn0).mpr
    have ht := (div_lt_iff₀ hτ).mp hnτ
    linarith only [ht]
  refine ⟨2*n^2,2*(n:ℚ),1/(2*(n:ℚ)^2),?_,even_two_mul _,by positivity,?_,?_,?_,?_,?_⟩
  · exact hnD.trans (by nlinarith only [sq_nonneg (n-1)])
  · push_cast; positivity
  · push_cast; positivity
  · push_cast
    exact (div_le_one (by positivity)).mpr (by nlinarith only [hn1])
  · push_cast; field_simp
  · push_cast
    simpa only [div_eq_mul_inv,one_mul] using (horizon_error hn0).trans hsmall

theorem exists_rational_parameters {τ : ℝ} (hτ : 0<τ) (D₀ : ℕ) :
    ∃ p : RationalParameters τ, D₀≤p.Δ ∧ Even p.Δ := by
  obtain ⟨Δ,Λ,g,hD,heven,hΔ,hΛ,hg,hg1,hunit,hgrid⟩ := exists_rational_grid_horizon hτ D₀
  have hΔr : (0:ℝ)<Δ := by exact_mod_cast hΔ
  have hC : 0<batchConstant Δ := by unfold batchConstant; positivity
  obtain ⟨φ,hφ,hφb⟩ := exists_rat_btwn (show (0:ℝ)< min 1 (τ/(8*(Λ:ℝ)*batchConstant Δ*(Δ:ℝ))) by positivity)
  have hφ1 : (φ:ℝ)≤1 := (hφb.trans_le (min_le_left _ _)).le
  have hφτ : 8*(Λ:ℝ)*batchConstant Δ*(Δ:ℝ)*(φ:ℝ)≤τ := by
    have ht := (le_div_iff₀ (by positivity : 0<8*(Λ:ℝ)*batchConstant Δ*(Δ:ℝ))).mp
      (hφb.trans_le (min_le_right _ _)).le
    nlinarith only [ht]
  let D : ℝ := 16*((Δ^2+Δ:ℕ):ℝ)+10
  let K : ℝ := 2*(g:ℝ)*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ))
  have hDpos : 0<D := by dsimp [D]; positivity
  have hKpos : 0<K := by dsimp [K]; positivity
  let r := min (1/4) (min (φ:ℝ) (min (savingsFraction (g:ℝ)/D) (min (1/K) ((φ:ℝ)/(16*(Δ:ℝ))))))
  have hr : 0 < r := by
    apply lt_min (by norm_num)
    apply lt_min hφ
    apply lt_min (div_pos (savingsFraction_pos hg) hDpos)
    exact lt_min (by positivity) (by positivity)
  obtain ⟨T,hT⟩ := exists_nat_gt (max 0 ((Λ:ℝ)/r))
  have hTr : (0:ℝ)<T := lt_of_le_of_lt (le_max_left _ _) hT
  let h : ℚ := Λ/T
  have hTh : (T:ℝ)*(h:ℝ)=(Λ:ℝ) := by dsimp only [h]; push_cast; field_simp
  have hh : 0<(h:ℝ) := by dsimp only [h]; push_cast; positivity
  have hhr : (h:ℝ) ≤ r := by
    have ht := (div_lt_iff₀ hr).mp (lt_of_le_of_lt (le_max_right _ _) hT)
    dsimp only [h]
    push_cast
    apply (div_le_iff₀ hTr).mpr
    linarith only [ht]
  have hh4 : (h:ℝ)≤1/4 := hhr.trans (min_le_left _ _)
  have hrest := hhr.trans (min_le_right _ _)
  have hhφ : (h:ℝ)≤(φ:ℝ) := hrest.trans (min_le_left _ _)
  have hrest' := hrest.trans (min_le_right _ _)
  have hhD : (h:ℝ)≤ savingsFraction (g:ℝ)/D := hrest'.trans (min_le_left _ _)
  have hrest'' := hrest'.trans (min_le_right _ _)
  have hhK : (h:ℝ)≤1/K := hrest''.trans (min_le_left _ _)
  have hhΔ : (h:ℝ)≤(φ:ℝ)/(16*(Δ:ℝ)) := hrest''.trans (min_le_right _ _)
  obtain ⟨β,hβ,hβb⟩ := exists_rat_btwn (show (0:ℝ)<τ*((2*(h:ℝ)*(g:ℝ))*(φ:ℝ)^2*(g:ℝ))/(96*(Δ:ℝ)^2*(T:ℝ)) by positivity)
  obtain ⟨ζ,hζ,hζb⟩ := exists_rat_btwn (show (0:ℝ)< min (1/4) (τ/(48*(Λ:ℝ))) by positivity)
  have hζ1 : (ζ:ℝ)<1/4 := hζb.trans_le (min_le_left _ _)
  have hζτ : 48*(Λ:ℝ)*(ζ:ℝ)≤τ := by
    have ht := (le_div_iff₀ (by positivity : 0<48*(Λ:ℝ))).mp
      (hζb.trans_le (min_le_right _ _)).le
    nlinarith only [ht]
  have hprob : (1+(φ:ℝ))*(2*(h:ℝ)*(g:ℝ))≤1 := by
    have hp : 1+(φ:ℝ)≤2 := by linarith only [hφ1]
    have htwo : 2*(h:ℝ)*(g:ℝ)≤1/2 :=
      (mul_le_of_le_one_right (by positivity) hg1).trans (by linarith only [hh4])
    have ht := mul_le_mul_of_nonneg_right hp (show 0≤2*(h:ℝ)*(g:ℝ) by positivity)
    linarith only [ht,htwo]
  have hsmall : D*(h:ℝ)≤ savingsFraction (g:ℝ) := by
    have ht := (le_div_iff₀ hDpos).mp hhD
    linarith only [ht]
  have hsurv : (2*(h:ℝ)*(g:ℝ))*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ))≤1 := by
    have ht := (le_div_iff₀ hKpos).mp hhK
    dsimp only [K] at ht
    nlinarith only [ht]
  have hcount : 8*(2*(h:ℝ)*(g:ℝ))*(Δ:ℝ)≤(φ:ℝ)*(g:ℝ) := by
    have ht := (le_div_iff₀ (by positivity : 0<16*(Δ:ℝ))).mp hhΔ
    have hhg := mul_le_mul_of_nonneg_right ht hg.le
    nlinarith only [hhg]
  have herr : (T:ℝ)*(h:ℝ)*((g:ℝ)+12*(ζ:ℝ))+
      (T:ℝ)*batchConstant Δ*(h:ℝ)*((φ:ℝ)+(h:ℝ))*(Δ:ℝ)+
      5*(Δ:ℝ)*Real.exp (-(T:ℝ)*(h:ℝ)/2)≤τ := by
    have hc := mul_le_mul_of_nonneg_left hhφ (show 0≤(Λ:ℝ)*batchConstant Δ*(Δ:ℝ) by positivity)
    have ht : (Λ:ℝ)*batchConstant Δ*((φ:ℝ)+(h:ℝ))*(Δ:ℝ)≤τ/4 := by
      nlinarith only [hc,hφτ]
    have heq : (T:ℝ)*batchConstant Δ*(h:ℝ)*((φ:ℝ)+(h:ℝ))*(Δ:ℝ)=
        (Λ:ℝ)*batchConstant Δ*((φ:ℝ)+(h:ℝ))*(Δ:ℝ) := by
      rw [show (T:ℝ)*batchConstant Δ*(h:ℝ)=(T:ℝ)*(h:ℝ)*batchConstant Δ by ring,hTh]
    rw [heq,hTh,show -(T:ℝ)*(h:ℝ)/2=-(Λ:ℝ)/2 by rw [neg_mul,hTh]]
    nlinarith only [ht,hgrid,hζτ]
  have hf : (T:ℝ)*(96*(Δ:ℝ)^2*(β:ℝ)/((2*(h:ℝ)*(g:ℝ))*(φ:ℝ)^2*(g:ℝ)))≤τ := by
    have hb := (le_div_iff₀ (by positivity : 0<96*(Δ:ℝ)^2*(T:ℝ))).mp hβb.le
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hb]
  have happrox : ∀ t : Fin T, ∃ q : ℚ, 0<(q:ℝ) ∧ (q:ℝ)≤1/2 ∧
      |(q:ℝ)-Analytic.P (Real.exp (-(t.val:ℝ)*(h:ℝ)))|≤(ζ:ℝ) := by
    intro t
    let a := Analytic.P (Real.exp (-(t.val:ℝ)*(h:ℝ)))
    have ha : 0<a := Analytic.P_pos (Real.exp_pos _).le
    have ha1 : a≤1/2 := Analytic.P_le_half_s35 (Real.exp_pos _).le
    obtain ⟨q,hql,hqr⟩ := exists_rat_btwn (show max 0 (a-(ζ:ℝ))<a from max_lt ha (by linarith only [hζ]))
    refine ⟨q,(le_max_left _ _).trans_lt hql,hqr.le.trans ha1,?_⟩
    rw [abs_of_neg (sub_neg.mpr hqr)]
    have ht := (le_max_right _ _).trans_lt hql
    linarith only [ht]
  choose taper ht0 ht1 hte using happrox
  exact ⟨⟨Δ,g,h,φ,β,ζ,T,taper,hΔ,hg,hg1,hunit,hh,by linarith only [hh4],hφ,hφ1,hβ,hζ,hζ1,
    hprob,hsmall,hsurv,hcount,herr,hf,ht0,ht1,hte⟩,hD,heven⟩

end MetricKMedian.FixedBatch
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalAllParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation

 theorem exists_rational_all_parameters_s35_oai {η τ : ℝ} (hη : 0<η) (hτ : 0<τ) :
    Nonempty (RationalAllParameters η τ) := by
  obtain ⟨δ,M,T₁,γ,hδ,hδ1,hM,hT,hγ,hγ1,hθ,hα,g₀,hg₀,hg⟩ := exists_preparation_parameters hη
  obtain ⟨D₀,hD⟩ := all_fine_grids hg₀
  obtain ⟨q,hq,heven⟩ := FixedBatch.exists_rational_parameters hτ D₀
  have heq : (q.g:ℝ)=1/(q.Δ:ℝ) := (eq_div_iff (by exact_mod_cast q.Δpos.ne')).mpr q.unit
  have hsmall : (q.g:ℝ) ≤ g₀ := heq ▸ (hD q.Δ hq).2.2
  have he := hg (q.g:ℝ) q.gpos hsmall
  exact ⟨{
    round := q
    even := heven
    M := M
    δ := δ
    γ := γ
    T₁ := T₁
    hM := by exact_mod_cast hM
    hδ := by exact_mod_cast hδ
    hδ1 := hδ1
    hγ := by exact_mod_cast hγ
    hγ1 := by exact_mod_cast hγ1
    hT := by exact_mod_cast hT
    hθ := hθ
    hα := hα
    failure := by linarith only [he.1]
    error := he.2 }⟩

end MetricKMedian.Preparation
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Preparation.exists_rational_all_parameters_s35_oai := @OAI.MetricKMedian.Preparation.exists_rational_all_parameters_s35_oai
