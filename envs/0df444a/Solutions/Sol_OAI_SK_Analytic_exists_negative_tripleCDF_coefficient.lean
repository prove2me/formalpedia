-- Prove2me | solution 1 for OAI.SK.Analytic.exists_negative_tripleCDF_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T05:19:19.805567+00:00
-- url     : https://prove2.me/submissions/5e40ac1e-88c1-416e-9bb1-d41983572b6d

import Mathlib
import Definitions.Def_OAIQ036S006
import Theorems.Thm_OAI_SK_Analytic_exists_scalarCDFParisi_minimizer_locking_data

section
-- module Solutions.OAIQ036_SK.SKBarriers_Parisi_CDFZeroSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem cdf_pos_of_zero_mem_support (μ : ProbabilityMeasure ℝ)
    (h0 : (0:ℝ)∈(μ : Measure ℝ).support) {s : ℝ} (hs : 0 < s) :
    0 < cdf (μ : Measure ℝ) s := by
  have H : 0<(μ : Measure ℝ) (Iic s) :=
    (Measure.mem_support_iff_forall (μ:=(μ : Measure ℝ)) 0).mp h0 _ (Iic_mem_nhds hs)
  rw [cdf_eq_real,measureReal_def]
  exact ENNReal.toReal_pos H.ne' (measure_ne_top _ _)

end SK.Analytic

end
end

end OAI
end

section
-- module Solutions.OAIQ036_SK.SKBarriers_Locking_TripleNegativeCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem continuousAt_small_interval {f : ℝ → ℝ} (hf : ContinuousAt f 0)
    {b L : ℝ} (hb : f 0 < b) (hL : 0 < L) :
    ∃ e ∈ Ioo (0:ℝ) L, ∀ x ∈ Icc (0:ℝ) e, f x < b := by
  obtain ⟨d,hd,hf'⟩ := Metric.eventually_nhds_iff.mp (hf.eventually_lt continuousAt_const hb)
  refine ⟨min L d/2,⟨by positivity,?_⟩,?_⟩
  · have H := min_le_left L d; linarith [lt_min hL hd]
  · intro x hx
    apply hf'
    rw [Real.dist_eq,sub_zero,abs_of_nonneg hx.1]
    have H := min_le_right L d
    linarith [hx.2]

theorem cdfArea_antitone {α : ℝ → ℝ} (hm : Monotone α) (ha : ∀ z,0 ≤ α z)
    {h q : ℝ} (hhq : h ≤ q) : (∫ z in q..1,α z) ≤ ∫ z in h..1,α z := by
  have H := intervalIntegral.integral_add_adjacent_intervals (hm.intervalIntegrable (μ:=volume) (a:=h) (b:=q))
    (hm.intervalIntegrable (μ:=volume) (a:=q) (b:=1))
  have H' := intervalIntegral.integral_nonneg (μ:=volume) hhq (fun z _ => ha z)
  linarith

theorem exists_negative_tripleCDF_coefficient_oai {β : ℝ} (hβ : 0 < β)
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    ∃ μ : ProbabilityMeasure ℝ, (μ : Measure ℝ) (Icc (0:ℝ) 1)=1 ∧
      scalarCDFParisi β (cdf (μ : Measure ℝ))=finiteParisiInf β ∧
      ∃ s₁ s₂ τ r₀ c : ℝ, 0 < s₁ ∧ s₁ < s₂ ∧ s₂ < h ∧ 0 < τ ∧
        0 < r₀ ∧ r₀ < s₁ ∧ 0 < c ∧
        ∀ r q : ℝ, r ∈ Icc (0:ℝ) r₀ → q ∈ Icc h 1 →
          |q-scalarCDFOverlap β (cdf (μ : Measure ℝ)) q| ≤ τ →
          tripleCDFTrialCoefficient β (cdf (μ : Measure ℝ)) (s₂-s₁)⁻¹ r s₁ s₂ q ≤ -c := by
  obtain ⟨μ,hμ,hmin,h0,hχ0,hβA,hstrict,hχ⟩ := exists_scalarCDFParisi_minimizer_locking_data hβ.ne'
  let α := cdf (μ : Measure ℝ)
  let A₀ : ℝ := ∫ z in (0:ℝ)..1,α z
  let Ah : ℝ := ∫ z in h..1,α z
  have ha (z) : α z ∈ Icc (0:ℝ) 1 := ⟨cdf_nonneg _ _,cdf_le_one _ _⟩
  have hAh : 0 ≤ Ah := intervalIntegral.integral_nonneg hh1 (fun z _ => (ha z).1)
  have hAA : Ah < A₀ := hstrict h hh
  have hA₀ : 0 < A₀ := hAh.trans_lt hAA
  have HB : β*A₀ ≤ 1 := by simpa only [abs_of_pos hβ] using hβA
  have Hprod : β^2*Ah*A₀ < 1 := by
    have H := mul_lt_mul_of_pos_left hAA (mul_pos (sq_pos_of_pos hβ) hA₀)
    have H' : (β*A₀)^2 ≤ 1 := pow_le_one₀ (mul_pos hβ hA₀).le HB
    nlinarith only [H,H']
  let g : ℝ → ℝ := fun s => β^2*Ah*(A₀+2*(β^2*s)+4*(β^2*s)^2)-1
  have hg : ContinuousAt g 0 := by dsimp [g]; fun_prop
  have hg0 : g 0 < 0 := by dsimp [g]; nlinarith only [Hprod]
  obtain ⟨s₂,hs₂,hgs⟩ := continuousAt_small_interval hg hg0 hh
  have hgs₂ : g s₂ < 0 := hgs s₂ ⟨hs₂.1.le,le_rfl⟩
  let s₁ := s₂/2
  have hs₁ : 0 < s₁ := half_pos hs₂.1
  have hs : s₁ < s₂ := by dsimp [s₁]; linarith [hs₂.1]
  let K := (s₂-s₁)⁻¹
  have hK : 0 ≤ K := inv_nonneg.mpr (sub_pos.mpr hs).le
  have hm : 0 < α s₁ := cdf_pos_of_zero_mem_support μ h0 hs₁
  let C := A₀+2*(β^2*s₂)+4*(β^2*s₂)^2
  have hC : 0 ≤ C := by exact add_nonneg (add_nonneg hA₀.le (mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg β) hs₂.1.le))) (mul_nonneg (by norm_num) (sq_nonneg _))
  let R : ℝ → ℝ := fun t => β^2*(Ah+t)*C-1
  let F : ℝ → ℝ := fun t => β^2*K*t+β^2*α s₁*R t
  have hR0 : R 0 < 0 := by simpa only [R,C,g,add_zero] using hgs₂
  have hF0 : F 0 < 0 := by
    dsimp [F]
    simpa only [mul_zero,zero_add] using mul_neg_of_pos_of_neg (mul_pos (sq_pos_of_pos hβ) hm) hR0
  let c₀ := -F 0/2
  have hc₀ : 0 < c₀ := by dsimp [c₀]; linarith
  have hFc : F 0 < -c₀ := by dsimp [c₀]; linarith
  have hF : ContinuousAt F 0 := by dsimp [F,R]; fun_prop
  obtain ⟨τ,hτ,hFτ⟩ := continuousAt_small_interval hF hFc zero_lt_one
  have HT : F τ < -c₀ := hFτ τ ⟨hτ.1.le,le_rfl⟩
  have hRτ : R τ < 0 := by
    have HP : 0 ≤ β^2*K*τ := mul_nonneg (mul_nonneg (sq_nonneg β) hK) hτ.1.le
    have HB : 0 < β^2*α s₁ := mul_pos (sq_pos_of_pos hβ) hm
    dsimp only [F] at HT
    nlinarith
  have hE : ContinuousAt (tripleTimeCommonError β K) 0 := by
    unfold tripleTimeCommonError
    fun_prop
  have hE0 : tripleTimeCommonError β K 0 < c₀/2 := by
    simp only [tripleTimeCommonError,mul_zero,zero_pow (by decide : 2≠0),add_zero,Real.sqrt_zero]
    linarith
  obtain ⟨r₀,hr₀,hEr⟩ := continuousAt_small_interval hE hE0 hs₁
  refine ⟨μ,hμ,hmin,s₁,s₂,τ,r₀,c₀/2,hs₁,hs,hs₂.2,hτ.1,hr₀.1,hr₀.2,
    half_pos hc₀,?_⟩
  intro r q hr hq he
  have hq' : q ∈ Icc (0:ℝ) 1 := ⟨hh.le.trans hq.1,hq.2⟩
  have Hdiff : α q*(q-scalarCDFOverlap β α q) ≤ τ := by
    calc
      _ ≤ α q*τ := mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans he) (ha q).1
      _ ≤ τ := mul_le_of_le_one_left hτ.1.le (ha q).2
  have Hmean : scalarCDFSusceptibilityAverage β α q ≤ Ah+τ := by
    have H := hχ q hq'
    have HA := cdfArea_antitone α.mono (fun z => (ha z).1) hq.1
    change scalarCDFSusceptibilityAverage β α q=(∫ z in q..1,α z)+α q*(q-scalarCDFOverlap β α q) at H
    dsimp only [Ah] at ⊢
    linarith
  have Hresponse : tripleCDFResponse β α s₂ q ≤ R τ := by
    unfold tripleCDFResponse
    change β^2*scalarCDFSusceptibilityAverage β α q*
      (scalarCDFHessian β α 0 1 0+2*(β^2*s₂)+4*(β^2*s₂)^2)-1 ≤ R τ
    rw [hχ0]
    exact sub_le_sub_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left Hmean (sq_nonneg β)) hC) 1
  have Hcoefficient : tripleCDFTrialCoefficient β α K r s₁ s₂ q ≤ F τ+tripleTimeCommonError β K r := by
    unfold tripleCDFTrialCoefficient
    rw [max_eq_right (Hresponse.trans hRτ.le),add_zero]
    have HA := hχ q hq'
    change scalarCDFSusceptibilityAverage β α q=(∫ z in q..1,α z)+α q*(q-scalarCDFOverlap β α q) at HA
    have H1 := mul_le_mul_of_nonneg_left Hdiff (mul_nonneg (sq_nonneg β) hK)
    have H2 := mul_le_mul_of_nonneg_left Hresponse (mul_pos (sq_pos_of_pos hβ) hm).le
    dsimp only [F]
    rw [HA,add_sub_cancel_left]
    nlinarith only [H1,H2]
  have Her := hEr r hr
  exact Hcoefficient.trans (le_of_lt (by linarith))

end SK.Analytic

end
end

end OAI
end

theorem solution : type_of% @OAI.SK.Analytic.exists_negative_tripleCDF_coefficient_oai := @OAI.SK.Analytic.exists_negative_tripleCDF_coefficient_oai
