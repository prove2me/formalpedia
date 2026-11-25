-- Prove2me | solution 1 for GlobalTheory.HkLocal.logDeriv_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:28:45.600489+00:00
-- url     : https://prove2.me/submissions/928515c8-7231-47f2-8388-9aa33acb2308

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormula
import Theorems.Thm_GlobalTheory_HkLocal_analyticOrderNatAt_comp_affine
import Theorems.Thm_GlobalTheory_LogDerivZeros_main
import Theorems.Thm_GlobalTheory_T_rayClassFamily_logDeriv_re_gt_one
import Theorems.Thm_GlobalTheory_T_rayClassLFunctionFamily_continuation_growth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.HkLocal
namespace GlobalTheory.HkLocal
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (t : ℝ), {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}.Finite ∧ (∑ᶠ w ∈ {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}, (analyticOrderNatAt (𝓕.F χ) w : ℝ)) ≤ C * 𝓕.ell t ∧ ∀ s : ℂ, ‖s - (5 / 4 + t * I)‖ ≤ 1 / 2 → 𝓕.F χ s ≠ 0 → ‖deriv (𝓕.F χ) s / 𝓕.F χ s - ∑ᶠ w ∈ {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}, (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)‖ ≤ C * 𝓕.ell t := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LogDerivZeros.main (5/7) (6/7) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨12 * C, by positivity, ?_⟩
  intro 𝓕 χ t
  obtain ⟨han, hLS, hgr, -⟩ := GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ
  set c : ℂ := 5 / 4 + t * I with hc
  have hcre : c.re = 5 / 4 := by simp [hc]
  have hcn : ‖c‖ ≤ 5 / 4 + |t| := by
    refine (norm_add_le _ _).trans ?_
    simp
  have hB : 4 ≤ 𝓕.B := 𝓕.B_ge
  have ht : 0 ≤ |t| := abs_nonneg t
  set ρ : ℂ := 7 / 10 with hρ
  have hρ0 : ρ ≠ 0 := by rw [hρ]; norm_num
  have hρn : ‖ρ‖ = 7 / 10 := by simp [hρ]
  have hre : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, 11 / 20 ≤ (c + ρ * z).re ∧ ‖ρ * z‖ ≤ 7 / 10 := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := by simpa using hz
    have h1 : ‖ρ * z‖ ≤ 7 / 10 := by rw [norm_mul, hρn]; linarith
    have := (abs_le.1 ((Complex.abs_re_le_norm _).trans h1)).1
    refine ⟨?_, h1⟩
    rw [add_re, hcre]; linarith
  have hf : AnalyticOnNhd ℂ (fun z => 𝓕.F χ (c + ρ * z)) (Metric.closedBall 0 1) := by
    intro z hz
    have h1 : AnalyticAt ℂ (𝓕.F χ) (c + ρ * z) :=
      han _ (show 1 / 2 < (c + ρ * z).re by linarith [(hre z hz).1])
    exact AnalyticAt.comp (g := 𝓕.F χ) (f := fun z => c + ρ * z) h1 (by fun_prop)
  have hlow : 1 / 100 ≤ ‖𝓕.F χ (c + ρ * 0)‖ := by
    have h1 : 1 < c.re := by rw [hcre]; norm_num
    have h2 := (GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ c h1).2.1
    rw [hcre] at h2
    rw [mul_zero, add_zero, (hLS c h1).2, norm_mul]
    have h3 : 1 / 4 ≤ ‖(if χ = 1 then c - 1 else 1 : ℂ)‖ := by
      split_ifs
      · have := (le_abs_self _).trans (Complex.abs_re_le_norm (c - 1))
        rw [sub_re, hcre, one_re] at this
        linarith
      · norm_num
    have h4 : 1 / 25 ≤ ‖LSeries (𝓕.aChi χ) c‖ := le_trans (by norm_num) h2
    calc (1 / 100 : ℝ) = (1 / 4) * (1 / 25) := by norm_num
      _ ≤ _ := by gcongr
  have hf0 : 𝓕.F χ (c + ρ * 0) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hlow
    linarith
  have hM : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      ‖𝓕.F χ (c + ρ * z)‖ ≤ 300 * 𝓕.B * (|t| + 3) ^ 2 := by
    intro z hz
    obtain ⟨h1, h2⟩ := hre z hz
    have hn : ‖c + ρ * z‖ + 1 ≤ |t| + 3 := by
      have := norm_add_le c (ρ * z)
      linarith
    refine (hgr _ h1).trans ?_
    gcongr
  obtain ⟨⟨hfin, hcnt⟩, hb⟩ := H _ _ hf hf0 hM
  have hset : {w : ℂ | ‖w - c‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0} =
      (fun z => c + ρ * z) '' {w : ℂ | ‖w‖ ≤ 6 / 7 ∧ 𝓕.F χ (c + ρ * w) = 0} := by
    ext w
    constructor
    · rintro ⟨h1, h2⟩
      have e : c + ρ * ((w - c) / ρ) = w := by field_simp; ring
      refine ⟨(w - c) / ρ, ⟨?_, by rw [e]; exact h2⟩, e⟩
      rw [norm_div, hρn, div_le_iff₀ (by norm_num)]
      linarith
    · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
      refine ⟨?_, h2⟩
      simp only [add_sub_cancel_left, norm_mul, hρn]
      linarith
  have hinj : Set.InjOn (fun z => c + ρ * z) {w : ℂ | ‖w‖ ≤ 6 / 7 ∧ 𝓕.F χ (c + ρ * w) = 0} :=
    fun a _ b _ h => mul_left_cancel₀ hρ0 (add_left_cancel h)
  have hlog : 1 + Real.log (300 * 𝓕.B * (|t| + 3) ^ 2 / ‖𝓕.F χ (c + ρ * 0)‖) ≤ 8 * 𝓕.ell t ∧
      0 ≤ 𝓕.ell t := by
    unfold LFam.ell
    set X : ℝ := 𝓕.B * (|t| + 2) with hX
    have hX8 : 8 ≤ X := by rw [hX]; nlinarith
    have hl1 : 1 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le (show 0 < X by linarith)]
      linarith [Real.exp_one_lt_d9]
    have hp : 0 < ‖𝓕.F χ (c + ρ * 0)‖ := norm_pos_iff.2 hf0
    have h8 : 300 * 𝓕.B * (|t| + 3) ^ 2 / ‖𝓕.F χ (c + ρ * 0)‖ ≤ X ^ 7 := by
      rw [div_le_iff₀ hp]
      have hX0 : 0 ≤ X := by linarith
      have h5 : (8 : ℝ) ^ 5 ≤ X ^ 5 := by gcongr
      have h6 : 4 * (𝓕.B * (|t| + 2) ^ 2) ≤ X ^ 2 := by
        rw [hX, mul_pow, pow_two 𝓕.B, mul_assoc]
        gcongr
      have h7 : (|t| + 3) ^ 2 ≤ (9 / 4) * (|t| + 2) ^ 2 := by nlinarith
      have h9 : 𝓕.B * (|t| + 3) ^ 2 ≤ 𝓕.B * ((9 / 4) * (|t| + 2) ^ 2) := by gcongr
      have h10 : 0 ≤ X ^ 2 := by positivity
      calc 300 * 𝓕.B * (|t| + 3) ^ 2 ≤ 8 ^ 5 * X ^ 2 * (1 / 100) := by nlinarith
        _ ≤ X ^ 5 * X ^ 2 * ‖𝓕.F χ (c + ρ * 0)‖ := by gcongr
        _ = _ := by ring
    have h9 := Real.log_le_log (by positivity) h8
    rw [Real.log_pow] at h9
    push_cast at h9
    constructor <;> linarith
  obtain ⟨hlog, hell⟩ := hlog
  have hCl : C * (1 + Real.log (300 * 𝓕.B * (|t| + 3) ^ 2 / ‖𝓕.F χ (c + ρ * 0)‖)) ≤
      C * (8 * 𝓕.ell t) := by gcongr
  have hCe : 0 ≤ C * 𝓕.ell t := by positivity
  rw [hset]
  refine ⟨hfin.image _, ?_, ?_⟩
  · rw [finsum_mem_image hinj]
    simp only [analyticOrderNatAt_comp_affine _ _ _ _ hρ0] at hcnt
    refine hcnt.trans (hCl.trans ?_)
    linarith
  · intro s hs hLs
    have e : c + ρ * ((s - c) / ρ) = s := by field_simp; ring
    have hz : ‖(s - c) / ρ‖ ≤ 5 / 7 := by
      rw [norm_div, hρn, div_le_iff₀ (by norm_num)]
      linarith
    have hb' := hb ((s - c) / ρ) hz (by simpa only [e] using hLs)
    have hsre : 1 / 2 < s.re := by
      have := (hre ((s - c) / ρ) (by simpa only [mem_closedBall_zero_iff] using hz.trans (by norm_num))).1
      rw [e] at this
      linarith
    have hder : deriv (fun z => 𝓕.F χ (c + ρ * z)) ((s - c) / ρ) = ρ * deriv (𝓕.F χ) s := by
      have hd : HasDerivAt (fun z : ℂ => c + ρ * z) ρ ((s - c) / ρ) := by
        simpa using ((hasDerivAt_id ((s - c) / ρ)).const_mul ρ).const_add c
      have h1 : HasDerivAt (𝓕.F χ) (deriv (𝓕.F χ) s) (c + ρ * ((s - c) / ρ)) := by
        rw [e]; exact (han s hsre).differentiableAt.hasDerivAt
      have := (HasDerivAt.comp ((s - c) / ρ) h1 hd).deriv
      rw [mul_comm] at this
      exact this
    rw [finsum_mem_image hinj]
    simp only [analyticOrderNatAt_comp_affine _ _ _ _ hρ0, hder, e] at hb'
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hb' ⊢
    have e2 : ∀ w : ℂ, (analyticOrderNatAt (𝓕.F χ) (c + ρ * w) : ℂ) / ((s - c) / ρ - w) =
        ρ * ((analyticOrderNatAt (𝓕.F χ) (c + ρ * w) : ℂ) / (s - (c + ρ * w))) := by
      intro w
      have : s - (c + ρ * w) = ρ * ((s - c) / ρ - w) := by field_simp; ring
      rw [this, ← mul_div_assoc, mul_div_mul_left _ _ hρ0]
    simp only [e2] at hb'
    rw [← Finset.mul_sum, mul_div_assoc, ← mul_sub, norm_mul, hρn] at hb'
    have := hb'.trans hCl
    linarith
end GlobalTheory.HkLocal
