-- Prove2me | solution 1 for MeasureTheory.exists_contDiff_integral_integral_mul_log_sq_linear_add_sq_mul_sq_eq_add_abs_mul_of_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/479b1ca2-09ea-5a6b-a603-df245d53127d

import Mathlib
import Theorems.Thm_MeasureTheory_exists_contDiff_integral_mul_log_sq_add_sq_eq_add_abs_mul_of_hasCompactSupport
import Theorems.Thm_MeasureTheory_contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_contDiff_integral_integral_mul_log_sq_linear_add_sq_mul_sq_eq_add_abs_mul_of_hasCompactSupport

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open MeasureTheory

noncomputable section

namespace ParamLogPot

section Bump
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_smooth_bump {S U : Set E} (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ (∀ x ∈ S, χ x = 1) ∧ tsupport χ ⊆ U := by
  obtain ⟨R, hR⟩ := hS.isBounded.subset_ball 0
  set U' : Set E := U ∩ Metric.ball 0 R with hU'
  have hU'o : IsOpen U' := hU.inter Metric.isOpen_ball
  have hd : Disjoint U'ᶜ S := by
    rw [Set.disjoint_left]
    intro x hx hxS
    exact hx ⟨hSU hxS, hR hxS⟩
  obtain ⟨f, hf0, hf1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (modelWithCornersSelf ℝ E) (n := (⊤ : ℕ∞)) hU'o.isClosed_compl hS.isClosed hd
  obtain ⟨V, hVo, hsV, hV⟩ := eventually_nhdsSet_iff_exists.mp hf0
  have hts : tsupport (⇑f) ⊆ U' := by
    refine (closure_minimal (fun x hx => ?_) hVo.isClosed_compl).trans (Set.compl_subset_comm.mp hsV)
    exact fun hxV => hx (hV x hxV)
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, ?_, fun x hx => hf1.self_of_nhdsSet x hx,
    hts.trans Set.inter_subset_left⟩
  exact IsCompact.of_isClosed_subset (isCompact_closedBall 0 R) (isClosed_tsupport _)
    (hts.trans (Set.inter_subset_right.trans Metric.ball_subset_closedBall))
end Bump

theorem contDiff_paramIntegral
    {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q] [FiniteDimensional ℝ Q]
    {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]
    (F : Q × Y → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (w : Y → ℝ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : Q => ∫ y, (w y : ℝ) • F (q, y) ∂μ) := by
  rw [contDiff_iff_contDiffAt]
  intro q₀
  let χ' : ContDiffBump q₀ := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨w', hw', hw'c, hw'1, -⟩ := exists_smooth_bump (E := Y) hwc isOpen_univ (Set.subset_univ _)
  let Ψ : Y × Q → ℂ := fun z => ((w' z.1 * (χ' : Q → ℝ) z.2 : ℝ)) • F (z.2, z.1)
  have hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ := by
    refine ContDiff.smul ((hw'.comp contDiff_fst).mul (χ'.contDiff.comp contDiff_snd)) ?_
    exact hF.comp (contDiff_snd.prodMk contDiff_fst)
  have hΨc : HasCompactSupport Ψ := by
    refine HasCompactSupport.intro (hw'c.prod χ'.hasCompactSupport) fun z hz => ?_
    simp only [Set.mem_prod, not_and_or] at hz
    show ((w' z.1 * (χ' : Q → ℝ) z.2 : ℝ)) • F (z.2, z.1) = 0
    rcases hz with h | h
    · rw [image_eq_zero_of_notMem_tsupport h, zero_mul, zero_smul]
    · rw [image_eq_zero_of_notMem_tsupport h, mul_zero, zero_smul]
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun q : Q => ∫ y, (w y) • Ψ (id y, q) ∂μ) :=
    MeasureTheory.contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport μ id continuous_id
      w hw.continuous hwc Ψ hΨ hΨc
  have hGI : ∀ q : Q, (∫ y, (w y) • Ψ (id y, q) ∂μ) =
      (((χ' : Q → ℝ) q : ℝ) : ℂ) * ∫ y, (w y : ℝ) • F (q, y) ∂μ := by
    intro q
    rw [← Complex.real_smul, ← integral_smul]
    congr 1
    funext y
    show (w y) • (((w' y * (χ' : Q → ℝ) q : ℝ)) • F (q, y)) = ((χ' : Q → ℝ) q) • ((w y : ℝ) • F (q, y))
    by_cases hy : w y = 0
    · rw [hy, zero_smul, zero_smul, smul_zero]
    · rw [hw'1 y (subset_tsupport _ hy), one_mul, smul_comm]
  have hev : (fun q : Q => ∫ y, (w y : ℝ) • F (q, y) ∂μ) =ᶠ[nhds q₀]
      fun q : Q => ∫ y, (w y) • Ψ (id y, q) ∂μ := by
    filter_upwards [Metric.closedBall_mem_nhds q₀ one_pos] with q hq
    rw [hGI q, χ'.one_of_mem_closedBall hq, Complex.ofReal_one, one_mul]
  exact hG.contDiffAt.congr_of_eventuallyEq hev

theorem abs_log_sq_add_sq_le (s ρ : ℝ) :
    |Real.log (s ^ 2 + ρ ^ 2)| ≤ |Real.log (s ^ 2)| + Real.log (1 + s ^ 2) + Real.log (1 + ρ ^ 2) + |Real.log (ρ ^ 2)| := by
  have h1 : 0 ≤ Real.log (1 + s ^ 2) := Real.log_nonneg (by nlinarith)
  have h2 : 0 ≤ Real.log (1 + ρ ^ 2) := Real.log_nonneg (by nlinarith)
  by_cases hs : s = 0
  · subst hs
    have e1 : ((0 : ℝ) ^ 2 + ρ ^ 2) = ρ ^ 2 := by ring
    have e2 : Real.log ((0 : ℝ) ^ 2) = 0 := by simp
    have e3 : Real.log (1 + (0 : ℝ) ^ 2) = 0 := by simp
    rw [e1, e2, e3, abs_zero, zero_add, zero_add]
    linarith [abs_nonneg (Real.log (ρ ^ 2))]
  have hs2 : 0 < s ^ 2 := by positivity
  by_cases hle : s ^ 2 + ρ ^ 2 < 1
  · have hlt0 : Real.log (s ^ 2 + ρ ^ 2) ≤ 0 := Real.log_nonpos (by positivity) hle.le
    have hge : Real.log (s ^ 2) ≤ Real.log (s ^ 2 + ρ ^ 2) := Real.log_le_log hs2 (by nlinarith)
    rw [abs_of_nonpos hlt0]
    have : |Real.log (s ^ 2)| = -Real.log (s ^ 2) := abs_of_nonpos (hge.trans hlt0)
    linarith [abs_nonneg (Real.log (ρ ^ 2))]
  · push Not at hle
    have hpos : 0 ≤ Real.log (s ^ 2 + ρ ^ 2) := Real.log_nonneg hle
    rw [abs_of_nonneg hpos]
    have hprod : s ^ 2 + ρ ^ 2 ≤ (1 + s ^ 2) * (1 + ρ ^ 2) := by nlinarith
    calc Real.log (s ^ 2 + ρ ^ 2) ≤ Real.log ((1 + s ^ 2) * (1 + ρ ^ 2)) :=
          Real.log_le_log (by linarith) hprod
      _ = Real.log (1 + s ^ 2) + Real.log (1 + ρ ^ 2) := Real.log_mul (by positivity) (by positivity)
      _ ≤ _ := by linarith [abs_nonneg (Real.log (s ^ 2)), abs_nonneg (Real.log (ρ ^ 2))]

theorem integrableOn_logBound' (R ρ : ℝ) :
    IntegrableOn (fun s : ℝ => |Real.log (s ^ 2)| + Real.log (1 + s ^ 2) + Real.log (1 + ρ ^ 2) + |Real.log (ρ ^ 2)|)
      (Set.Icc (-R) R) := by
  have h1 : IntervalIntegrable (fun s : ℝ => |Real.log (s ^ 2)|) volume (-R) R := by
    have : (fun s : ℝ => |Real.log (s ^ 2)|) = fun s => |(2 : ℝ) * Real.log s| := by
      funext s; rw [Real.log_pow]; norm_num
    rw [this]
    exact (intervalIntegral.intervalIntegrable_log'.const_mul 2).abs
  have hc : Continuous fun s : ℝ => Real.log (1 + s ^ 2) + Real.log (1 + ρ ^ 2) + |Real.log (ρ ^ 2)| := by
    refine (Continuous.add ?_ continuous_const).add continuous_const
    refine continuous_iff_continuousAt.mpr fun s => ?_
    exact (Real.continuousAt_log (by positivity)).comp (by fun_prop : Continuous fun s : ℝ => 1 + s ^ 2).continuousAt
  have h2 := hc.intervalIntegrable (μ := volume) (-R) R
  by_cases hR : 0 ≤ R
  · have := (h1.add h2)
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)] at this
    refine this.congr_fun (fun s _ => by ring) measurableSet_Icc
  · rw [Set.Icc_eq_empty (by linarith)]
    exact integrableOn_empty

section Shear
variable {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup V] [NormedSpace ℝ V]

def shear (c₀ : P → ℝ) (φ : P → (V →L[ℝ] ℝ)) : (P × V) × ℝ → P × (ℝ × V) :=
  fun y => (y.1.1, ((y.2 - φ y.1.1 y.1.2) * (c₀ y.1.1)⁻¹, y.1.2))

def unshear (c₀ : P → ℝ) (φ : P → (V →L[ℝ] ℝ)) : P × (ℝ × V) → (P × V) × ℝ :=
  fun x => ((x.1, x.2.2), c₀ x.1 * x.2.1 + φ x.1 x.2.2)

theorem shear_unshear (c₀ : P → ℝ) (φ : P → (V →L[ℝ] ℝ)) (hc₀0 : ∀ p, c₀ p ≠ 0) (x : P × (ℝ × V)) :
    shear c₀ φ (unshear c₀ φ x) = x := by
  obtain ⟨p, s, v⟩ := x
  show (p, ((c₀ p * s + φ p v - φ p v) * (c₀ p)⁻¹, v)) = (p, (s, v))
  rw [add_sub_cancel_right, mul_comm (c₀ p) s, mul_assoc, mul_inv_cancel₀ (hc₀0 p), mul_one]

theorem unshear_shear (c₀ : P → ℝ) (φ : P → (V →L[ℝ] ℝ)) (hc₀0 : ∀ p, c₀ p ≠ 0) (y : (P × V) × ℝ) :
    unshear c₀ φ (shear c₀ φ y) = y := by
  obtain ⟨⟨p, v⟩, u⟩ := y
  show ((p, v), c₀ p * ((u - φ p v) * (c₀ p)⁻¹) + φ p v) = ((p, v), u)
  rw [mul_comm (u - φ p v), ← mul_assoc, mul_inv_cancel₀ (hc₀0 p), one_mul, sub_add_cancel]

theorem shear_apply (c₀ : P → ℝ) (φ : P → (V →L[ℝ] ℝ)) (hc₀0 : ∀ p, c₀ p ≠ 0) (p : P) (s : ℝ) (v : V) :
    shear c₀ φ ((p, v), c₀ p * s + φ p v) = (p, (s, v)) :=
  shear_unshear c₀ φ hc₀0 (p, (s, v))

theorem contDiff_shear (c₀ : P → ℝ) (φ : P → (V →L[ℝ] ℝ)) (hc₀ : ContDiff ℝ (⊤ : ℕ∞) c₀)
    (hc₀0 : ∀ p, c₀ p ≠ 0) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : ContDiff ℝ (⊤ : ℕ∞) (shear c₀ φ) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun y : (P × V) × ℝ => φ y.1.1 y.1.2 :=
    (hφ.comp (contDiff_fst.comp contDiff_fst)).clm_apply (contDiff_snd.comp contDiff_fst)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun y : (P × V) × ℝ => (c₀ y.1.1)⁻¹ :=
    (hc₀.comp (contDiff_fst.comp contDiff_fst)).inv fun y => hc₀0 _
  exact (contDiff_fst.comp contDiff_fst).prodMk
    (((contDiff_snd.sub h1).mul h2).prodMk (contDiff_snd.comp contDiff_fst))

theorem contDiff_unshear (c₀ : P → ℝ) (φ : P → (V →L[ℝ] ℝ)) (hc₀ : ContDiff ℝ (⊤ : ℕ∞) c₀)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : ContDiff ℝ (⊤ : ℕ∞) (unshear c₀ φ) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun x : P × (ℝ × V) => φ x.1 x.2.2 :=
    (hφ.comp contDiff_fst).clm_apply (contDiff_snd.comp contDiff_snd)
  exact (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)).prodMk
    (((hc₀.comp contDiff_fst).mul (contDiff_fst.comp contDiff_snd)).add h1)

def shearHomeomorph (c₀ : P → ℝ) (φ : P → (V →L[ℝ] ℝ)) (hc₀ : ContDiff ℝ (⊤ : ℕ∞) c₀)
    (hc₀0 : ∀ p, c₀ p ≠ 0) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : (P × V) × ℝ ≃ₜ P × (ℝ × V) where
  toFun := shear c₀ φ
  invFun := unshear c₀ φ
  left_inv := unshear_shear c₀ φ hc₀0
  right_inv := shear_unshear c₀ φ hc₀0
  continuous_toFun := (contDiff_shear c₀ φ hc₀ hc₀0 hφ).continuous
  continuous_invFun := (contDiff_unshear c₀ φ hc₀ hφ).continuous

theorem coe_shearHomeomorph (c₀ : P → ℝ) (φ : P → (V →L[ℝ] ℝ)) (hc₀ : ContDiff ℝ (⊤ : ℕ∞) c₀)
    (hc₀0 : ∀ p, c₀ p ≠ 0) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ⇑(shearHomeomorph c₀ φ hc₀ hc₀0 hφ) = shear c₀ φ := rfl

end Shear

end ParamLogPot

end

namespace ParamLogPot

theorem abs_log_sq_add_sq_le_of_abs_le (u e M : ℝ) (hu : u ≠ 0) (he : |e| ≤ M) :
    |Real.log (u ^ 2 + e ^ 2)| ≤ |Real.log (u ^ 2)| + Real.log (1 + u ^ 2) + Real.log (1 + M ^ 2) + |Real.log (M ^ 2)| := by
  have hu2 : 0 < u ^ 2 := by positivity
  have h1 : 0 ≤ Real.log (1 + u ^ 2) := Real.log_nonneg (by nlinarith)
  have hM : 0 ≤ M := (abs_nonneg e).trans he
  have h2 : 0 ≤ Real.log (1 + M ^ 2) := Real.log_nonneg (by nlinarith)
  have he2 : e ^ 2 ≤ M ^ 2 := by
    have : |e| ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (abs_nonneg e) he 2
    rwa [sq_abs] at this
  by_cases hle : u ^ 2 + e ^ 2 < 1
  · have hlt0 : Real.log (u ^ 2 + e ^ 2) ≤ 0 := Real.log_nonpos (by positivity) hle.le
    have hge : Real.log (u ^ 2) ≤ Real.log (u ^ 2 + e ^ 2) := Real.log_le_log hu2 (by nlinarith)
    rw [abs_of_nonpos hlt0]
    have : |Real.log (u ^ 2)| = -Real.log (u ^ 2) := abs_of_nonpos (hge.trans hlt0)
    linarith [abs_nonneg (Real.log (M ^ 2))]
  · push Not at hle
    have hpos : 0 ≤ Real.log (u ^ 2 + e ^ 2) := Real.log_nonneg hle
    rw [abs_of_nonneg hpos]
    have hprod : u ^ 2 + e ^ 2 ≤ (1 + u ^ 2) * (1 + M ^ 2) := by nlinarith
    calc Real.log (u ^ 2 + e ^ 2) ≤ Real.log ((1 + u ^ 2) * (1 + M ^ 2)) :=
          Real.log_le_log (by linarith) hprod
      _ = Real.log (1 + u ^ 2) + Real.log (1 + M ^ 2) := Real.log_mul (by positivity) (by positivity)
      _ ≤ _ := by linarith [abs_nonneg (Real.log (u ^ 2)), abs_nonneg (Real.log (M ^ 2))]

end ParamLogPot

open ParamLogPot in
theorem solution
    {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (g : P × (ℝ × V) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (c₀ : P → ℝ) (hc₀ : ContDiff ℝ (⊤ : ℕ∞) c₀) (hc₀0 : ∀ p, c₀ p ≠ 0)
    (φ : P → (V →L[ℝ] ℝ)) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (θ : P × V → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hθ0 : ∀ q, 0 ≤ θ q) :
    ∃ A B : P × ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (p : P) (ρ : ℝ),
        Integrable (fun sv : ℝ × V =>
          g (p, sv) * (Real.log ((c₀ p * sv.1 + φ p sv.2) ^ 2 + (ρ * θ (p, sv.2)) ^ 2) : ℂ)) ((volume : Measure ℝ).prod μ) ∧
        ∫ sv : ℝ × V, g (p, sv) * (Real.log ((c₀ p * sv.1 + φ p sv.2) ^ 2 + (ρ * θ (p, sv.2)) ^ 2) : ℂ) ∂((volume : Measure ℝ).prod μ) =
          A (p, ρ) + ((|ρ| : ℝ) : ℂ) * B (p, ρ) := by
  classical

  set g₀ : (P × V) × ℝ → ℂ := g ∘ shear c₀ φ with hg₀
  have hg₀s : ContDiff ℝ (⊤ : ℕ∞) g₀ := hg.comp (contDiff_shear c₀ φ hc₀ hc₀0 hφ)
  have hg₀c : HasCompactSupport g₀ := hgc.comp_homeomorph (shearHomeomorph c₀ φ hc₀ hc₀0 hφ)
  have hg₀_apply : ∀ (p : P) (s : ℝ) (v : V), g₀ ((p, v), c₀ p * s + φ p v) = g (p, (s, v)) := by
    intro p s v
    show g (shear c₀ φ ((p, v), c₀ p * s + φ p v)) = g (p, (s, v))
    rw [shear_apply c₀ φ hc₀0]
  have hg₀_apply' : ∀ (p : P) (v : V) (u : ℝ), g₀ ((p, v), u) = g (p, ((u - φ p v) * (c₀ p)⁻¹, v)) := fun p v u => rfl

  obtain ⟨A₀, B₀, hA₀, hB₀, hD0⟩ :=
    MeasureTheory.exists_contDiff_integral_mul_log_sq_add_sq_eq_add_abs_mul_of_hasCompactSupport g₀ hg₀s hg₀c

  obtain ⟨SV, hSV⟩ : ∃ SV : Set V, SV = (fun x : P × (ℝ × V) => x.2.2) '' tsupport g := ⟨_, rfl⟩
  have hSVc : IsCompact SV := by rw [hSV]; exact hgc.image (continuous_snd.comp continuous_snd)
  have hgz : ∀ (p : P) (s : ℝ) (v : V), v ∉ SV → g (p, (s, v)) = 0 := by
    intro p s v hv
    exact image_eq_zero_of_notMem_tsupport fun h => hv (by rw [hSV]; exact ⟨_, h, rfl⟩)
  obtain ⟨χ, hχ, hχc, hχ1, -⟩ := exists_smooth_bump hSVc isOpen_univ (Set.subset_univ _)

  have hκs : ContDiff ℝ (⊤ : ℕ∞) fun p : P => |c₀ p|⁻¹ := by
    rw [contDiff_iff_contDiffAt]
    intro p
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => |x|) (c₀ p) := contDiffAt_abs (hc₀0 p)
    exact (h1.comp p hc₀.contDiffAt).inv (abs_ne_zero.mpr (hc₀0 p))
  obtain ⟨IA, hIA⟩ : ∃ IA : P × ℝ → ℂ,
      IA = fun q => ∫ v, (χ v : ℝ) • A₀ ((q.1, v), q.2 * θ (q.1, v)) ∂μ := ⟨_, rfl⟩
  obtain ⟨IB, hIB⟩ : ∃ IB : P × ℝ → ℂ,
      IB = fun q => ∫ v, (χ v : ℝ) • (((θ (q.1, v) : ℝ) : ℂ) * B₀ ((q.1, v), q.2 * θ (q.1, v))) ∂μ := ⟨_, rfl⟩
  have hθ' : ContDiff ℝ (⊤ : ℕ∞) fun z : (P × ℝ) × V => θ (z.1.1, z.2) :=
    hθ.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have hq : ContDiff ℝ (⊤ : ℕ∞) fun z : (P × ℝ) × V => ((z.1.1, z.2), z.1.2 * θ (z.1.1, z.2)) :=
    ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd).prodMk ((contDiff_snd.comp contDiff_fst).mul hθ')
  have hIAs : ContDiff ℝ (⊤ : ℕ∞) IA := by
    rw [hIA]
    exact contDiff_paramIntegral μ (fun z : (P × ℝ) × V => A₀ ((z.1.1, z.2), z.1.2 * θ (z.1.1, z.2)))
      (hA₀.comp hq) χ hχ hχc
  have hIBs : ContDiff ℝ (⊤ : ℕ∞) IB := by
    rw [hIB]
    exact contDiff_paramIntegral μ
      (fun z : (P × ℝ) × V => ((θ (z.1.1, z.2) : ℝ) : ℂ) * B₀ ((z.1.1, z.2), z.1.2 * θ (z.1.1, z.2)))
      ((Complex.ofRealCLM.contDiff.comp hθ').mul (hB₀.comp hq)) χ hχ hχc
  refine ⟨fun q => ((|c₀ q.1|⁻¹ : ℝ) : ℂ) * IA q, fun q => ((|c₀ q.1|⁻¹ : ℝ) : ℂ) * IB q, ?_, ?_, fun p ρ => ?_⟩
  · exact (Complex.ofRealCLM.contDiff.comp (hκs.comp contDiff_fst)).mul hIAs
  · exact (Complex.ofRealCLM.contDiff.comp (hκs.comp contDiff_fst)).mul hIBs

  set f : ℝ × V → ℂ := fun sv : ℝ × V =>
    g (p, sv) * (Real.log ((c₀ p * sv.1 + φ p sv.2) ^ 2 + (ρ * θ (p, sv.2)) ^ 2) : ℂ) with hf
  set h : V → ℝ → ℂ := fun v u => g₀ ((p, v), u) * (Real.log (u ^ 2 + (ρ * θ (p, v)) ^ 2) : ℂ) with hh
  have hfh : ∀ (v : V) (s : ℝ), f (s, v) = h v (c₀ p * s + φ p v) := by
    intro v s
    show g (p, (s, v)) * _ = g₀ ((p, v), c₀ p * s + φ p v) * _
    rw [hg₀_apply]

  obtain ⟨Cg, hCg⟩ := hg₀s.continuous.bounded_above_of_compact_support hg₀c
  have hCg0 : 0 ≤ Cg := (norm_nonneg _).trans (hCg 0)
  obtain ⟨R, hR⟩ := ((hg₀c.image continuous_snd).isBounded).subset_closedBall (0 : ℝ)
  have hsuppu : ∀ (v : V) (u : ℝ), g₀ ((p, v), u) ≠ 0 → u ∈ Set.Icc (-R) R := by
    intro v u hne
    have hmem : ((p, v), u) ∈ tsupport g₀ := by
      by_contra hc; exact hne (image_eq_zero_of_notMem_tsupport hc)
    have : u ∈ Metric.closedBall (0 : ℝ) R := hR ⟨_, hmem, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le] at this
    exact ⟨this.1, this.2⟩
  have hsuppv : ∀ (v : V) (u : ℝ), g₀ ((p, v), u) ≠ 0 → v ∈ SV := by
    intro v u hne
    by_contra hv
    exact hne (by rw [hg₀_apply']; exact hgz p _ v hv)
  obtain ⟨Θ, hΘ⟩ := hSVc.exists_bound_of_continuousOn
    ((hθ.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn (s := SV))
  set M : ℝ := |ρ| * Θ with hM
  have heM : ∀ v ∈ SV, |ρ * θ (p, v)| ≤ M := by
    intro v hv
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _).symm.le.trans (hΘ v hv)) (abs_nonneg ρ)
  set Bnd : ℝ → ℝ := fun s => |Real.log (s ^ 2)| + Real.log (1 + s ^ 2) + Real.log (1 + M ^ 2) + |Real.log (M ^ 2)|
    with hBnd
  have hBnd0 : ∀ s, 0 ≤ Bnd s := fun s => (abs_nonneg _).trans (abs_log_sq_add_sq_le s M)
  have hbnd' : IntegrableOn (fun s => Cg * Bnd s) (Set.Icc (-R) R) (volume : Measure ℝ) :=
    (integrableOn_logBound' R M).const_mul Cg
  have hbnd : Integrable ((Set.Icc (-R) R).indicator fun s => Cg * Bnd s) (volume : Measure ℝ) :=
    hbnd'.integrable_indicator measurableSet_Icc
  have hh_le : ∀ (v : V) (u : ℝ), u ≠ 0 → ‖h v u‖ ≤ (Set.Icc (-R) R).indicator (fun s => Cg * Bnd s) u := by
    intro v u hu
    by_cases hne : g₀ ((p, v), u) = 0
    · have : h v u = 0 := by show g₀ ((p, v), u) * _ = 0; rw [hne, zero_mul]
      rw [this, norm_zero]
      exact Set.indicator_nonneg (fun s _ => mul_nonneg hCg0 (hBnd0 s)) _
    · rw [Set.indicator_of_mem (hsuppu v u hne)]
      show ‖g₀ ((p, v), u) * (Real.log (u ^ 2 + (ρ * θ (p, v)) ^ 2) : ℂ)‖ ≤ Cg * Bnd u
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hCg _) (abs_log_sq_add_sq_le_of_abs_le u _ M hu (heM v (hsuppv v u hne)))
        (abs_nonneg _) hCg0
  have hh_ae : ∀ v : V, ∀ᵐ u ∂(volume : Measure ℝ), ‖h v u‖ ≤ (Set.Icc (-R) R).indicator (fun s => Cg * Bnd s) u := by
    intro v
    have h0 : ({0} : Set ℝ)ᶜ ∈ ae (volume : Measure ℝ) := compl_mem_ae_iff.mpr (measure_singleton 0)
    filter_upwards [h0] with u hu
    exact hh_le v u (by simpa using hu)
  have hh_meas : ∀ v : V, AEStronglyMeasurable (h v) (volume : Measure ℝ) := by
    intro v
    refine (((hg₀s.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mul ?_)
    exact (Complex.continuous_ofReal.measurable.comp
      (Real.measurable_log.comp (by fun_prop : Measurable fun u : ℝ => u ^ 2 + (ρ * θ (p, v)) ^ 2))).aestronglyMeasurable
  have hh_int : ∀ v : V, Integrable (h v) (volume : Measure ℝ) := fun v =>
    hbnd.mono' (hh_meas v) (hh_ae v)

  have hf_slice : ∀ v : V, Integrable (fun s : ℝ => f (s, v)) (volume : Measure ℝ) := by
    intro v
    have h1 := ((hh_int v).comp_add_right (φ p v)).comp_mul_left' (hc₀0 p)
    refine h1.congr (Filter.Eventually.of_forall fun s => ?_)
    exact (hfh v s).symm
  have hinner : ∀ v : V, ∫ s, f (s, v) = ((|c₀ p|⁻¹ : ℝ) : ℂ) *
      (A₀ ((p, v), ρ * θ (p, v)) + ((|ρ| * θ (p, v) : ℝ) : ℂ) * B₀ ((p, v), ρ * θ (p, v))) := by
    intro v
    calc ∫ s, f (s, v) = ∫ s, (fun x : ℝ => h v (x + φ p v)) (c₀ p * s) := by
          congr 1; funext s; exact hfh v s
      _ = |(c₀ p)⁻¹| • ∫ x, h v (x + φ p v) :=
          Measure.integral_comp_mul_left (fun x : ℝ => h v (x + φ p v)) (c₀ p)
      _ = |(c₀ p)⁻¹| • ∫ u, h v u := by rw [integral_add_right_eq_self (h v) (φ p v)]
      _ = ((|c₀ p|⁻¹ : ℝ) : ℂ) *
          (A₀ ((p, v), ρ * θ (p, v)) + ((|ρ| * θ (p, v) : ℝ) : ℂ) * B₀ ((p, v), ρ * θ (p, v))) := by
          rw [abs_inv, Complex.real_smul]
          congr 1
          have e := hD0 (p, v) (ρ * θ (p, v))
          rw [abs_mul, abs_of_nonneg (hθ0 (p, v))] at e
          exact e
  have hinner_norm : ∀ v : V, ∫ s, ‖f (s, v)‖ = |(c₀ p)⁻¹| * ∫ u, ‖h v u‖ := by
    intro v
    calc ∫ s, ‖f (s, v)‖ = ∫ s, (fun x : ℝ => ‖h v (x + φ p v)‖) (c₀ p * s) := by
          congr 1; funext s; rw [hfh v s]
      _ = |(c₀ p)⁻¹| • ∫ x, ‖h v (x + φ p v)‖ :=
          Measure.integral_comp_mul_left (fun x : ℝ => ‖h v (x + φ p v)‖) (c₀ p)
      _ = |(c₀ p)⁻¹| * ∫ u, ‖h v u‖ := by
          rw [smul_eq_mul]
          congr 1
          exact integral_add_right_eq_self (fun u => ‖h v u‖) (φ p v)

  set M' : ℝ := |(c₀ p)⁻¹| * ∫ s, (Set.Icc (-R) R).indicator (fun s => Cg * Bnd s) s with hM'
  have hprof : ∀ v : V, ∫ s, ‖f (s, v)‖ ≤ SV.indicator (fun _ => M') v := by
    intro v
    by_cases hv : v ∈ SV
    · rw [Set.indicator_of_mem hv, hinner_norm v]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbnd (hh_ae v)
    · rw [Set.indicator_of_notMem hv]
      have : ∀ s : ℝ, f (s, v) = 0 := by
        intro s; show g (p, (s, v)) * _ = 0; rw [hgz p s v hv, zero_mul]
      simp [this]

  have hfm : Measurable f := by
    refine Measurable.mul ?_ ?_
    · exact (hg.continuous.comp (continuous_const.prodMk continuous_id)).measurable
    · have hc : Continuous fun sv : ℝ × V => (c₀ p * sv.1 + φ p sv.2) ^ 2 + (ρ * θ (p, sv.2)) ^ 2 :=
        (((continuous_const.mul continuous_fst).add ((φ p).continuous.comp continuous_snd)).pow 2).add
          ((continuous_const.mul (hθ.continuous.comp (continuous_const.prodMk continuous_snd))).pow 2)
      exact Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp hc.measurable)
  have hInt : Integrable f ((volume : Measure ℝ).prod μ) := by
    rw [integrable_prod_iff' hfm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall hf_slice, ?_⟩
    have hconst : Integrable (SV.indicator fun _ => M') μ :=
      (integrableOn_const (hs := hSVc.measure_lt_top.ne)).integrable_indicator hSVc.isClosed.measurableSet
    refine hconst.mono' ?_ (Filter.Eventually.of_forall fun v => ?_)
    · exact (hfm.stronglyMeasurable.norm.integral_prod_left (μ := (volume : Measure ℝ))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact hprof v
  refine ⟨hInt, ?_⟩

  show ∫ z, f z ∂((volume : Measure ℝ).prod μ) =
    ((|c₀ p|⁻¹ : ℝ) : ℂ) * IA (p, ρ) + ((|ρ| : ℝ) : ℂ) * (((|c₀ p|⁻¹ : ℝ) : ℂ) * IB (p, ρ))
  rw [integral_prod_symm f hInt]
  have hθc : Continuous fun v : V => θ (p, v) := hθ.continuous.comp (continuous_const.prodMk continuous_id)
  have hpt_cont : Continuous fun v : V => ((p, v), ρ * θ (p, v)) :=
    (continuous_const.prodMk continuous_id).prodMk (continuous_const.mul hθc)
  have hiA : Integrable (fun v => (χ v : ℝ) • A₀ ((p, v), ρ * θ (p, v))) μ :=
    (hχ.continuous.smul (hA₀.continuous.comp hpt_cont)).integrable_of_hasCompactSupport hχc.smul_right
  have hiB : Integrable (fun v => (χ v : ℝ) • ((((θ (p, v)) : ℝ) : ℂ) * B₀ ((p, v), ρ * θ (p, v)))) μ :=
    (hχ.continuous.smul ((Complex.continuous_ofReal.comp hθc).mul (hB₀.continuous.comp hpt_cont))).integrable_of_hasCompactSupport
      hχc.smul_right
  have hG1 : ∫ v, ∫ s, f (s, v) ∂volume ∂μ = ∫ v, (χ v : ℝ) • ∫ s, f (s, v) ∂volume ∂μ := by
    congr 1; funext v
    by_cases hv : v ∈ SV
    · rw [hχ1 v hv, one_smul]
    · have : ∀ s : ℝ, f (s, v) = 0 := by
        intro s; show g (p, (s, v)) * _ = 0; rw [hgz p s v hv, zero_mul]
      simp [this]
  rw [hG1]
  simp_rw [hinner]
  have hpt : ∀ v : V, (χ v : ℝ) • (((|c₀ p|⁻¹ : ℝ) : ℂ) *
      (A₀ ((p, v), ρ * θ (p, v)) + ((|ρ| * θ (p, v) : ℝ) : ℂ) * B₀ ((p, v), ρ * θ (p, v)))) =
      ((|c₀ p|⁻¹ : ℝ) : ℂ) * ((χ v : ℝ) • A₀ ((p, v), ρ * θ (p, v))) +
        (((|ρ| : ℝ) : ℂ) * ((|c₀ p|⁻¹ : ℝ) : ℂ)) *
          ((χ v : ℝ) • ((((θ (p, v)) : ℝ) : ℂ) * B₀ ((p, v), ρ * θ (p, v)))) := by
    intro v; simp only [Complex.real_smul, Complex.ofReal_mul]; ring
  simp_rw [hpt]
  rw [integral_add (hiA.const_mul _) (hiB.const_mul _), integral_const_mul, integral_const_mul, hIA, hIB]
  ring

end S_MeasureTheory_exists_contDiff_integral_integral_mul_log_sq_linear_add_sq_mul_sq_eq_add_abs_mul_of_hasCompactSupport
end P2MW
export P2MW.S_MeasureTheory_exists_contDiff_integral_integral_mul_log_sq_linear_add_sq_mul_sq_eq_add_abs_mul_of_hasCompactSupport (solution)
