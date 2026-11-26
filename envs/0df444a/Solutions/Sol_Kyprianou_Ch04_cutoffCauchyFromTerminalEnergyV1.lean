-- Prove2me | solution 1 for Kyprianou.Ch04.cutoffCauchyFromTerminalEnergyV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:26:17.474554+00:00
-- url     : https://prove2.me/submissions/6ea0c924-6e91-4fc9-b872-3d93c5b62df9

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_Kyprianou_Ch04_smallJumpContinuousQuadraticTailV1
import Theorems.Thm_Kyprianou_Ch04_rightContinuousMartingaleL2MaximalV1
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Quantitative terminal energy and individual regularity imply the cutoff Cauchy conclusion. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (ν : Measure ℝ) (hν : IsLevyMeasure ν)
    (M : ℝ → NNReal → Ω → ℝ) (T : NNReal) (hT : 0 < T)
    (C : ℝ) (hM : ∀ e, 0 < e → e < 1 → Martingale (M e) F P)
    (hR : ∀ e, 0 < e → e < 1 → ∀ᵐ ω ∂P, ∀ t : NNReal,
      Tendsto (fun s => M e s ω) (𝓝[>] t) (𝓝 (M e t ω)))
    (hL2 : ∀ e, 0 < e → e < 1 → MemLp (M e T) 2 P)
    (hEnergy : ∀ a b : ℝ, 0 < a → a ≤ b → b < 1 →
      (∫ ω, (M a T ω - M b T ω)^2 ∂P) ≤ C *
        (∫⁻ z in {z : ℝ | |z| ≤ b}, ENNReal.ofReal (z^2) ∂ν).toReal) :
    (∀ e : ℝ, 0 < e → e < 1 →
      Integrable (fun ω => sSup ((fun t : NNReal => |M e t ω|^2) '' Iic T)) P) ∧
    ∀ δ : ℝ, 0 < δ → ∃ e0 : ℝ, 0 < e0 ∧ e0 < 1 ∧
      ∀ a b : ℝ, 0 < a → a < e0 → 0 < b → b < e0 →
        Integrable (fun ω => sSup ((fun t : NNReal => |M a t ω - M b t ω|^2) '' Iic T)) P ∧
        (∫ ω, sSup ((fun t : NNReal => |M a t ω - M b t ω|^2) '' Iic T) ∂P) < δ := by
  constructor
  · intro e he he1
    exact (Kyprianou.Ch04.rightContinuousMartingaleL2MaximalV1 P F
      (M e) (hM e he he1) T hT (hR e he he1) (hL2 e he he1).integrable_sq).1
  intro δ hδ
  let q : ℝ → ℝ := fun r =>
    (∫⁻ z in {z : ℝ | |z| ≤ r}, ENNReal.ofReal (z^2) ∂ν).toReal
  have hq : Tendsto q (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [q, Function.comp_def] using (ENNReal.tendsto_toReal (a := 0) (by simp)).comp
      (Kyprianou.Ch04.smallJumpContinuousQuadraticTailV1 ν hν)
  have hlim : Tendsto (fun r => 4 * C * q r) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := 4 * C)).mul hq
  obtain ⟨r, hr, hsmall⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hlim) δ hδ
  let e0 := min r 1 / 2
  have he0 : 0 < e0 := by dsimp [e0]; positivity
  have he01 : e0 < 1 := by dsimp [e0]; linarith [min_le_right r (1 : ℝ)]
  have he0r : e0 < r := by dsimp [e0]; linarith [min_le_left r (1 : ℝ)]
  refine ⟨e0, he0, he01, ?_⟩
  intro a b ha ha0 hb hb0
  have ha1 := ha0.trans he01
  have hb1 := hb0.trans he01
  let D : NNReal → Ω → ℝ := M a - M b
  have hd : Martingale D F P := (hM a ha ha1).sub (hM b hb hb1)
  have hdr : ∀ᵐ ω ∂P, ∀ t : NNReal, Tendsto (fun s => D s ω) (𝓝[>] t) (𝓝 (D t ω)) := by
    filter_upwards [hR a ha ha1, hR b hb hb1] with ω h₁ h₂
    intro t
    exact (h₁ t).sub (h₂ t)
  have hdsq : Integrable (fun ω => (D T ω)^2) P :=
    ((hL2 a ha ha1).sub (hL2 b hb hb1)).integrable_sq
  have hmax := Kyprianou.Ch04.rightContinuousMartingaleL2MaximalV1 P F D hd T hT hdr hdsq
  have hbudget : (∫ ω, (D T ω)^2 ∂P) ≤ C * q (max a b) := by
    rcases le_total a b with hab | hba
    · simpa [D, q, max_eq_right hab] using hEnergy a b ha hab hb1
    · have heq : (∫ ω, (D T ω)^2 ∂P) =
          ∫ ω, (M b T ω - M a T ω)^2 ∂P := by
        apply integral_congr_ae
        filter_upwards with ω
        change (M a T ω - M b T ω)^2 = (M b T ω - M a T ω)^2
        ring
      rw [heq, max_eq_left hba]
      exact hEnergy b a hb hba ha1
  have hmpos : 0 < max a b := ha.trans_le (le_max_left _ _)
  have hm : max a b < r := max_lt (ha0.trans he0r) (hb0.trans he0r)
  have hsmall' := hsmall (x := max a b) hmpos (by simpa [Real.dist_eq, abs_of_pos hmpos] using hm)
  rw [Real.dist_eq, sub_zero] at hsmall'
  refine ⟨hmax.1, hmax.2.trans_lt ?_⟩
  calc
    4 * (∫ ω, (D T ω)^2 ∂P) ≤ 4 * (C * q (max a b)) :=
      mul_le_mul_of_nonneg_left hbudget (by norm_num)
    _ = 4 * C * q (max a b) := by ring
    _ ≤ |4 * C * q (max a b)| := le_abs_self _
    _ < δ := hsmall'
