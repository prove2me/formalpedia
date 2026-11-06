-- Prove2me | solution 1 for GoldieRenewal.Kesten.corollary_2_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T04:08:16.962448+00:00
-- url     : https://prove2.me/submissions/6a5a7cdb-4a74-48d3-b4d8-8854598a3ef7

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Implicit_TailConstants
import Theorems.Thm_GoldieRenewal_Implicit_theorem_2_3
import Theorems.Thm_GoldieRenewal_Kesten_lemma_9_4

open MeasureTheory ProbabilityTheory Filter Topology

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (Ψ : ℝ → Ω → ℝ) (hΨ : Measurable (fun p : ℝ × Ω => Ψ p.1 p.2))
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R)
    (hCramer : GoldieRenewal.Implicit.CramerConditions κ (P.map M))
    (hindep : IndepFun R (fun ω => (M ω, fun t => Ψ t ω)) P)
    (hfix : P.map (fun ω => Ψ (R ω) ω) = P.map R) :
    (P {ω | M ω < 0} = 0 →
      (Integrable (fun ω => (max (Ψ (R ω) ω) 0) ^ κ - (max (M ω * R ω) 0) ^ κ) P →
        Tendsto (fun t : ℝ => t ^ κ * P.real {ω | t < R ω}) atTop
          (𝓝 ((κ * GoldieRenewal.Implicit.cramerMean κ (P.map M))⁻¹ *
            ∫ ω, ((max (Ψ (R ω) ω) 0) ^ κ - (max (M ω * R ω) 0) ^ κ) ∂P))) ∧
      (Integrable (fun ω => (max (-Ψ (R ω) ω) 0) ^ κ - (max (-(M ω * R ω)) 0) ^ κ) P →
        Tendsto (fun t : ℝ => t ^ κ * P.real {ω | R ω < -t}) atTop
          (𝓝 ((κ * GoldieRenewal.Implicit.cramerMean κ (P.map M))⁻¹ *
            ∫ ω, ((max (-Ψ (R ω) ω) 0) ^ κ - (max (-(M ω * R ω)) 0) ^ κ) ∂P)))) ∧
    (0 < P {ω | M ω < 0} →
      Integrable (fun ω => (max (Ψ (R ω) ω) 0) ^ κ - (max (M ω * R ω) 0) ^ κ) P →
      Integrable (fun ω => (max (-Ψ (R ω) ω) 0) ^ κ - (max (-(M ω * R ω)) 0) ^ κ) P →
        Tendsto (fun t : ℝ => t ^ κ * P.real {ω | t < R ω}) atTop
          (𝓝 ((2 * κ * GoldieRenewal.Implicit.cramerMean κ (P.map M))⁻¹ *
            ∫ ω, (|Ψ (R ω) ω| ^ κ - |M ω * R ω| ^ κ) ∂P)) ∧
        Tendsto (fun t : ℝ => t ^ κ * P.real {ω | R ω < -t}) atTop
          (𝓝 ((2 * κ * GoldieRenewal.Implicit.cramerMean κ (P.map M))⁻¹ *
            ∫ ω, (|Ψ (R ω) ω| ^ κ - |M ω * R ω| ^ κ) ∂P))) := by
  classical
  set X : Ω → ℝ := fun ω => Ψ (R ω) ω with hXdef
  have hX : Measurable X := hΨ.comp (hR.prodMk measurable_id)
  have hMR : Measurable (fun ω => M ω * R ω) := hM.mul hR
  have hκ : 0 < κ := hCramer.pos
  -- equality in law of `X = Ψ(R)` and `R`
  have hlaw : ∀ s : Set ℝ, MeasurableSet s → P.real (R ⁻¹' s) = P.real (X ⁻¹' s) := by
    intro s hs
    have h1 : (P.map X) s = (P.map R) s := by rw [hfix]
    rw [Measure.map_apply hX hs, Measure.map_apply hR hs] at h1
    simp only [measureReal_def, h1]
  have hgt : ∀ t : ℝ, P.real {ω | t < R ω} = P.real {ω | t < X ω} := fun t =>
    hlaw (Set.Ioi t) measurableSet_Ioi
  have hlt : ∀ t : ℝ, P.real {ω | R ω < -t} = P.real {ω | t < -X ω} := by
    intro t
    have := hlaw (Set.Iio (-t)) measurableSet_Iio
    have e : {ω | t < -X ω} = X ⁻¹' Set.Iio (-t) := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iio]; constructor <;>
        intro h <;> linarith
    rw [e]; exact this
  have habs : ∀ t : ℝ, P.real {ω | t < |R ω|} = P.real {ω | t < |X ω|} := fun t =>
    hlaw {x | t < |x|} (measurableSet_lt measurable_const continuous_abs.measurable)
  have hMRlt : ∀ t : ℝ, {ω | M ω * R ω < -t} = {ω | t < -(M ω * R ω)} := by
    intro t; ext ω; simp only [Set.mem_setOf_eq]; constructor <;> intro h <;> linarith
  -- independence of `R` and `M`
  have hindRM : IndepFun R M P := by
    have := hindep.comp measurable_id (measurable_fst : Measurable (fun p : ℝ × (ℝ → ℝ) => p.1))
    exact this
  have T := GoldieRenewal.Implicit.theorem_2_3 P M R hM hR κ hCramer hindRM
  -- Lemma 9.4 instances
  have L1 := GoldieRenewal.Kesten.lemma_9_4 P κ hκ X (fun ω => M ω * R ω) hX hMR
  have L2 := GoldieRenewal.Kesten.lemma_9_4 P κ hκ (fun ω => -X ω) (fun ω => -(M ω * R ω))
    hX.neg hMR.neg
  have L3 := GoldieRenewal.Kesten.lemma_9_4 P κ hκ (fun ω => |X ω|) (fun ω => |M ω * R ω|)
    hX.abs hMR.abs
  have eplus : GoldieRenewal.Implicit.tailDiffPlus P M R κ =
      fun t => (P.real {ω | t < X ω} - P.real {ω | t < M ω * R ω}) * t ^ (κ - 1) := by
    funext t; simp only [GoldieRenewal.Implicit.tailDiffPlus, hgt]
  have eminus : GoldieRenewal.Implicit.tailDiffMinus P M R κ =
      fun t => (P.real {ω | t < -X ω} - P.real {ω | t < -(M ω * R ω)}) * t ^ (κ - 1) := by
    funext t; simp only [GoldieRenewal.Implicit.tailDiffMinus, hlt, hMRlt]
  have eabs : GoldieRenewal.Implicit.tailDiffAbs P M R κ =
      fun t => (P.real {ω | t < |X ω|} - P.real {ω | t < |M ω * R ω|}) * t ^ (κ - 1) := by
    funext t; simp only [GoldieRenewal.Implicit.tailDiffAbs, habs]
  -- pointwise identity |a|^κ = (a⁺)^κ + (a⁻)^κ
  have hsplit : ∀ a : ℝ, |a| ^ κ = (max a 0) ^ κ + (max (-a) 0) ^ κ := by
    intro a
    rcases le_total 0 a with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith : -a ≤ 0),
        Real.zero_rpow hκ.ne']; ring
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith : 0 ≤ -a),
        Real.zero_rpow hκ.ne']; ring
  have hmaxabs : ∀ a : ℝ, max |a| 0 = |a| := fun a => max_eq_left (abs_nonneg a)
  refine ⟨?_, ?_⟩
  · intro hneg
    have hae : ∀ᵐ ω ∂P, 0 ≤ M ω := by
      rw [ae_iff]; simpa only [not_le] using hneg
    obtain ⟨Tp, Tm⟩ := T.1 hae
    refine ⟨?_, ?_⟩
    · intro hint
      obtain ⟨hI, hEq⟩ := L1.2 hint
      have hc : GoldieRenewal.Implicit.TailCondPlus P M R κ := by
        unfold GoldieRenewal.Implicit.TailCondPlus; rw [eplus]; exact hI
      have := Tp hc
      convert this using 2
      unfold GoldieRenewal.Implicit.Cplus
      rw [eplus, hEq, mul_inv]; ring
    · intro hint
      obtain ⟨hI, hEq⟩ := L2.2 hint
      have hc : GoldieRenewal.Implicit.TailCondMinus P M R κ := by
        unfold GoldieRenewal.Implicit.TailCondMinus; rw [eminus]; exact hI
      have := Tm hc
      convert this using 2
      unfold GoldieRenewal.Implicit.Cminus
      rw [eminus, hEq, mul_inv]; ring
  · intro hneg hint1 hint2
    obtain ⟨hI1, -⟩ := L1.2 hint1
    obtain ⟨hI2, -⟩ := L2.2 hint2
    have hc1 : GoldieRenewal.Implicit.TailCondPlus P M R κ := by
      unfold GoldieRenewal.Implicit.TailCondPlus; rw [eplus]; exact hI1
    have hc2 : GoldieRenewal.Implicit.TailCondMinus P M R κ := by
      unfold GoldieRenewal.Implicit.TailCondMinus; rw [eminus]; exact hI2
    have hint3 : Integrable (fun ω => (max |X ω| 0) ^ κ - (max |M ω * R ω| 0) ^ κ) P := by
      have := hint1.add hint2
      refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp only [hmaxabs, Pi.add_apply, hXdef]
      rw [hsplit (Ψ (R ω) ω), hsplit (M ω * R ω)]
      ring
    obtain ⟨-, hEq3⟩ := L3.2 hint3
    have hC : GoldieRenewal.Implicit.Ctwo P M R κ =
        (2 * κ * GoldieRenewal.Implicit.cramerMean κ (P.map M))⁻¹ *
          ∫ ω, (|Ψ (R ω) ω| ^ κ - |M ω * R ω| ^ κ) ∂P := by
      unfold GoldieRenewal.Implicit.Ctwo
      rw [eabs, hEq3]
      simp only [hmaxabs]
      rw [mul_inv, mul_inv, mul_inv]; ring
    obtain ⟨A, B⟩ := T.2 hneg hc1 hc2
    rw [hC] at A B
    exact ⟨A, B⟩
