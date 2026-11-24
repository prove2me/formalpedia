-- Prove2me | solution 1 for GlobalTheory.LineCos.exists_map_cosSq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:30:47.64886+00:00
-- url     : https://prove2.me/submissions/85fe5538-c805-436a-aeb5-a5dbd833c1a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CosineSquarePushforwardUniformStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalDensityBoundNearPoint
import Theorems.Thm_GlobalTheory_LineCos_exists_lintegral_le_iterated
import Theorems.Thm_GlobalTheory_LineCos_fsDensity_pos
import Theorems.Thm_GlobalTheory_LineCos_continuousOn_fsDensity
import Theorems.Thm_GlobalTheory_LineCos_lintegral_fsDensity_indicator
import Theorems.Thm_GlobalTheory_LineCos_continuousOn_cosSq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LineCos
namespace GlobalTheory.LineCos
theorem _root_.solution (d : ℕ) (T : Set (V (d + 1))) (ρ : V (d + 1) → ℝ)
    (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (s : Bool) (z₀ : V (d + 1))
    (hT : IsOpen T) (hz₀ : z₀ ∈ T) (hρ : ContinuousOn ρ T) (hG : ContinuousOn (fun z => G (base z)) T)
    (hp : ∀ z ∈ T, (G (base z)).PosDef) :
    ∃ N : Set (V (d + 1)), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ T ∧ ∃ C : ENNReal, C ≠ ⊤ ∧
      Measure.map (fun z => cosSq s (G (base z)) (fib z))
          ((volume.restrict N).withDensity fun z => ENNReal.ofReal (ρ z)) ≤
        C • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  classical
  obtain ⟨c, hc, hF⟩ := exists_lintegral_le_iterated d
  have hfs := continuousOn_fsDensity s hG hp
  have h0 := fsDensity_pos s (hp z₀ hz₀) (fib z₀)
  set R : ℝ := (|ρ z₀| + 1) / fsDensity s (G (base z₀)) (fib z₀) with hR
  have hR0 : 0 ≤ R := by positivity
  have hb : Continuous (fun z : V (d + 1) => base z) := by
    unfold base
    fun_prop
  let K : Set (Fin d → ℂ) := Metric.ball (base z₀) 1
  let N : Set (V (d + 1)) := (T ∩ (fun z => R * fsDensity s (G (base z)) (fib z) - ρ z) ⁻¹' Ioi 0) ∩
    (fun z => base z) ⁻¹' K
  have hN : IsOpen N :=
    (((continuousOn_const.mul hfs).sub hρ).isOpen_inter_preimage hT isOpen_Ioi).inter
      (Metric.isOpen_ball.preimage hb)
  have hNT : N ⊆ T := fun z hz => hz.1.1
  refine ⟨N, hN, ⟨⟨hz₀, ?_⟩, Metric.mem_ball_self one_pos⟩, hNT, c * (ENNReal.ofReal R * volume K),
    ENNReal.mul_ne_top hc (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne), ?_⟩
  · show 0 < R * fsDensity s (G (base z₀)) (fib z₀) - ρ z₀
    rw [hR, div_mul_cancel₀ _ h0.ne']
    linarith [le_abs_self (ρ z₀)]
  set f : V (d + 1) → ℝ := fun z => cosSq s (G (base z)) (fib z) with hf
  have hf' : Measurable (N.piecewise f 0) :=
    ((continuousOn_cosSq s hG hp).mono hNT).measurable_piecewise continuousOn_const hN.measurableSet
  have hae : f =ᵐ[(volume.restrict N).withDensity fun z => ENNReal.ofReal (ρ z)] N.piecewise f 0 := by
    refine (withDensity_absolutelyContinuous _ _).ae_le ?_
    filter_upwards [ae_restrict_mem hN.measurableSet] with z hz
    rw [Set.piecewise_eq_of_mem _ _ _ hz]
  rw [Measure.map_congr hae, Measure.le_iff]
  intro A hA
  rw [Measure.map_apply hf' hA, withDensity_apply _ (hf' hA), Measure.restrict_restrict (hf' hA),
    ← lintegral_indicator ((hf' hA).inter hN.measurableSet), Measure.smul_apply, smul_eq_mul]
  refine (hF _).trans ?_
  rw [mul_assoc c]
  refine mul_le_mul_right ?_ _
  have key : ∀ b : Fin d → ℂ, ∫⁻ x : ℂ, (N.piecewise f 0 ⁻¹' A ∩ N).indicator (fun z => ENNReal.ofReal (ρ z))
      ((splitLin d).symm (b, x)) ≤
      K.indicator (fun _ => ENNReal.ofReal R * volume.restrict (Icc (0 : ℝ) 1) A) b := by
    intro b
    have hbase : ∀ x, base ((splitLin d).symm (b, x)) = b := fun x =>
      congrArg Prod.fst ((splitLin d).apply_symm_apply (b, x))
    have hfib : ∀ x, fib ((splitLin d).symm (b, x)) = x := fun x =>
      congrArg Prod.snd ((splitLin d).apply_symm_apply (b, x))
    by_cases hex : ∃ x, (splitLin d).symm (b, x) ∈ N
    · obtain ⟨x₀, hx₀⟩ := hex
      have hbK : b ∈ K := by
        have := hx₀.2
        rwa [mem_preimage, hbase] at this
      have hGb : (G b).PosDef := by
        have := hp _ (hNT hx₀)
        rwa [hbase] at this
      rw [indicator_of_mem hbK, ← lintegral_fsDensity_indicator s hGb hA,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun x => ?_
      by_cases hx : (splitLin d).symm (b, x) ∈ N.piecewise f 0 ⁻¹' A ∩ N
      · have h1 : x ∈ cosSq s (G b) ⁻¹' A := by
          have := hx.1
          rw [mem_preimage, Set.piecewise_eq_of_mem _ _ _ hx.2, hf] at this
          simpa only [hbase, hfib, mem_preimage] using this
        have h2 : 0 < R * fsDensity s (G b) x - ρ ((splitLin d).symm (b, x)) := by
          have := hx.2.1.2
          simpa only [mem_preimage, hbase, hfib, mem_Ioi] using this
        simp only [indicator_of_mem hx, indicator_of_mem h1]
        rw [← ENNReal.ofReal_mul hR0]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      · simp only [indicator_of_notMem hx]
        exact zero_le
    · have : ∀ x : ℂ, (N.piecewise f 0 ⁻¹' A ∩ N).indicator (fun z => ENNReal.ofReal (ρ z))
          ((splitLin d).symm (b, x)) = 0 := fun x => indicator_of_notMem (fun h => hex ⟨x, h.2⟩) _
      simp only [this, lintegral_zero]
      exact zero_le
  refine (lintegral_mono key).trans (le_of_eq ?_)
  rw [lintegral_indicator Metric.isOpen_ball.measurableSet, setLIntegral_const]
  ring
end GlobalTheory.LineCos
