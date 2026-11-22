-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result8_2_v2_bridge_slice_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:04:26.397803+00:00
-- url     : https://prove2.me/submissions/af7ea876-f8d0-4764-8490-28c03c7a1ffa

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_bridge_upper_drawdown
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_2_v2_bridge_upper_integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
private lemma tauPlus_shift {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (x d : ℝ) (ω : Ω) :
    tauPlus (shifted X x) (x + d) ω = tauPlus X d ω := by
  unfold tauPlus shifted ; congr 1
  ext t ; constructor <;> rintro ⟨u, hu0, hut, hlt⟩ <;> exact ⟨u, hu0, hut, by simpa using hlt⟩
private lemma tauMinus_shift {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (x : ℝ) (ω : Ω) :
    tauMinus (shifted X x) 0 ω = tauMinus X (-x) ω := by
  unfold tauMinus shifted ; congr 1
  ext t ; constructor <;> rintro ⟨u, hu0, hut, hlt⟩ <;> exact ⟨u, hu0, hut, by linarith⟩
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : SpectrallyNegativeModel Ω P) (ψ : ℝ → ℝ)
    (hψ : IsLaplaceExponent (SpectrallyNegativeModel.toData P D) ψ)
    (q : ℝ) (hq : 0 ≤ q) (n : Measure ℝ) (hLaw : HasActualQExcursionHeightLaw P D ψ q n) :
    ∀ l d : ℝ, 0 < l → 0 < d →
      upBeforeDownExpectation P D.X q l (l + d) ≤
        Real.exp (-(d * (Phi ψ q + (n (Set.Ici (l + d + d))).toReal))) := by
  intro l d hl hd
  have hpos : 0 < l + d + d := by linarith
  have hLawInst := (hLaw.2 d (l + d + d) hd hpos).2
  have hIncl : {ω | tauPlus D.X d ω < tauMinus D.X (-l) ω} ⊆
      {ω | NoDrawdownBeforeUpcrossing D.X d (l + d + d) ω} := by
    intro ω hU t ht
    exact lt_of_le_of_lt (source_result8_2_v2_bridge_upper_drawdown P D l d hl hd t ω ht hU) (by linarith)
  have hNpos : 0 < Real.exp (Phi ψ q * d) := Real.exp_pos _
  rw [MeasureTheory.integral_const_mul] at hLawInst
  have hN : (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X d (l + d + d) ω}, discountedAt q (tauPlus D.X d ω) ∂P) = Real.exp (-(d * (Phi ψ q + (n (Set.Ici (l + d + d))).toReal))) := by
    have hDiv : (∫ ω in {ω | NoDrawdownBeforeUpcrossing D.X d (l + d + d) ω}, discountedAt q (tauPlus D.X d ω) ∂P) = Real.exp (-d * (n (Set.Ici (l + d + d))).toReal) / Real.exp (Phi ψ q * d) := by
      rw [eq_div_iff (ne_of_gt hNpos), mul_comm]
      exact hLawInst
    rw [hDiv, ← Real.exp_sub] ; congr 1 ; ring
  rw [← hN]
  unfold upBeforeDownExpectation
  simp only [tauPlus_shift, tauMinus_shift]
  exact source_result8_2_v2_bridge_upper_integral P D q hq l d hl hd hIncl
