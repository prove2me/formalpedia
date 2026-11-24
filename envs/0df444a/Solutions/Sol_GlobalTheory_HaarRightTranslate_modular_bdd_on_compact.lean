-- Prove2me | solution 1 for GlobalTheory.HaarRightTranslate.modular_bdd_on_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:11:18.291847+00:00
-- url     : https://prove2.me/submissions/1b82f118-c852-45a8-9ed6-8e5a42148321

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarLintegralMulRightLe
import Theorems.Thm_GlobalTheory_HaarRightTranslate_map_mul_right_eq_modular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped ENNReal NNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.HaarRightTranslate
variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
namespace GlobalTheory.HaarRightTranslate
theorem _root_.solution {V : Set H} (hV : IsCompact V) :
    ∃ M : ℝ≥0, ∀ v ∈ V, modularCharacterFun v ≤ M := by
  set μ : Measure H := haar
  have K : PositiveCompacts H := Classical.arbitrary _
  set A : Set H := closure (K : Set H) with hA
  have hAc : IsCompact A := K.isCompact.closure
  have hAm : MeasurableSet A := isClosed_closure.measurableSet
  have hpos : μ A ≠ 0 :=
    (measure_pos_of_nonempty_interior _
      (K.interior_nonempty.mono (interior_mono subset_closure))).ne'
  have hfin : μ A ≠ ∞ := hAc.measure_lt_top.ne
  have hB : IsCompact (A * V⁻¹) := hAc.mul hV.inv
  have hBfin : μ (A * V⁻¹) ≠ ∞ := hB.measure_lt_top.ne
  refine ⟨(μ (A * V⁻¹) / μ A).toNNReal, fun v hv => ?_⟩
  have h1 : (modularCharacterFun v : ℝ≥0∞) * μ A ≤ μ (A * V⁻¹) := by
    have h := congrArg (fun ρ : Measure H => ρ A) (map_mul_right_eq_modular μ v)
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    rw [← h, map_apply (measurable_mul_const _) hAm]
    refine measure_mono fun x hx => ?_
    exact ⟨x * v, hx, v⁻¹, by simpa using hv, by simp⟩
  have h2 : (modularCharacterFun v : ℝ≥0∞) ≤ μ (A * V⁻¹) / μ A :=
    (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hfin)).2 h1
  have hne : μ (A * V⁻¹) / μ A ≠ ∞ := ENNReal.div_ne_top hBfin hpos
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hne]
  exact h2
end GlobalTheory.HaarRightTranslate
