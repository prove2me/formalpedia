-- Prove2me | solution 1 for GlobalTheory.QuadFibre.exists_map_div_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:44:58.274972+00:00
-- url     : https://prove2.me/submissions/546f966d-2950-4668-a950-a98e352ef3ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FibOfZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HaarDisintegrationAveragedFibreMeasures

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped Pointwise ENNReal NNReal
open GlobalTheory GlobalTheory.QuadFibre
namespace GlobalTheory.QuadFibre
theorem _root_.solution {K : Type} [NontriviallyNormedField K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsAddHaarMeasure] {a : K} (ha : a ≠ 0) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ Measure.map (fun t : K => t / a) ν = c • ν := by
  refine ⟨distribHaarChar K (Units.mk0 a ha), (distribHaarChar_pos).ne', ?_⟩
  ext S hS
  have hpre : (fun t : K => t / a) ⁻¹' S = (Units.mk0 a ha) • S := by
    ext t
    rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, Units.val_inv_eq_inv_val,
      Units.val_mk0, smul_eq_mul, div_eq_inv_mul]
  have hf : Measurable (fun t : K => t / a) := (continuous_id.div_const a).measurable
  rw [Measure.map_apply hf hS, hpre, ← distribHaarChar_mul ν,
    Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
end GlobalTheory.QuadFibre
