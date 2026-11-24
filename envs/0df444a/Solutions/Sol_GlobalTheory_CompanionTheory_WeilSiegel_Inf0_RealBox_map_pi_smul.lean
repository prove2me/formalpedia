-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.map_pi_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:10:57.260349+00:00
-- url     : https://prove2.me/submissions/879e05c7-5ef3-4c12-bf44-76ec20302e70

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoreR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuadraticBoxVolumeBound
import Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_Inf0_RealBox_pi_smul_const_family

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox
namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox
theorem _root_.solution {P : Type} [Fintype P] (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [(volume : Measure E).IsAddHaarMeasure] (r : P → ℝ) (hr : ∀ w, 0 < r w) :
    (volume : Measure (P → E)).map (fun x w => r w • x w) =
      ENNReal.ofReal (∏ w, (r w ^ Module.finrank ℝ E)⁻¹) • (volume : Measure (P → E)) := by
  have hc : ∀ w, (volume : Measure E).map (fun y => r w • y) =
      Real.toNNReal ((r w ^ Module.finrank ℝ E)⁻¹) • (volume : Measure E) := fun w => by
    rw [Measure.map_addHaar_smul _ (hr w).ne', abs_of_pos (inv_pos.mpr (pow_pos (hr w) _))]
    ext s _
    rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.ofReal]
  haveI : ∀ w, SigmaFinite ((volume : Measure E).map (fun y => r w • y)) := fun w => by
    rw [hc w]; infer_instance
  have hmap := Measure.pi_map_pi (μ := fun _ : P => (volume : Measure E))
    (f := fun w (y : E) => r w • y)
    (fun w => (continuous_id.const_smul (r w)).measurable.aemeasurable)
  beta_reduce at hmap
  rw [volume_pi, hmap]
  simp only [hc]
  rw [GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox.pi_smul_const_family, ← Real.toNNReal_prod_of_nonneg
    (fun w _ => (inv_pos.mpr (pow_pos (hr w) (Module.finrank ℝ E))).le)]
  ext s _
  rw [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.ofReal]
end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealBox
