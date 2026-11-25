-- Prove2me | solution 1 for GlobalTheory.MaxLatLam.factor_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:02:04.065099+00:00
-- url     : https://prove2.me/submissions/a9bb916d-6d96-4848-842b-56197f203f11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalLatticeLocalFactorProductPosAndLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
noncomputable section
open GlobalTheory GlobalTheory.MaxLatLam
namespace GlobalTheory.MaxLatLam
theorem _root_.solution {q : ℝ} (hq : 2 ≤ q) {n : ℕ} (hn : 1 ≤ n) :
    0 < (q ^ n - (-1) ^ n) / (q + 1) ∧ (q ^ n - (-1) ^ n) / (q + 1) ≤ (q ^ 2) ^ ((n : ℝ) / 2) := by
  have h1 : q ≤ q ^ n := le_self_pow₀ (by linarith) (by omega)
  have h2 : (-1 : ℝ) ^ n = 1 ∨ (-1 : ℝ) ^ n = -1 := neg_one_pow_eq_or ℝ n
  have h3 : (q ^ 2) ^ ((n : ℝ) / 2) = q ^ n := by
    rw [← Real.rpow_natCast q 2, ← Real.rpow_mul (by linarith), ← Real.rpow_natCast q n]
    congr 1
    push_cast
    ring
  refine ⟨div_pos (by rcases h2 with e | e <;> rw [e] <;> linarith) (by linarith), ?_⟩
  rw [h3, div_le_iff₀ (by linarith)]
  rcases h2 with e | e <;> rw [e] <;> nlinarith
end GlobalTheory.MaxLatLam
