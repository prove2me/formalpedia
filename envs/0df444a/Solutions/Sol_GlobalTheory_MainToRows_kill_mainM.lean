-- Prove2me | solution 1 for GlobalTheory.MainToRows.kill_mainM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:23:36.834798+00:00
-- url     : https://prove2.me/submissions/b3060147-924c-488f-ab33-3712d657102c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MainTermImpliesRowHypothesis
import Theorems.Thm_GlobalTheory_MainToRows_kill_inl
import Theorems.Thm_GlobalTheory_MainToRows_kill_inr
import Theorems.Thm_GlobalTheory_MainToRows_kill_inr_zero
import Theorems.Thm_GlobalTheory_MainToRows_sum_castLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds
noncomputable section
open scoped BigOperators
open Classical MvPowerSeries Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open GlobalTheory GlobalTheory.MainToRows
variable {C : Type} [Field C]
namespace GlobalTheory.MainToRows
theorem _root_.solution (V : VF C) (i : ℕ) {n0 n : ℕ} (hn : n0 ≤ n) (Φ : Fin n → Fin n0 → C) :
    killCompl (eps hn) (mainM V i Φ) = mainM V i (fun b c => Φ (Fin.castLE hn b) c) := by
  unfold mainM
  rw [map_smul, map_sum, sum_castLE hn]
  · simp only [map_sum, map_smul, map_mul, map_pow, kill_inl, kill_inr]
  · intro b hb
    simp only [map_sum, map_smul, map_mul, kill_inr_zero hn b hb, mul_zero, smul_zero,
      Finset.sum_const_zero]
end GlobalTheory.MainToRows
