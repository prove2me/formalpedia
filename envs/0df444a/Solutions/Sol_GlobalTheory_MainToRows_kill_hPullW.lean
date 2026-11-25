-- Prove2me | solution 1 for GlobalTheory.MainToRows.kill_hPullW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:23:34.611186+00:00
-- url     : https://prove2.me/submissions/cda84360-97a5-4767-82c7-bf6638f9ad92

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MainTermImpliesRowHypothesis
import Theorems.Thm_GlobalTheory_MainToRows_killCompl_subst
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
theorem _root_.solution {I : Fin 2 → Type} [∀ g, Fintype (I g)] {n0 n : ℕ} (hn : n0 ≤ n)
    (H : MvPowerSeries (WV I) C) (e : Fin n0 → WV I → C) (e' : Fin n → WV I → C) :
    killCompl (eps hn) (hPullW H e e') = hPullW H e (fun b => e' (Fin.castLE hn b)) := by
  unfold hPullW
  rw [killCompl_subst _ _ (fun k => by simp)]
  congr 1
  funext w
  rw [map_add, map_sum, map_sum, sum_castLE hn (fun b => killCompl (eps hn) (e' b w • X (Sum.inr b)))]
  · simp only [map_smul, kill_inl, kill_inr]
  · intro b hb
    rw [map_smul, kill_inr_zero hn b hb, smul_zero]
end GlobalTheory.MainToRows
