-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.exists_diag_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:32:54.669381+00:00
-- url     : https://prove2.me/submissions/2fc9ce57-d986-4a70-a5a4-290eb7f24e20

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryCellSumLeviReductionOfSteps
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_fSatake_diag_exists


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L}
    (hσ : σ ϖ = ϖ) (h0 : ϖ ≠ 0) {r : ℕ} (b : Fin r → ℤ) (hb : ∀ i, b i.rev = -b i) :
    ∃ s : GU σ r, mat s = Matrix.diagonal (fun i => ϖ ^ b i) := by
  obtain ⟨s, hs, -⟩ := P.fSatake_diag_exists (σ := σ) (fun i => ϖ ^ b i) (fun i => by
    rw [map_zpow₀, hσ, hb, ← zpow_add₀ h0, add_neg_cancel, zpow_zero])
  exact ⟨s, hs⟩
end GlobalTheory.SatakeWeyl
