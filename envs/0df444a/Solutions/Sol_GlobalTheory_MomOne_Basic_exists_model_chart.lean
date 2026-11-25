-- Prove2me | solution 1 for GlobalTheory.MomOne.Basic.exists_model_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:08:37.798839+00:00
-- url     : https://prove2.me/submissions/23cdadb6-654f-4b34-bfcd-1c2d04082e70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Theorems.Thm_GlobalTheory_MomOne_Basic_exists_ok
import Theorems.Thm_GlobalTheory_MomOne_Basic_exists_chart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.MomOne
variable {q : ℕ} [Fact q.Prime]
open GlobalTheory.MomOne.Basic
open Filter Topology
namespace GlobalTheory.MomOne.Basic
theorem _root_.solution (q : ℕ) [Fact q.Prime] : ∃ (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧), M.Chart ℓ := by
  obtain ⟨M, hM⟩ := exists_ok q
  obtain ⟨ℓ, h, -⟩ := exists_chart M hM
  exact ⟨M, ℓ, h⟩
end GlobalTheory.MomOne.Basic
