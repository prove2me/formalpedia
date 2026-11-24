-- Prove2me | solution 1 for GlobalTheory.BK.mem_uPow_iff_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:45:24.866901+00:00
-- url     : https://prove2.me/submissions/2af3bcc4-81bb-472a-bacb-3883a7cbad7d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesVecReduceModUMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ConnPhiExtensionGeneratorEqZeta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {K : Type} [NormedField K] {a : ℕ} {ι κ : Type}
namespace GlobalTheory.BK
theorem _root_.solution {m : ℕ} {v : Vec K a ι} :
    v ∈ uPow K a ι m ↔ ∃ w : Vec K a ι, v = (X : K⟦X⟧) ^ m • w := by
  constructor
  · intro h
    choose w hw using h
    exact ⟨w, funext fun τ => funext fun i => hw τ i⟩
  · rintro ⟨w, rfl⟩ τ i
    exact Dvd.intro _ rfl
end GlobalTheory.BK
