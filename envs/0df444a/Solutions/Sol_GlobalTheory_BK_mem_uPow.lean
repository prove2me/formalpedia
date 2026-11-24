-- Prove2me | solution 1 for GlobalTheory.BK.mem_uPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:03:26.99683+00:00
-- url     : https://prove2.me/submissions/ed41f8bc-7fbf-4fac-8b29-c4b1fa524ea0

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
theorem _root_.solution {m : ℕ} {v : Vec K a ι} : v ∈ uPow K a ι m ↔ ∀ τ i, (X : K⟦X⟧) ^ m ∣ v τ i :=
  Iff.rfl
end GlobalTheory.BK
