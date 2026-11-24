-- Prove2me | solution 1 for GlobalTheory.BK.dvd_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:45:23.287822+00:00
-- url     : https://prove2.me/submissions/0d74f4aa-53c1-4b1e-8581-d58b4e44bd97

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
theorem _root_.solution [Fintype ι] {c : K⟦X⟧} (Y : Matrix κ ι K⟦X⟧) {v : ι → K⟦X⟧} (hv : ∀ i, c ∣ v i)
    (j : κ) : c ∣ (Y *ᵥ v) j := Finset.dvd_sum fun i _ => (hv i).mul_left _
end GlobalTheory.BK
