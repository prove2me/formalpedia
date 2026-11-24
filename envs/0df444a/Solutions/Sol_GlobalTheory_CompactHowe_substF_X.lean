-- Prove2me | solution 1 for GlobalTheory.CompactHowe.substF_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:16:03.951799+00:00
-- url     : https://prove2.me/submissions/328d77b8-4a84-4b39-898f-07091f02fabb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeAevalLeOfLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.CompactHowe
variable {ι : Type} {N n : ℕ}
namespace GlobalTheory.CompactHowe
theorem _root_.solution (h : ι → Matrix (Fin N) (Fin N) ℂ) (g : ι → Matrix (Fin n) (Fin n) ℂ) (p : ι × Fin N × Fin n) :
    substF h g (X p) = ∑ k, ∑ l, C (h p.1 k p.2.1 * g p.1 l p.2.2) * X (p.1, k, l) := aeval_X _ _
end GlobalTheory.CompactHowe
