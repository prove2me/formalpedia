-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FourierMat.entries_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:36:01.475906+00:00
-- url     : https://prove2.me/submissions/6fe71e32-5c87-4819-9ab1-86a110b04317

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInjectiveMatrixSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Matrix FourierTransform InnerProductSpace ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FourierMat
namespace GlobalTheory.CompanionTheory.FourierMat
theorem _root_.solution (m n : ℕ) (u : Fin m → Fin n → ℂ) (p : Fin m × Fin n) :
    entries m n u p = u p.1 p.2 := rfl
end GlobalTheory.CompanionTheory.FourierMat
