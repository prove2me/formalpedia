-- Prove2me | solution 1 for GlobalTheory.MinorNorm.pol_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:29:13.390607+00:00
-- url     : https://prove2.me/submissions/a8212329-01dc-4de4-8fa1-2acdc0610a8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
variable {R : Type} [CommRing R] [Algebra ℂ R]
variable {k : ℕ} (x : Fin k → Fin k → R) (d : Fin k → Fin k → Derivation ℂ R R)
namespace GlobalTheory.MinorNorm
theorem _root_.solution (i j : Fin k) (P : R) : pol x d i j P = ∑ r, x r i * d r j P := by
  unfold pol
  have : ∀ s : Finset (Fin k), (∑ r ∈ s, x r i • d r j) P = ∑ r ∈ s, x r i * d r j P := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [Finset.sum_insert ha, ih]
  exact this _
end GlobalTheory.MinorNorm
