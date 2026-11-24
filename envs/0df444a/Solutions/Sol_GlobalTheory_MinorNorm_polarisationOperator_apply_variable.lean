-- Prove2me | solution 1 for GlobalTheory.MinorNorm.polarisationOperator_apply_variable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:38:04.193872+00:00
-- url     : https://prove2.me/submissions/eab3997a-5542-4681-b07f-209b963652b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
import Theorems.Thm_GlobalTheory_MinorNorm_pol_apply

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
variable {x d}
namespace GlobalTheory.MinorNorm
theorem _root_.solution (hd : ∀ r j s c, d r j (x s c) = if r = s ∧ j = c then 1 else 0) (i j s c : Fin k) :
    pol x d i j (x s c) = if c = j then x s i else 0 := by
  rw [pol_apply]
  simp only [hd]
  by_cases h : c = j
  · subst h; simp
  · simp [h, Ne.symm h]
end GlobalTheory.MinorNorm
