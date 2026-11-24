-- Prove2me | solution 1 for GlobalTheory.WeylDuality.dualWeyl_int_fg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:31.621861+00:00
-- url     : https://prove2.me/submissions/7fe03cce-f0ee-4ccd-abcf-436c4ee4de39

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ApplyWordMemDualWeyl
import Theorems.Thm_Formalism_GradedWeylDivisibility_sSBasis
import Theorems.Thm_Formalism_GradedWeylDivisibility_sSIdxFinite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.WeylDuality
namespace GlobalTheory.WeylDuality
theorem _root_.solution (r n : ℕ) (ν : Fin n → ℕ) : (dualWeyl ℤ r n ν).FG := by
  obtain ⟨b, hb, -⟩ := sSBasis ℤ r n ν
  obtain ⟨-, hspan, -⟩ := hb
  have := (sSIdxFinite r n ν).to_subtype
  rw [← hspan]
  exact Submodule.fg_span (Set.finite_range b)
end GlobalTheory.WeylDuality
