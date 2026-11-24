-- Prove2me | solution 1 for GlobalTheory.T.polarization_lattice_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:35:58.176721+00:00
-- url     : https://prove2.me/submissions/c33f96fd-a7c8-4f2e-89ac-131f385e61bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationLatticeFg
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationLatticeFgStatement
import Theorems.Thm_GlobalTheory_polMod_mul_fg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (L : Submodule (OF E) E),
    (∃ N : ℕ, 0 < N ∧ ∀ x ∈ L, IsIntegral ℤ ((N : E) * x)) → IsUnit (polMod L) → (polMod L * L).toAddSubgroup.FG := by
  first | exact @GlobalTheory.polMod_mul_fg | exact GlobalTheory.polMod_mul_fg | (intros; apply GlobalTheory.polMod_mul_fg <;> assumption)
end _root_.GlobalTheory.T
