-- Prove2me | solution 1 for GlobalTheory.DualFormExists.clBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:04:32.605292+00:00
-- url     : https://prove2.me/submissions/970539d7-4372-4f91-ac30-3e381aab113c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualFormExistsUnique
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
noncomputable section
open GlobalTheory GlobalTheory.DualFormExists
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.DualFormExists
theorem _root_.solution (ξ : E) (hξ : ξ ≠ 0) (i) : clBasis ξ hξ i = riemannCl ξ (Module.finBasis ℚ E i) := by
  simp [clBasis]
end GlobalTheory.DualFormExists
