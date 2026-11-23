-- Prove2me | solution 1 for GlobalTheory.SS.Dil.dd_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:46.316825+00:00
-- url     : https://prove2.me/submissions/7e99a492-5584-4d76-9ae6-4b0b2016dc38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_UnramifiedIdealLocusCharacterization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Dil
variable {R B S : Type} [CommRing R] [CommRing B] [CommRing S] [Algebra R B] [Algebra B S]
namespace GlobalTheory.SS.Dil
theorem _root_.solution (x y : B) :
    dd R B S (x * y) = algebraMap B S x • dd R B S y + algebraMap B S y • dd R B S x := by
  simp [dd, tmul_add]
end GlobalTheory.SS.Dil
