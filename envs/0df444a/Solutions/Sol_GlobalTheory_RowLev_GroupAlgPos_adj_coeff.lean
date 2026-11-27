-- Prove2me | solution 1 for GlobalTheory.RowLev.GroupAlgPos.adj_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:23:08.36493+00:00
-- url     : https://prove2.me/submissions/955d0844-2c67-4afa-99a0-87bee9640a54

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfAdjointIdempotentPosType

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowLev GlobalTheory.RowLev.GroupAlgPos
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
variable {Q : Type} [Group Q]
namespace GlobalTheory.RowLev.GroupAlgPos
theorem _root_.solution [Finite Q] (a : MonoidAlgebra ℂ Q) (q : Q) : (adj a).coeff q = star (a.coeff q⁻¹) := rfl
end GlobalTheory.RowLev.GroupAlgPos
