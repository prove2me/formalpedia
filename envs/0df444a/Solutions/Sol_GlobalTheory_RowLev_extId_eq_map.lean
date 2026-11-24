-- Prove2me | solution 1 for GlobalTheory.RowLev.extId_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:15:33.402695+00:00
-- url     : https://prove2.me/submissions/81ea00f0-21d8-491f-baf1-31bb3fdf2b2a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralAdeleIdealOfIdealPrincipalAndInter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev
open Formalism.UG Formalism.UG.P Inhab
namespace GlobalTheory.RowLev
theorem _root_.solution (I : AutInst) (𝔞 : Ideal (𝓞 I.E)) : extId I 𝔞 = 𝔞.map (psi I.F I.E) := by
  unfold extId Ideal.map
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, hz⟩
    exact ⟨a, ha, (Subtype.ext hz).symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
end GlobalTheory.RowLev
