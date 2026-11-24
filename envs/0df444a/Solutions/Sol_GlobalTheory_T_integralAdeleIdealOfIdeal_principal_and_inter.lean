-- Prove2me | solution 1 for GlobalTheory.T.integralAdeleIdealOfIdeal_principal_and_inter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:16:09.870969+00:00
-- url     : https://prove2.me/submissions/9c352340-4efb-4a62-95b7-c7ee668d6f33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralAdeleIdealOfIdealPrincipalAndInter
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralAdeleIdealOfIdealPrincipalAndInterStatement
import Theorems.Thm_GlobalTheory_RowLev_extId_principal_and_inter


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (I : AutInst) (𝔞 : Ideal (𝓞 I.E)), 𝔞 ≠ ⊥ → (∃ t : IntAf I.F I.E, IsUnit (t : (I.E ⊗[I.F] Af I.F)) ∧ extId I 𝔞 = Ideal.span {t}) ∧ ∀ (a : 𝓞 I.E) (h : Formalism.UG.inclE (F := I.F) (Af I.F) (a : I.E) ∈ IntAf I.F I.E), (⟨_, h⟩ : IntAf I.F I.E) ∈ extId I 𝔞 ↔ a ∈ 𝔞 := by
  first | exact @GlobalTheory.RowLev.extId_principal_and_inter | exact GlobalTheory.RowLev.extId_principal_and_inter | (intros; apply GlobalTheory.RowLev.extId_principal_and_inter <;> assumption)
end _root_.GlobalTheory.T
