-- Prove2me | solution 1 for GlobalTheory.PhaseLipschitz.continuous_finset_sup_seminorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:26:01.731154+00:00
-- url     : https://prove2.me/submissions/b102fba8-1fd8-4adc-b6da-4433458a6ad8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormSmulLeftLinearPhaseLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCharacterSeminormBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap
open GlobalTheory.Published.Metaplectic
noncomputable section
open GlobalTheory GlobalTheory.PhaseLipschitz
namespace GlobalTheory.PhaseLipschitz
theorem _root_.solution {E ι : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    {p : ι → Seminorm ℂ E} (hp : ∀ i, Continuous (p i)) (s : Finset ι) :
    Continuous ⇑(s.sup p : Seminorm ℂ E) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty]
    exact continuous_const
  | insert i s _ ih =>
    rw [Finset.sup_insert]
    exact ((hp i).max ih).congr fun x => (Seminorm.sup_apply _ _ _).symm
end GlobalTheory.PhaseLipschitz
