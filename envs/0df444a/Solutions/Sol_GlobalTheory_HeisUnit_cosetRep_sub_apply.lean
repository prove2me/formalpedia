-- Prove2me | solution 1 for GlobalTheory.HeisUnit.cosetRep_sub_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:25:04.838813+00:00
-- url     : https://prove2.me/submissions/0260aed3-494c-4287-992e-02ac92e82dd0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryAndSeparates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergCosetRepTranslatesOrthogonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.HeisUnit
namespace GlobalTheory.HeisUnit
theorem _root_.solution {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n d : ℕ} (ϖ : kˣ) (i0 : Fin n) (T T' : Fin d → SplitFlip.Res k 1) (j : Fin d) :
    (cosetRep ϖ i0 T' - cosetRep ϖ i0 T) i0 j =
      (ϖ : k)⁻¹ * (((Quotient.out (T j) : 𝒪[k]) : k) - ((Quotient.out (T' j) : 𝒪[k]) : k)) := by
  simp [cosetRep]; ring
end GlobalTheory.HeisUnit
