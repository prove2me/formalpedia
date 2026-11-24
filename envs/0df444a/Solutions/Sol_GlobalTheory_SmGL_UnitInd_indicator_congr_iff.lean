-- Prove2me | solution 1 for GlobalTheory.SmGL.UnitInd.indicator_congr_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:50:25.27172+00:00
-- url     : https://prove2.me/submissions/98f62ea1-f0b8-4d41-91d3-e1ee5bd7897d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
namespace GlobalTheory.SmGL.UnitInd
theorem _root_.solution {A B : Type} {S : Set A} {T : Set B} {a : A} {b : B} {f : A → ℝ≥0∞} {g : B → ℝ≥0∞}
    (h : a ∈ S ↔ b ∈ T) (h' : f a = g b) : S.indicator f a = T.indicator g b := by
  by_cases hb : b ∈ T
  · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (h.2 hb), h']
  · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem (mt h.1 hb)]
end GlobalTheory.SmGL.UnitInd
