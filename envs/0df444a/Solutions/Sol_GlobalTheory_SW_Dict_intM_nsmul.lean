-- Prove2me | solution 1 for GlobalTheory.SW.Dict.intM_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:36.547268+00:00
-- url     : https://prove2.me/submissions/b8f0d033-c695-49f9-8eaf-1ad700c873ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Dict
noncomputable section
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW.Dict
namespace _root_.GlobalTheory.SW.Dict
theorem _root_.solution {K κ ι : Type} [Field K] (R : ℕ) {x : Matrix κ ι K}
    (h : _root_.GlobalTheory.SW.IntM x) :
    _root_.GlobalTheory.SW.IntM (R • x) := by
  intro k i
  simpa using (h k i).nsmul R
end _root_.GlobalTheory.SW.Dict
end GlobalTheory.SW.Dict
