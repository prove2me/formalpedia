-- Prove2me | solution 1 for GlobalTheory.PolModLattice.real_of_bar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:55.349506+00:00
-- url     : https://prove2.me/submissions/809e73b7-7449-409b-9776-b012f5f164c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationModuleUnitDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
open GlobalTheory GlobalTheory.PolModLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.PolModLattice
theorem _root_.solution {v : E} (h : bar v = v) : ∃ w : maximalRealSubfield E, (w : E) = v :=
  ⟨⟨v, (IsCMField.complexConj_eq_self_iff E v).1 h⟩, rfl⟩
end GlobalTheory.PolModLattice
