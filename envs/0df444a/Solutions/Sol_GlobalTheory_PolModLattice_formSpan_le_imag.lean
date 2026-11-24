-- Prove2me | solution 1 for GlobalTheory.PolModLattice.formSpan_le_imag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:27:09.546793+00:00
-- url     : https://prove2.me/submissions/c2ab56d8-e3d0-4aa3-afb4-c5e16c6104f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PolarizationModuleUnitDual
import Theorems.Thm_GlobalTheory_PolModLattice_altForm_bar

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
theorem _root_.solution (L : Submodule (OF E) E) : formSpan L ≤ imagPart E := by
  rw [formSpan, Submodule.span_le]
  rintro _ ⟨x, -, y, -, rfl⟩
  exact altForm_bar x y
end GlobalTheory.PolModLattice
