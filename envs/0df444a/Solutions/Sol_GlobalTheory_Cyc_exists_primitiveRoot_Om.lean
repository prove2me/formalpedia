-- Prove2me | solution 1 for GlobalTheory.Cyc.exists_primitiveRoot_Om
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:31.448612+00:00
-- url     : https://prove2.me/submissions/88b249da-614f-4c7c-926d-683e317ad990

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cyc
open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open scoped IntermediateField
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc
theorem _root_.solution (j : ℕ) : ∃ ζ : Om l, IsPrimitiveRoot ζ (l ^ j) := by
  have hlp : l.Prime := Fact.out
  haveI : NeZero (l ^ j) := ⟨(pow_pos hlp.pos j).ne'⟩
  haveI : CharZero (Om l) := algebraRat.charZero _
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ j)
end GlobalTheory.Cyc
