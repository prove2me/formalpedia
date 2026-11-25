-- Prove2me | solution 1 for GlobalTheory.T.exists_imagQuadratic_subfield_of_toricCMFieldData
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:22:04.426265+00:00
-- url     : https://prove2.me/submissions/f5fd57d0-1874-45a7-b3d2-bda8916678b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsImagQuadraticSubfieldOfToricCMFieldData
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_VpBounds
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_LatticeNormTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsImagQuadraticSubfieldOfToricCMFieldDataStatement
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ClassZetaValuationBounds_ToricDenominatorLevel_exact
import Theorems.Thm_GlobalTheory_QuadInHost_exists_quadField


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (d : ℕ) (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → d % 4 = 3 → ∀ (Λ : PeriodPair), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ → ∃ K : IntermediateField ℚ E, Module.finrank ℚ K = 2 ∧ discr K = -(d : ℤ) ∧ ∃ φK : K →+* ℂ, (∀ i, (φ i).comp (algebraMap K E) = φK) ∧ (starRingEnd ℂ).comp φK ≠ φK ∧ IsLatOf φK 1 Λ := by
  first | exact @GlobalTheory.QuadInHost.exists_quadField | exact GlobalTheory.QuadInHost.exists_quadField | (intros; apply GlobalTheory.QuadInHost.exists_quadField <;> assumption)
end _root_.GlobalTheory.T
