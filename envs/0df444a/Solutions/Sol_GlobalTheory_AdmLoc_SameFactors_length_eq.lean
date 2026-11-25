-- Prove2me | solution 1 for GlobalTheory.AdmLoc.SameFactors.length_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:29:31.500747+00:00
-- url     : https://prove2.me/submissions/80ac732e-ba5e-4892-b7d2-4c633c702d30

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_ReciprocityTheory_BasicDefinitions_AdRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdmLoc
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open ReciprocityTheory.Def (Z1 B1 H1 d0 d1 C1)
open scoped Pointwise
variable {R : Type} [Ring R]
variable {M N P : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
namespace GlobalTheory.AdmLoc
namespace SameFactors
theorem _root_.solution (h : SameFactors R M N) : Module.length R M = Module.length R N := by
  obtain ⟨s, t, h1, h2, h3, h4, e, -⟩ := h
  rw [← Module.length_compositionSeries s h1 h2, ← Module.length_compositionSeries t h3 h4]
  exact congrArg _ (Fin.equiv_iff_eq.mp ⟨e⟩)
end SameFactors
end GlobalTheory.AdmLoc
