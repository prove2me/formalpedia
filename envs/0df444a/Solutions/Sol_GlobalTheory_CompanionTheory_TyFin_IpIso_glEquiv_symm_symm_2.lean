-- Prove2me | solution 2 for GlobalTheory.CompanionTheory.TyFin.IpIso.glEquiv_symm_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:47:46.920685+00:00
-- url     : https://prove2.me/submissions/c8695713-4b54-4bef-b2e4-7ab3bfb14c24

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
import Theorems.Thm_PI_GreenLabelSurjWork_glEquiv_symm_val
import Theorems.Thm_PI_GreenLabelSurjWork_glEquiv_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.IpIso
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
namespace GlobalTheory.CompanionTheory.TyFin.IpIso
theorem _root_.solution (e : α ≃ β) (g : GL α K) :
    (glEquiv K e.symm).symm g = glEquiv K e g := by
  apply Units.ext
  ext i j
  rw [PI.GreenLabelSurjWork.glEquiv_symm_val, PI.GreenLabelSurjWork.glEquiv_val]
  simp
end GlobalTheory.CompanionTheory.TyFin.IpIso
