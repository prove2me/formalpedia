-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.IpIso.glEquiv_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:13:24.994217+00:00
-- url     : https://prove2.me/submissions/1bee5e2e-0123-4f8c-88f8-7be0b46abe7c

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIso
import Theorems.Thm_GlobalTheory_T_permutation_matrix_properties
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
theorem _root_.solution (e e' : α ≃ β) (g : GL α K) :
    glEquiv K e' g =
      pm K (e.symm.trans e') * glEquiv K e g * (pm K (e.symm.trans e'))⁻¹ := by
  rw [(GlobalTheory.T.permutation_matrix_properties K β (e.symm.trans e')).2.1]
  apply Units.ext
  ext i j
  rw [PI.GreenLabelSurjWork.glEquiv_val, PI.GreenLabelSurjWork.glEquiv_val,
    PI.GreenLabelSurjWork.glEquiv_val]
  simp
end GlobalTheory.CompanionTheory.TyFin.IpIso
