-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal.hcFun_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:50:09.666489+00:00
-- url     : https://prove2.me/submissions/bc5eb639-07d6-452e-bbfe-1a93bb66cfd9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionTwoBlocksStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionUniqueStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FrobeniusReciprocityInnerProductStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraCharacterStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntertwinerInnerProductStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InnerProductCuspidalIsoStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MackeyInnerProductStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SamePartitionStatementStatement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelSurjective_Transp
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MackeyFormulaAll
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_MackeyCuspidal_blkGL_unip
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_blkGL_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_one_mem_unip


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s s' : ℕ}
namespace GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal
theorem _root_.solution (β : ι → Fin s) (ψ : ∀ c : Fin s, GL {i // β i = c} K → ℂ) {u h : GL ι K}
    (hu : u ∈ unip K β) (hh : h ∈ parab K β) : hcFun β ψ (u⁻¹ * h) = hcFun β ψ h := by
  refine Finset.prod_congr rfl fun c _ => ?_
  have h1 : blkGL β c u⁻¹ = 1 := by
    have := GlobalTheory.CompanionTheory.TyFin.CuspVan.blkGL_mul β c hu.1 (inv_mem hu.1)
    rwa [mul_inv_cancel, blkGL_unip β c hu, one_mul,
      blkGL_unip β c (GlobalTheory.CompanionTheory.TyFin.CuspVan.one_mem_unip β), eq_comm] at this
  rw [GlobalTheory.CompanionTheory.TyFin.CuspVan.blkGL_mul β c (inv_mem hu.1) hh, h1, one_mul]
end GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal
