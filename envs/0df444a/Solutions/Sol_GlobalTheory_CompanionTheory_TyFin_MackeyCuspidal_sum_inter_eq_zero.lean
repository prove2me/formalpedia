-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal.sum_inter_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:58:38.746228+00:00
-- url     : https://prove2.me/submissions/282822ed-2ee3-4d37-a109-b351cfd9b725

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
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_MackeyCuspidal_mem_parab_of_isBlockUT
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_MackeyCuspidal_hcFun_inv_mul
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_GlobalTheory_T_cuspidal_vanishing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
open CategoryTheory
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s s' : ℕ}
open Classical
namespace GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal
theorem _root_.solution (b : ι → Fin s) (β : ι → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (hl : ∀ c, IsCuspidal K (lam c))
    (ψ : ∀ c : Fin s', GL {i // β i = c} K → ℂ) (hs : ∃ i j, b i = b j ∧ β i ≠ β j) :
    (∑ h, if h ∈ parab K b ⊓ parab K β then
      hcFun β ψ h⁻¹ * hcFun b (fun c => (lam c).character) h else 0) = 0 := by
  refine GlobalTheory.T.cuspidal_vanishing K ι s s' b β lam hl hs (parab K b ⊓ parab K β)
    (fun h => hcFun β ψ h⁻¹) inf_le_left ?_
  intro u hu hoff
  have hub : IsBlockUT K b (u : Matrix ι ι K) := fun i j hij => hoff i j (ne_of_gt hij)
  refine ⟨⟨mem_parab_of_isBlockUT b hub, hu.1⟩, fun h hh => ?_⟩
  simp only [mul_inv_rev]
  exact hcFun_inv_mul β ψ hu (inv_mem hh.2)
end GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal
