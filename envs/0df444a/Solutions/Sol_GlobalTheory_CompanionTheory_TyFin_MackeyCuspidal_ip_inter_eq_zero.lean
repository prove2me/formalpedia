-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal.ip_inter_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:13:29.512334+00:00
-- url     : https://prove2.me/submissions/e2aaf380-2865-4237-a413-4961c3d3de56

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
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_MackeyCuspidal_sum_inter_eq_zero
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
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
namespace GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal
theorem _root_.solution (b : ι → Fin s) (β : ι → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (hl : ∀ c, IsCuspidal K (lam c))
    (nu : ∀ c : Fin s', FDRep ℂ (GL {i // β i = c} K)) (hn : ∀ c, IsCuspidal K (nu c))
    (hs : ¬ ∀ i j, b i = b j ↔ β i = β j) :
    ip ((parab K b ⊓ parab K β : Subgroup (GL ι K)) : Set (GL ι K))
      (hcFun b fun c => (lam c).character) (hcFun β fun c => (nu c).character) = 0 := by
  classical
  unfold ip
  refine mul_eq_zero_of_right _ ?_
  by_cases hA : ∃ i j, b i = b j ∧ β i ≠ β j
  · refine Eq.trans ?_ (sum_inter_eq_zero b β lam hl (fun c => (nu c).character) hA)
    refine Fintype.sum_equiv (Equiv.inv _) _ _ fun g => ?_
    simp only [Equiv.inv_apply, inv_inv, SetLike.mem_coe]
    by_cases hg : g ∈ parab K b ⊓ parab K β
    · rw [if_pos hg, if_pos (inv_mem hg), mul_comm]
    · rw [if_neg hg, if_neg (fun h => hg (by simpa using inv_mem h))]
  · have hB : ∃ i j, β i = β j ∧ b i ≠ b j := by
      by_contra hB
      push_neg at hA hB
      exact hs fun i j => ⟨hA i j, hB i j⟩
    have := sum_inter_eq_zero β b nu hn (fun c => (lam c).character) hB
    rw [inf_comm] at this
    simpa only [SetLike.mem_coe] using this
end GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal
