-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal.term_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:00:46.603633+00:00
-- url     : https://prove2.me/submissions/e41aaa2a-14ea-4a73-9f7a-b3aab0791880

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
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_MackeyCuspidal_ip_inter_eq_zero
import Theorems.Thm_GlobalTheory_T_permutation_matrix_properties
import Theorems.Thm_PI_GreenLabelSurjWork_transp_cusp


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
variable {n s s' : ℕ} (b : Fin n → Fin s) (b' : Fin n → Fin s')
  (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
  (mu : ∀ c : Fin s', FDRep ℂ (GL {i // b' i = c} K))
namespace GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal
theorem _root_.solution (σ : Equiv.Perm (Fin n)) (hl : ∀ c, IsCuspidal K (lam c))
    (hm : ∀ c, IsCuspidal K (mu c)) (h : ¬ ∀ i j, b i = b j ↔ b' (σ i) = b' (σ j)) :
    ip ((parab K b ⊓ cj (pm K σ) (parab K b') : Subgroup (GL (Fin n) K)) : Set (GL (Fin n) K))
      (hcFun b fun c => (lam c).character)
      (fun x => hcFun b' (fun c => (mu c).character) (pm K σ * x * (pm K σ)⁻¹)) = 0 := by
  obtain ⟨-, h2, h3, h4⟩ := GlobalTheory.T.permutation_matrix_properties K (Fin n) σ
  let e : ∀ c : Fin s', {i // (b' ∘ σ) i = c} ≃ {j // b' j = c} := fun c =>
    σ.subtypeEquiv (p := fun i => (b' ∘ σ) i = c) (q := fun j => b' j = c) fun _ => Iff.rfl
  have hf : (fun x => hcFun b' (fun c => (mu c).character) (pm K σ * x * (pm K σ)⁻¹)) =
      hcFun (b' ∘ σ) (fun c => (transp (e c).symm (mu c)).character) := by
    funext x
    rw [h2, h4 s' b']
    congr 1
  rw [hf, h3 s' b']
  exact ip_inter_eq_zero b (b' ∘ σ) lam hl _
    (fun c => PI.GreenLabelSurjWork.transp_cusp _ _ (hm c)) h
end GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal
