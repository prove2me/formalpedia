-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal.term_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:44:31.824482+00:00
-- url     : https://prove2.me/submissions/154161d8-aff1-42cc-806e-aa1772122961

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
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_MackeyCuspidal_ip_same
import Theorems.Thm_GlobalTheory_T_permutation_matrix_properties


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
open Classical
namespace GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal
theorem _root_.solution (σ : Equiv.Perm (Fin n)) (π : Fin s ≃ Fin s') (h : b' ∘ σ = π ∘ b)
    (hl : ∀ c, Simple (lam c)) (hm : ∀ c, Simple (mu c)) :
    ip ((parab K b ⊓ cj (pm K σ) (parab K b') : Subgroup (GL (Fin n) K)) : Set (GL (Fin n) K))
      (hcFun b fun c => (lam c).character)
      (fun x => hcFun b' (fun c => (mu c).character) (pm K σ * x * (pm K σ)⁻¹)) =
      if ∀ c, CuspIso K (lam c) (mu (π c)) then 1 else 0 := by
  obtain ⟨-, h2, h3, h4⟩ := GlobalTheory.T.permutation_matrix_properties K (Fin n) σ
  have hf : (fun x => hcFun b' (fun c => (mu c).character) (pm K σ * x * (pm K σ)⁻¹)) =
      hcFun (b' ∘ σ) (fun c x => (mu c).character (glEquiv K
        (σ.subtypeEquiv (p := fun i => (b' ∘ σ) i = c) (q := fun j => b' j = c) fun _ => Iff.rfl) x)) := by
    funext x
    rw [h2, h4 s' b']
  rw [hf, h3 s' b']
  exact ip_same b π (b' ∘ σ) h b' lam mu _ hl hm
end GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal
