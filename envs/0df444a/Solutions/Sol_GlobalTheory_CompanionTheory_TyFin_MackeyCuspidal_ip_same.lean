-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal.ip_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:36:23.462893+00:00
-- url     : https://prove2.me/submissions/a4e68bd5-d5fe-4d7a-adde-b787401b359f

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
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_MackeyCuspidal_glEquiv_glEquiv
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_Formalism_L2_NT_IsTeich_injective
import Theorems.Thm_GlobalTheory_T_inner_product_cuspidal_iso
import Theorems.Thm_GlobalTheory_T_same_partition_statement
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
theorem _root_.solution (b : ι → Fin s) (π : Fin s ≃ Fin s') (β : ι → Fin s') (hβ : β = π ∘ b) (b' : ι → Fin s')
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    (mu : ∀ c : Fin s', FDRep ℂ (GL {i // b' i = c} K))
    (e : ∀ c : Fin s', {i // β i = c} ≃ {j // b' j = c})
    (hl : ∀ c, Simple (lam c)) (hm : ∀ c, Simple (mu c)) :
    ip ((parab K b ⊓ parab K β : Subgroup (GL ι K)) : Set (GL ι K))
      (hcFun b fun c => (lam c).character)
      (hcFun β fun c x => (mu c).character (glEquiv K (e c) x)) =
      if ∀ c, CuspIso K (lam c) (mu (π c)) then 1 else 0 := by
  subst hβ
  rw [GlobalTheory.T.same_partition_statement K ι s s' b π]
  have key : ∀ c, ip Set.univ (lam c).character (fun x => (mu (π c)).character
      (glEquiv K (e (π c)) (glEquiv K (Equiv.subtypeEquivRight (p := fun i => b i = c)
        (q := fun i => (π ∘ b) i = π c) fun _ => π.injective.eq_iff.symm) x))) =
      if CuspIso K (lam c) (mu (π c)) then 1 else 0 := by
    intro c
    simp only [glEquiv_glEquiv]
    exact (GlobalTheory.T.inner_product_cuspidal_iso K _ _ (lam c) (mu (π c)) _ (hl c) (hm (π c))).1
  rw [Finset.prod_congr rfl fun c _ => key c, Finset.prod_boole]
  simp
end GlobalTheory.CompanionTheory.TyFin.MackeyCuspidal
