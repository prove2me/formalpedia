-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Bruhat.conj_diag_mem_borel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:49:19.300898+00:00
-- url     : https://prove2.me/submissions/4d4fd885-6f1b-4a0b-886d-3a94beacf037

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionTwoBlocks
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Bruhat_conj_pm_apply
import Theorems.Thm_GroundTheory_Automorphic_mem_borel_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin Formalism.IrreducibleCountingLemmas.TYPES GroundTheory.Automorphic
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Bruhat
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}
namespace GlobalTheory.CompanionTheory.TyFin.Bruhat
theorem _root_.solution (ρ : Equiv.Perm (Fin n)) {t : GL (Fin n) K}
    (ht : ∀ i j, i ≠ j → (t : Matrix (Fin n) (Fin n) K) i j = 0) :
    pm K ρ * t * (pm K ρ)⁻¹ ∈ borel n K := by
  refine (mem_borel_iff _).2 fun i j hji => ?_
  rw [conj_pm_apply]
  exact ht _ _ fun e => hji.ne (ρ⁻¹.injective e).symm
end GlobalTheory.CompanionTheory.TyFin.Bruhat
