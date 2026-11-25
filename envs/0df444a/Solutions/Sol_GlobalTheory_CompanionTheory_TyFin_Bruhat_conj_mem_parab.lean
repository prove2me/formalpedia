-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Bruhat.conj_mem_parab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:12:11.688701+00:00
-- url     : https://prove2.me/submissions/acfb9131-984e-4d4a-9194-66114ba6217d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionTwoBlocks
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Bruhat_isBlockUT_conj

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
theorem _root_.solution {s : ℕ} (b : Fin n → Fin s) (τ : Equiv.Perm (Fin n))
    (hτ : Monotone (b ∘ τ)) {x : GL (Fin n) K} (hx : x ∈ borel n K) :
    pm K τ * x * (pm K τ)⁻¹ ∈ parab K b := by
  refine ⟨isBlockUT_conj b τ hτ hx, ?_⟩
  have e : (pm K τ * x * (pm K τ)⁻¹)⁻¹ = pm K τ * x⁻¹ * (pm K τ)⁻¹ := by group
  rw [e]
  exact isBlockUT_conj b τ hτ ((borel n K).inv_mem hx)
end GlobalTheory.CompanionTheory.TyFin.Bruhat
