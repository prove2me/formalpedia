-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BruhatInv.cnt_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:08:31.370808+00:00
-- url     : https://prove2.me/submissions/7a879c21-0aca-4f81-8b8a-c8282f5334ba

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_BruhatInv_cnt_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.BruhatInv
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.BruhatInv
theorem _root_.solution {s s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s') (σ τ : Equiv.Perm ι)
    (h : ∃ β ∈ parab K b', ∃ α ∈ parab K b, pm K τ = β * pm K σ * α) (a a' : ℕ) :
    cnt b b' τ a a' = cnt b b' σ a a' := by
  refine le_antisymm (cnt_le (K := K) b b' σ τ h a a') (cnt_le (K := K) b b' τ σ ?_ a a')
  obtain ⟨β, hβ, α, hα, e⟩ := h
  refine ⟨β⁻¹, inv_mem hβ, α⁻¹, inv_mem hα, ?_⟩
  rw [e]; group
end GlobalTheory.CompanionTheory.BruhatInv
