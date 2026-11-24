-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BruhatInv.cnt_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:52:39.643483+00:00
-- url     : https://prove2.me/submissions/c892c397-02b6-40fc-98e6-bde9fcc9c9fa

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionUnique
import Theorems.Thm_GlobalTheory_CompanionTheory_BruhatInv_rank_cut_le
import Theorems.Thm_GlobalTheory_CompanionTheory_BruhatInv_rank_cut_pm

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
    cnt b b' τ a a' ≤ cnt b b' σ a a' := by
  obtain ⟨β, hβ, α, hα, e⟩ := h
  have hM : ((pm K τ : GL ι K) : Matrix ι ι K) =
      (β : Matrix ι ι K) * ((pm K σ : GL ι K) : Matrix ι ι K) * (α : Matrix ι ι K) := by
    rw [e]; simp [Units.val_mul]
  have key := rank_cut_le (K := K) (fun i => a' ≤ (b' i : ℕ)) (fun j => (b j : ℕ) < a)
    (β : Matrix ι ι K) ((pm K σ : GL ι K) : Matrix ι ι K) (α : Matrix ι ι K)
    (fun i j hi hj => hβ.1 i j (by
      rw [Fin.lt_def]; exact lt_of_lt_of_le (not_le.mp hj) hi))
    (fun i j hj hi => hα.1 i j (by
      rw [Fin.lt_def]; exact lt_of_lt_of_le hj (not_lt.mp hi)))
  rw [← hM, rank_cut_pm, rank_cut_pm] at key
  exact key
end GlobalTheory.CompanionTheory.BruhatInv
