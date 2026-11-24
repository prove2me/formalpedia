-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.Bruhat.isBlockUT_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:47:25.903953+00:00
-- url     : https://prove2.me/submissions/999caca0-0d74-469a-933c-a2af63eb2a05

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
theorem _root_.solution {s : ℕ} (b : Fin n → Fin s) (τ : Equiv.Perm (Fin n))
    (hτ : Monotone (b ∘ τ)) {x : GL (Fin n) K} (hx : x ∈ borel n K) :
    IsBlockUT K b ((pm K τ * x * (pm K τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  intro i j hij
  rw [conj_pm_apply]
  refine (mem_borel_iff x).1 hx _ _ ?_
  by_contra hle
  have h : b i ≤ b j := by simpa [Function.comp_apply] using hτ (not_lt.1 hle)
  exact absurd hij (not_lt.2 h)
end GlobalTheory.CompanionTheory.TyFin.Bruhat
