-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RootExch.tv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:26:41.44734+00:00
-- url     : https://prove2.me/submissions/4804180e-9404-412d-97ab-5a8d530528fd

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchange
import Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_tv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RootExch
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.RootExch
theorem _root_.solution {Ψ : ι → ι → Prop} (r t : ι) (h : r ≠ t) (s : K) (hrt : Ψ r t) :
    tv r t h s ∈ patSet K Ψ := by
  intro i j
  constructor
  · intro hij
    subst hij
    have hh : ¬ (i = r ∧ i = t) := fun h' => h (h'.1.symm.trans h'.2)
    rw [tv_apply, if_neg hh]
    simp
  · intro hij hn
    have hh : ¬ (i = r ∧ j = t) := by
      rintro ⟨rfl, rfl⟩
      exact hn hrt
    rw [tv_apply, if_neg hh]
    simp [Matrix.one_apply, hij]
end GlobalTheory.CompanionTheory.RootExch
