-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.BruhatInv.cnt_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:21:41.501869+00:00
-- url     : https://prove2.me/submissions/f149b904-cb42-4650-ad76-f6bffa9ea1e3

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionUnique

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
theorem _root_.solution {s s' : ℕ} (b : ι → Fin s) (b' : ι → Fin s') (σ : Equiv.Perm ι)
    (c : Fin s) (c' : Fin s') :
    cnt b b' σ (c + 1) c' + cnt b b' σ c (c' + 1) =
      cnt b b' σ c c' + cnt b b' σ (c + 1) (c' + 1) +
        Fintype.card {i // b i = c ∧ b' (σ i) = c'} := by
  rw [Fintype.card_subtype]
  simp only [cnt, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.ext_iff]
  split_ifs <;> omega
end GlobalTheory.CompanionTheory.BruhatInv
