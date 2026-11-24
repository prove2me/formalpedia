-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.col_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:53:21.056051+00:00
-- url     : https://prove2.me/submissions/09d76722-39b8-4854-aad5-ec00f840aede

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerBlockEmbeddingConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep GlobalTheory.CompanionTheory.TyFin.ColStep.Conj
variable {K : Type} [Field K]
namespace GlobalTheory.CompanionTheory.TyFin.ColStep.Conj
theorem _root_.solution {d j : ℕ} {u : GL (Fin d) K} (hu : u ∈ patSet K (colGe d j)) (i l : Fin d)
    (hl : (l : ℕ) < j) : (u : Matrix (Fin d) (Fin d) K) i l = if i = l then 1 else 0 := by
  by_cases e : i = l
  · rw [if_pos e]
    exact (hu i l).1 e
  · rw [if_neg e]
    exact (hu i l).2 e (fun c => absurd c.2 (not_le.2 hl))
end GlobalTheory.CompanionTheory.TyFin.ColStep.Conj
