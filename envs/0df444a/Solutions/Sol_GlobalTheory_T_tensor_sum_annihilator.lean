-- Prove2me | solution 1 for GlobalTheory.T.tensor_sum_annihilator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:25:36.483655+00:00
-- url     : https://prove2.me/submissions/35bfc8b1-dba8-4fa0-bc6e-6cfbd8048b7e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorSumAnnihilator
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorSumAnnihilatorStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_KillSum_sum_killed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι : Type} (T : Finset ι) (l : ι → Multiset ℂ), ∃ l' : Multiset ℂ, Multiset.card l' = ∏ τ ∈ T, Multiset.card (l τ) ∧
  ∀ (R : Type) [CommRing R] [Algebra ℂ R] (h : ι → R), (∀ τ ∈ T, ((l τ).map fun c => h τ - algebraMap ℂ R c).prod = 0) →
    (l'.map fun c => ∑ τ ∈ T, h τ - algebraMap ℂ R c).prod = 0 := by
  first | exact @GlobalTheory.CompanionTheory.KillSum.sum_killed | exact GlobalTheory.CompanionTheory.KillSum.sum_killed | (intros; apply GlobalTheory.CompanionTheory.KillSum.sum_killed <;> assumption)
end _root_.GlobalTheory.T
