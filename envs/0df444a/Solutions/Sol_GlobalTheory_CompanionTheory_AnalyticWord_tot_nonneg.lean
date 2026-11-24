-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticWord.tot_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:24.69408+00:00
-- url     : https://prove2.me/submissions/f4df2fd8-1554-46db-a17f-6b6cc230ded7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AnalyticWord
variable {V H : Type} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : Type}
variable [Fintype ι] (j : V →ₗ[ℂ] H) (Z : ι → Module.End ℂ V) {m : ℕ} (y : Fin m → V)
  (S Ω : Module.End ℂ V) (K : Finset ι) (c : ι → ι → ι → ℂ) (d o : Fin m → Fin m → ℂ)
namespace GlobalTheory.CompanionTheory.AnalyticWord
theorem _root_.solution (a : Fin m → Fin m → ℂ) : 0 ≤ tot a := by
  unfold GlobalTheory.CompanionTheory.AnalyticWord.tot
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
end GlobalTheory.CompanionTheory.AnalyticWord
