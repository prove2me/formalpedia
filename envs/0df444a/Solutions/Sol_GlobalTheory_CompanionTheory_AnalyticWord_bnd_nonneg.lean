-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticWord.bnd_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:00.068808+00:00
-- url     : https://prove2.me/submissions/60160f7d-0d4a-4a7f-9e25-b091b6420882

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
variable [Finite ι] (j : V →ₗ[ℂ] H) (Z : ι → Module.End ℂ V) {m : ℕ} (y : Fin m → V)
namespace GlobalTheory.CompanionTheory.AnalyticWord
theorem _root_.solution (k : ℕ) : 0 ≤ bnd j Z y k := by
  unfold GlobalTheory.CompanionTheory.AnalyticWord.bnd
  exact NNReal.coe_nonneg _
end GlobalTheory.CompanionTheory.AnalyticWord
