-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AnalyticWord.comb_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:17:17.323128+00:00
-- url     : https://prove2.me/submissions/97632579-b1cc-432b-aaaf-4d3c0814c4c1

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SkewAdjointCasimirSpectral
import Theorems.Thm_GlobalTheory_CompanionTheory_AnalyticWord_le_bnd

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
theorem _root_.solution {l : List ι} {k : ℕ} (hl : l.length = k) (a : Fin m → ℂ) :
    ‖j (word Z l (∑ f, a f • y f))‖ ≤ (∑ f, ‖a f‖) * bnd j Z y k := by
  rw [map_sum, map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun f _ => ?_)
  rw [map_smul, map_smul, norm_smul]
  exact mul_le_mul_of_nonneg_left (GlobalTheory.CompanionTheory.AnalyticWord.le_bnd j Z y hl f) (norm_nonneg _)
end GlobalTheory.CompanionTheory.AnalyticWord
