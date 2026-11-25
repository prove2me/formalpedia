-- Prove2me | solution 1 for GlobalTheory.T.finrank_mul_pow_le_finrank_of_prod_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:14.526032+00:00
-- url     : https://prove2.me/submissions/1a675661-f5ef-46e1-a057-bf098ebd128f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeriesStatement
import Theorems.Thm_GlobalTheory_finrank_mul_pow_le_finrank_of_powerSeries


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (D n : ℕ) (A : Type) [CommRing A] [Algebra ℂ A] (φ : Fin n → (A →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)) (x : Fin D → A) (c : Fin D → ℂ), (∀ u : A, (∀ j, φ j u = 0) → u = 0) → (∀ j i, φ j (x i) = MvPowerSeries.X i + MvPowerSeries.C (c i)) → ∀ (F G : Submodule ℂ A) [Module.Finite ℂ F] [Module.Finite ℂ G] (m : ℕ), 0 < m → (∀ (f : Fin m → A) (a : Fin D → ℕ), (∀ l, f l ∈ F) → (∀ i, a i < m) → (∏ l, f l) * ∏ i, x i ^ a i ∈ G) → Module.finrank ℂ F * m ^ D ≤ Module.finrank ℂ G := by
  first | exact @GlobalTheory.finrank_mul_pow_le_finrank_of_powerSeries | exact GlobalTheory.finrank_mul_pow_le_finrank_of_powerSeries | (intros; apply GlobalTheory.finrank_mul_pow_le_finrank_of_powerSeries <;> assumption)
end _root_.GlobalTheory.T
