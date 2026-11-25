-- Prove2me | solution 1 for GlobalTheory.T.approximate_identity_product_bumps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:12:26.707219+00:00
-- url     : https://prove2.me/submissions/a874ef5e-1f54-4cca-8ce6-245401571d1e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ApproximateIdentityProductBumps
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ApproximateIdentityProductBumpsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_BigCell_prod_coordinate_bumps


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G A ι : Type) [AddCommGroup G] [TopologicalSpace G] [AddCommGroup A] [TopologicalSpace A] [T2Space A] [Fintype ι] (e : G ≃ₜ+ (ι → A)) (ρ : ℕ → A → ℝ), (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ ∀ y, 0 ≤ ρ k y) → Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : A)).smallSets → (∀ k, Continuous (fun T : G => ∏ i, ρ k (e T i)) ∧ HasCompactSupport (fun T : G => ∏ i, ρ k (e T i)) ∧ ∀ T : G, 0 ≤ ∏ i, ρ k (e T i)) ∧ Filter.Tendsto (fun k => tsupport (fun T : G => ∏ i, ρ k (e T i))) Filter.atTop (nhds (0 : G)).smallSets := by
  first | exact @GlobalTheory.CompanionTheory.BigCell.prod_coordinate_bumps | exact GlobalTheory.CompanionTheory.BigCell.prod_coordinate_bumps | (intros; apply GlobalTheory.CompanionTheory.BigCell.prod_coordinate_bumps <;> assumption)
end _root_.GlobalTheory.T
