-- Prove2me | solution 1 for GlobalTheory.T.le_mul_setIntegral_image2_of_forall_le_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:27.581796+00:00
-- url     : https://prove2.me/submissions/1aa3284b-2657-4a55-aa86-f333d2f22594

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeMulSetIntegralImage2OfForallLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeMulSetIntegralImage2OfForallLeStatement
import Theorems.Thm_GlobalTheory_le_mul_setIntegral_image2_of_forall_le


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
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : ℕ) (Θ : (Fin N → ℝ) → G) (Q : Set (Fin N → ℝ)) (B : Set G) (K : ℝ), Continuous Θ → IsCompact Q → IsCompact B → B ∈ nhds (1 : G) → 0 ≤ K → ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : G → ℝ) (a : ℝ), Continuous F → (∀ g, 0 ≤ F g) → (∀ x ∈ B, a ≤ K * ∫ t in Q, F (Θ t * x)) → a ≤ C * ∫ x in Set.image2 (fun t b => Θ t * b) Q B, F x ∂μ := by
  first | exact @GlobalTheory.le_mul_setIntegral_image2_of_forall_le | exact GlobalTheory.le_mul_setIntegral_image2_of_forall_le | (intros; apply GlobalTheory.le_mul_setIntegral_image2_of_forall_le <;> assumption)
end _root_.GlobalTheory.T
