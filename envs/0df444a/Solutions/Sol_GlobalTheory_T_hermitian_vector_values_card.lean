-- Prove2me | solution 1 for GlobalTheory.T.hermitian_vector_values_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:41:15.859299+00:00
-- url     : https://prove2.me/submissions/9f607d17-bf4f-4add-999e-97ef6fa3dfd8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianVectorValuesCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianVectorValuesCardStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_Sphere_count


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (∀ c : E, τ c = c → c ≠ 0 → (Nat.card {v : V // B.h v v = c} : ℝ) = (q : ℝ) ^ (2 * m) / q * (1 - ((ε : ℝ) / q) ^ m)) ∧ (Nat.card {v : V // B.h v v = 0} : ℝ) = (q : ℝ) ^ (2 * m) / q * (1 + ((q : ℝ) - 1) * ((ε : ℝ) / q) ^ m) := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.Sphere.count | exact GlobalTheory.CompanionTheory.UnrDens.Sphere.count | (intros; apply GlobalTheory.CompanionTheory.UnrDens.Sphere.count <;> assumption)
end _root_.GlobalTheory.T
