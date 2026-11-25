-- Prove2me | solution 1 for GlobalTheory.T.exists_holomorphic_local_inverse_of_injOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:19:55.3762+00:00
-- url     : https://prove2.me/submissions/c1e257a6-709c-4dc6-979b-e44571fceeda

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsHolomorphicLocalInverseOfInjOn
import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotInjOnOfFderivEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsHolomorphicLocalInverseOfInjOnStatement
import Theorems.Thm_GlobalTheory_InjHol_exists_local_inverse_of_injOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (W : Set (V n)) (g : V n → V n) (a : V n), IsOpen W → a ∈ W → DifferentiableOn ℂ g W → Set.InjOn g W → ∃ h : V n → V n, ∀ᶠ u in 𝓝 (g a), h u ∈ W ∧ g (h u) = u ∧ DifferentiableAt ℂ h u := by
  first | exact @GlobalTheory.InjHol.exists_local_inverse_of_injOn | exact GlobalTheory.InjHol.exists_local_inverse_of_injOn | (intros; apply GlobalTheory.InjHol.exists_local_inverse_of_injOn <;> assumption)
end _root_.GlobalTheory.T
