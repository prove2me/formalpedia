-- Prove2me | solution 1 for GlobalTheory.T.isUnit_det_pairing_of_bicharacter_of_dvd_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:25:29.638958+00:00
-- url     : https://prove2.me/submissions/d9e8d24d-178d-4603-8723-da88a2671141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsUnitDetPairingOfBicharacterOfDvdTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsUnitDetPairingOfBicharacterOfDvdTraceStatement
import Theorems.Thm_GlobalTheory_isUnit_det_of_bicharacter_of_dvd_trace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O H K Γ : Type) [CommRing O] [IsDomain O] [CommRing H] [Algebra O H] [Field K] [IsAlgClosed K] [Algebra O K] [CommGroup Γ] (r : ℕ) (b : Module.Basis (Fin r) O H) (D : Matrix (Fin r) (Fin r) O) (pt : Γ → (H →ₐ[O] K)) (X : Γ → Γ → K) (c : O), Function.Injective (algebraMap O K) → IsReduced (K ⊗[O] H) → Function.Bijective pt → (∀ a a', X a a' = ∑ i, ∑ j, algebraMap O K (D i j) * pt a (b i) * pt a' (b j)) → (∀ a b, X a b ≠ 0) → (∀ a a' b, X (a * a') b = X a b * X a' b) → (∀ a b b', X a (b * b') = X a b * X a b') → (∀ a, (∀ b, X a b = 1) → a = 1) → c ≠ 0 → (r : O) = c ^ 2 → (∀ h : H, c ∣ Algebra.trace O H h) → IsUnit D.det := by
  first | exact @GlobalTheory.isUnit_det_of_bicharacter_of_dvd_trace | exact GlobalTheory.isUnit_det_of_bicharacter_of_dvd_trace | (intros; apply GlobalTheory.isUnit_det_of_bicharacter_of_dvd_trace <;> assumption)
end _root_.GlobalTheory.T
