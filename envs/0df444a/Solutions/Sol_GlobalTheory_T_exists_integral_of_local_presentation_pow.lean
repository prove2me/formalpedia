-- Prove2me | solution 1 for GlobalTheory.T.exists_integral_of_local_presentation_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:50:42.847798+00:00
-- url     : https://prove2.me/submissions/360ced62-8f5f-4e8c-a639-02f558beff07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIntegralOfLocalPresentationPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIntegralOfLocalPresentationPowStatement
import Theorems.Thm_GlobalTheory_exists_integral_of_local_presentation


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
theorem _root_.solution : ∀ (O H : Type) [CommRing O] [IsLocalRing O] [CommRing H] [Algebra O H] [Module.Finite O H] (ε : H →ₐ[O] O) (g n : ℕ) (T : Type) [CommRing T] [Algebra H T] [Algebra O T] [IsScalarTower O H T] [IsLocalization.AtPrime T ((IsLocalRing.maximalIdeal O).comap ε)] (εT : T →ₐ[O] O), (∀ h, εT (algebraMap H T h) = ε h) → ∀ (S : Type) [CommRing S] [Algebra O S] (π : S →ₐ[O] T) (x : Fin g → S) (a : Matrix (Fin g) (Fin g) S) (ρ : S →+* MvPowerSeries (Fin g) (IsLocalRing.ResidueField O)), Function.Surjective π → RingHom.ker π = Ideal.span (Set.range (a.mulVec x)) → RingHom.ker εT = Ideal.span (Set.range fun i => π (x i)) → (∀ i j, εT (π (a i j)) = if i = j then (n : O) else 0) → (∀ i, ρ (x i) = MvPowerSeries.X i) → (∀ c ∈ IsLocalRing.maximalIdeal O, ρ (algebraMap O S c) = 0) → ∃ l : H, (∀ h, ε h = 0 → h * l = 0) ∧ (n : O) ^ g ∣ ε l ∧ l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H) := by
  first | exact @GlobalTheory.exists_integral_of_local_presentation | exact GlobalTheory.exists_integral_of_local_presentation | (intros; apply GlobalTheory.exists_integral_of_local_presentation <;> assumption)
end _root_.GlobalTheory.T
