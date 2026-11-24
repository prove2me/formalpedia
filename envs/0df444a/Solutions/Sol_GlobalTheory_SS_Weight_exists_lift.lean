-- Prove2me | solution 1 for GlobalTheory.SS.Weight.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:22:02.800719+00:00
-- url     : https://prove2.me/submissions/8caa19e5-b624-42e1-839e-b9afa763d30c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsBasisAdaptedLatticeSubspace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsNilpotentSubOneOfConjPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FinrankLeOfWeightsUnipotentSymplecticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_WeightLeAddOfTorsionPairing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.Weight
open Module
open scoped TensorProduct nonZeroDivisors
namespace GlobalTheory.SS.Weight
theorem _root_.solution (l : ℕ) [Fact l.Prime] {T M : Type} [AddCommGroup T]
    [Module ℤ_[l] T] [AddCommGroup M] (π : ℕ → T →+ M)
    (h1 : ∀ n x, l • π (n + 1) x = π n x) (h0 : ∀ x, π 0 x = 0)
    (hs : ∀ n (a : ℤ_[l]) x, π n (a • x) = (PadicInt.toZModPow n a).val • π n x)
    (hu : ∀ s : ℕ → M, s 0 = 0 → (∀ n, l • s (n + 1) = s n) → ∃! x, ∀ n, π n x = s n)
    (S : M ≃+ M) : ∃ S' : T ≃ₗ[ℤ_[l]] T, ∀ n x, π n (S' x) = S (π n x) := by
  have hext : ∀ x y : T, (∀ n, π n x = π n y) → x = y := fun x y h =>
    (hu (fun n => π n y) (h0 y) (fun n => h1 n y)).unique h fun _ => rfl
  have lin : ∀ S : M ≃+ M, ∃ S' : T →ₗ[ℤ_[l]] T, ∀ n x, π n (S' x) = S (π n x) := by
    intro S
    choose f hf using fun x => (hu (fun n => S (π n x)) (by simp [h0])
      (fun n => by rw [← map_nsmul, h1])).exists
    refine ⟨⟨⟨f, fun x y => hext _ _ fun n => ?_⟩, fun a x => hext _ _ fun n => ?_⟩,
      fun n x => hf x n⟩
    · simp [hf]
    · simp [hf, hs]
  obtain ⟨f, hf⟩ := lin S
  obtain ⟨g, hg⟩ := lin S.symm
  refine ⟨LinearEquiv.ofLinear f g ?_ ?_, hf⟩
  · ext x; exact hext _ _ fun n => by simp [hf, hg]
  · ext x; exact hext _ _ fun n => by simp [hf, hg]
end GlobalTheory.SS.Weight
