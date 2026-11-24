-- Prove2me | solution 1 for GlobalTheory.DI.frobDeriv_factors_kaehler
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:24:55.931431+00:00
-- url     : https://prove2.me/submissions/3472b6e0-72de-43ff-a038-8478106443a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FrobeniusDerivationFactorsThroughKaehler
import Theorems.Thm_GlobalTheory_DI_FrobDeriv_twist_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory.DI.FrobDeriv
namespace GlobalTheory.DI
theorem _root_.solution : ∀ {K : Type} [CommRing K] {M : Type} [AddCommGroup M] [Module K M] (p : ℕ) [Fact p.Prime] [CharP K p] (φ : K →+ M), (∀ a b : K, φ (a * b) = a ^ p • φ b + b ^ p • φ a) → ∃ f : Ω[K⁄ℤ] →+ M, (∀ (c : K) v, f (c • v) = c ^ p • f v) ∧ ∀ a, f (KaehlerDifferential.D ℤ K a) = φ a := by
  intro K _ M _ _ p _ _ φ hφ
  let ψ : K →ₗ[ℤ] FrobTwist K p M := (φ : K →+ M).toIntLinearMap
  have hone : φ 1 = 0 := by
    have h := hφ 1 1
    simp only [mul_one, one_pow, one_smul] at h
    have : φ 1 + φ 1 = φ 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  let D : Derivation ℤ K (FrobTwist K p M) :=
    { toLinearMap := ψ
      map_one_eq_zero' := hone
      leibniz' := fun a b => by
        show φ (a * b) = a • (show FrobTwist K p M from φ b) + b • (show FrobTwist K p M from φ a)
        rw [twist_smul, twist_smul, hφ]; rfl }
  refine ⟨(D.liftKaehlerDifferential).toAddMonoidHom, ?_, ?_⟩
  · intro c v
    show D.liftKaehlerDifferential (c • v) = _
    rw [LinearMap.map_smul, twist_smul]
    rfl
  · intro a
    show D.liftKaehlerDifferential (KaehlerDifferential.D ℤ K a) = φ a
    rw [Derivation.liftKaehlerDifferential_comp_D]
    rfl
end GlobalTheory.DI
