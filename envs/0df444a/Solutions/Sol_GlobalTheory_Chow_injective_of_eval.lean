-- Prove2me | solution 1 for GlobalTheory.Chow.injective_of_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:27:40.355916+00:00
-- url     : https://prove2.me/submissions/30bb9853-7b4b-4a25-b958-7c31285234ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsAlgebraicIndependentGenericPoint
import Theorems.Thm_GlobalTheory_Chow_injective_of_constantCoeff
import Theorems.Thm_GlobalTheory_quotientMapCSupSpanLinFormEquiv_mk
import Theorems.Thm_GlobalTheory_quotientSpanLinFormEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.quotientMapCSupSpanLinFormEquiv_mk
attribute [local simp] GlobalTheory.quotientSpanLinFormEquiv_mk



set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.Chow
theorem _root_.solution {R S V : Type*} [CommRing R] [CommRing S]
    (ψ : MvPolynomial V R →+* MvPolynomial V S) (hX : ∀ v, ψ (X v) = X v) (c : V → R) (c' : V → S)
    (hc : ∀ v, ψ (C (c v)) = C (c' v))
    (h : ∀ r, eval c' (ψ (C r)) = 0 → r = 0) : Function.Injective ψ := by
  let τ : MvPolynomial V S →+* MvPolynomial V S := eval₂Hom C fun v => X v + C (c' v)
  let ρ : MvPolynomial V R →+* MvPolynomial V R := eval₂Hom C fun v => X v - C (c v)
  let ρ' : MvPolynomial V R →+* MvPolynomial V R := eval₂Hom C fun v => X v + C (c v)
  have h1 : ρ.comp ρ' = RingHom.id _ := by ext : 1 <;> [ext : 1; skip] <;> simp [ρ, ρ']
  have h2 : constantCoeff.comp τ = eval c' := by ext : 1 <;> [ext : 1; skip] <;> simp [τ]
  have h3 := injective_of_constantCoeff (τ.comp (ψ.comp ρ)) (fun v => by simp [τ, ρ, hX, hc])
    fun r hr => h r (by rw [← h2]; simpa [ρ] using hr)
  have h4 : Function.Injective (ψ.comp ρ) := Function.Injective.of_comp (f := τ) h3
  have hs : Function.Surjective ρ := fun x => ⟨ρ' x, DFunLike.congr_fun h1 x⟩
  intro x y hxy
  obtain ⟨x, rfl⟩ := hs x
  obtain ⟨y, rfl⟩ := hs y
  rw [h4 hxy]
end GlobalTheory.Chow
