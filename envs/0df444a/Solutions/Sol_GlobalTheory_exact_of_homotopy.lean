-- Prove2me | solution 1 for GlobalTheory.exact_of_homotopy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:38:05.386247+00:00
-- url     : https://prove2.me/submissions/28079e4d-f0ee-458b-9da5-b944d2400902

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Function
open GlobalTheory
variable {R : Type*} [CommRing R] {A B C : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
namespace GlobalTheory
theorem _root_.solution {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    {s : B →ₗ[R] A} {t : C →ₗ[R] B} (h : f ∘ₗ s + t ∘ₗ g = LinearMap.id) : Exact f g := by
  intro x
  constructor
  · intro hx
    refine ⟨s x, ?_⟩
    simpa [hx] using LinearMap.congr_fun h x
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun hfg y
end GlobalTheory
