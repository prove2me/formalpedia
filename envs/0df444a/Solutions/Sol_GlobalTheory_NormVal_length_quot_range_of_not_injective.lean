-- Prove2me | solution 1 for GlobalTheory.NormVal.length_quot_range_of_not_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:14:43.007829+00:00
-- url     : https://prove2.me/submissions/bfb873f3-1ea1-41a9-b23b-616fd83cb6da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsDiscreteValuationRing IsLocalRing Module TensorProduct
open GlobalTheory.NormVal
variable {R M : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
namespace GlobalTheory.NormVal
theorem _root_.solution (f : M →ₗ[R] M) (hf : ¬ Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) = ⊤ := by
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
  rw [f.quotKerEquivRange.finrank_eq] at h1
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  have h3 : 0 < Module.finrank R (LinearMap.ker f) := by
    rw [Nat.pos_iff_ne_zero, Ne, Submodule.finrank_eq_zero, LinearMap.ker_eq_bot]
    exact hf
  have h4 : 0 < Module.finrank R (M ⧸ LinearMap.range f) := by omega
  obtain ⟨v, hv⟩ : ∃ v : M ⧸ LinearMap.range f, ∀ a : R, a • v = 0 → a = 0 := by
    by_contra hcon
    push Not at hcon
    have : Module.finrank R (M ⧸ LinearMap.range f) = 0 := by
      rw [Module.finrank_eq_zero_iff]
      intro v
      obtain ⟨a, ha, ha0⟩ := hcon v
      exact ⟨a, ha0, ha⟩
    omega
  have hinj : Function.Injective (LinearMap.toSpanSingleton R _ v) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact hv a ha
  have h5 := Module.length_le_of_injective _ hinj
  have h6 : Module.length R R = ⊤ := by
    rw [← Ring.ord_zero, Ring.ord_eq_addVal, addVal_zero]
  rwa [h6, top_le_iff] at h5
end GlobalTheory.NormVal
