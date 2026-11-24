-- Prove2me | solution 1 for GlobalTheory.LengthCokernelInjective.length_coker_of_not_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:54:29.585644+00:00
-- url     : https://prove2.me/submissions/fb43b6f1-00fb-4b23-805b-ff371bc43f08

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCokerOfNotInjective
import Theorems.Thm_GlobalTheory_LengthCokernelInjective_length_self_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.LengthCokernelInjective
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
namespace GlobalTheory.LengthCokernelInjective
theorem _root_.solution (f : M →ₗ[R] M) (hf : LinearMap.ker f ≠ ⊥) :
    Module.length R (M ⧸ LinearMap.range f) = ⊤ := by
  have h1 : Module.finrank R (LinearMap.ker f) ≠ 0 := by
    rwa [ne_eq, Submodule.finrank_eq_zero]
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
  have h3 := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  rw [f.quotKerEquivRange.finrank_eq] at h2
  have h4 : Module.finrank R (M ⧸ LinearMap.range f) ≠ 0 := by omega
  rw [ne_eq, Module.finrank_eq_zero_iff] at h4
  push Not at h4
  obtain ⟨x, hx⟩ := h4
  have h5 : Function.Injective (LinearMap.toSpanSingleton R _ x) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra h0
    exact hx r h0 hr
  have h6 := Module.length_le_of_injective _ h5
  rw [length_self_eq_top] at h6
  exact top_le_iff.mp h6
end GlobalTheory.LengthCokernelInjective
