-- Prove2me | solution 1 for GlobalTheory.LengthCokernelInjective.relLength_map_eq_addVal_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:28:16.569623+00:00
-- url     : https://prove2.me/submissions/40ad37e6-25ec-4945-8eb5-3840027abf40

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthCokerOfNotInjective
import Theorems.Thm_GlobalTheory_LengthCokernelInjective_length_coker

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
theorem _root_.solution {R : Type u_1} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {V : Type u_2} [AddCommGroup V] [Module R V] {A : Submodule R V}
    [Module.Free R A] [Module.Finite R A] (g : V →ₗ[R] V) (hg : ∀ x ∈ A, g x ∈ A) :
    GlobalTheory.relLength A (Submodule.map g A) =
      IsDiscreteValuationRing.addVal R (LinearMap.det (LinearMap.restrict g hg)) := by
  have h : (Submodule.map g A).submoduleOf A = LinearMap.range (LinearMap.restrict g hg) := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
  rw [GlobalTheory.relLength_def, h, length_coker]
end GlobalTheory.LengthCokernelInjective
