-- Prove2me | solution 1 for GlobalTheory.SignedLengthMapLogDet.relLength_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:48:05.92109+00:00
-- url     : https://prove2.me/submissions/d3f5e9e0-156e-4168-a6cf-b73d4489ba05

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthMapEqLogOrdFracDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open GlobalTheory GlobalTheory.SignedLengthMapLogDet
open Module
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
namespace GlobalTheory.SignedLengthMapLogDet
theorem _root_.solution {A B C : Submodule R V} (hBA : B ≤ A) (hCB : C ≤ B) :
    relLength A C = relLength A B + relLength B C := by
  have hle : C.submoduleOf A ≤ B.submoduleOf A := Submodule.comap_mono hCB
  let i : B →ₗ[R] A ⧸ C.submoduleOf A := (C.submoduleOf A).mkQ ∘ₗ Submodule.inclusion hBA
  have hker : LinearMap.ker i = C.submoduleOf B := by
    ext x
    exact Submodule.Quotient.mk_eq_zero (C.submoduleOf A)
  have hex : Function.Exact (LinearMap.range i).subtype (Submodule.factor hle) := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro hy
      have hy' : (y : V) ∈ B := (Submodule.Quotient.mk_eq_zero (B.submoduleOf A)).mp hy
      exact ⟨⟨_, ⟨⟨y, hy'⟩, rfl⟩⟩, rfl⟩
    · rintro ⟨⟨_, x, rfl⟩, hx⟩
      rw [← hx]
      exact (Submodule.Quotient.mk_eq_zero (B.submoduleOf A)).mpr x.2
  rw [relLength_eq_length_range i hker, relLength_def, relLength_def, add_comm]
  exact Module.length_eq_add_of_exact _ _ (Submodule.injective_subtype _)
    (Submodule.factor_surjective hle) hex
end GlobalTheory.SignedLengthMapLogDet
