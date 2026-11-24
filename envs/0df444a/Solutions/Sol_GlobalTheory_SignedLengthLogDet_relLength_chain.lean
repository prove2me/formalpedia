-- Prove2me | solution 1 for GlobalTheory.SignedLengthLogDet.relLength_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:48:14.927019+00:00
-- url     : https://prove2.me/submissions/407042d4-ae8d-43e0-b945-949d916e1a51

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthEqLogOrdFracDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3 u_4
open GlobalTheory GlobalTheory.SignedLengthLogDet
open Module
namespace GlobalTheory.SignedLengthLogDet
theorem _root_.solution {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    {A D C : Submodule R V} (hCD : C ≤ D) (hDA : D ≤ A) :
    relLength A C = relLength A D + relLength D C := by
  have hle : C.submoduleOf A ≤ D.submoduleOf A := Submodule.comap_mono hCD
  have hf : C.submoduleOf D ≤ (C.submoduleOf A).comap (Submodule.inclusion hDA) :=
    fun x hx => hx
  have := Module.length_eq_add_of_exact
    (Submodule.mapQ (C.submoduleOf D) (C.submoduleOf A) (Submodule.inclusion hDA) hf)
    (Submodule.factor hle) ?_ (Submodule.factor_surjective hle) ?_
  · rw [relLength_def, this, add_comm]; rfl
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    exact hx
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro hy
      have hy' : (Submodule.Quotient.mk y : A ⧸ D.submoduleOf A) = 0 := hy
      rw [Submodule.Quotient.mk_eq_zero] at hy'
      exact ⟨Submodule.Quotient.mk ⟨y, hy'⟩, rfl⟩
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← hx]
      change (Submodule.Quotient.mk (Submodule.inclusion hDA x) : A ⧸ D.submoduleOf A) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact x.2
end GlobalTheory.SignedLengthLogDet
