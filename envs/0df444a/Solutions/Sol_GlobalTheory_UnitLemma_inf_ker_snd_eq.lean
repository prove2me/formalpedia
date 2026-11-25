-- Prove2me | solution 1 for GlobalTheory.UnitLemma.inf_ker_snd_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:02:47.778534+00:00
-- url     : https://prove2.me/submissions/393b4dbb-9c65-4d76-a972-fa1bde8114ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ComapInlMemStLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardStableLatticesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NcardFibreStableLatticePairProjection
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma
open Polynomial
variable {O E A₁ A₂ : Type} [CommRing O] [Field E] [Algebra O E]
  [CommRing A₁] [CommRing A₂] [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂]
  [IsScalarTower O E A₁] [IsScalarTower O E A₂]
namespace GlobalTheory.UnitLemma
theorem _root_.solution (M : Submodule O (A₁ × A₂)) :
    M ⊓ LinearMap.ker (LinearMap.snd O A₁ A₂) =
      (M.comap (LinearMap.inl O A₁ A₂)).map (LinearMap.inl O A₁ A₂) := by
  ext ⟨a, b⟩
  simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.snd_apply, Submodule.mem_map,
    Submodule.mem_comap, LinearMap.inl_apply]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨a, h, rfl⟩
  · rintro ⟨x, hx, h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hx, rfl⟩
end GlobalTheory.UnitLemma
