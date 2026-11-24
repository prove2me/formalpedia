-- Prove2me | solution 1 for GlobalTheory.UnitLemma.ProdCount.isLat_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:59:02.561285+00:00
-- url     : https://prove2.me/submissions/9245bcb2-808a-4a98-94da-04f6c71c9403

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountProdOfIdempotentSeparable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.ProdCount
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial
variable {O : Type} [CommRing O] {A₁ A₂ : Type} [CommRing A₁] [Algebra O A₁] [CommRing A₂] [Algebra O A₂]
namespace GlobalTheory.UnitLemma.ProdCount
theorem _root_.solution (E : Type) [Field E] [Algebra E A₁] [Algebra E A₂] (L₁ : Submodule O A₁) (L₂ : Submodule O A₂) :
    IsLat O E (L₁.prod L₂) ↔ IsLat O E L₁ ∧ IsLat O E L₂ := by
  have hs : Submodule.span E ((L₁.prod L₂ : Submodule O (A₁ × A₂)) : Set (A₁ × A₂)) =
      (Submodule.span E (L₁ : Set A₁)).prod (Submodule.span E (L₂ : Set A₂)) := by
    rw [Submodule.prod_coe]
    exact Submodule.span_prod_eq E L₁.zero_mem L₂.zero_mem
  unfold IsLat
  rw [hs, Submodule.prod_eq_top_iff]
  constructor
  · rintro ⟨h, h1, h2⟩
    have a := h.map (LinearMap.fst O A₁ A₂)
    have b := h.map (LinearMap.snd O A₁ A₂)
    rw [Submodule.prod_map_fst] at a
    rw [Submodule.prod_map_snd] at b
    exact ⟨⟨a, h1⟩, b, h2⟩
  · rintro ⟨⟨a, h1⟩, b, h2⟩
    exact ⟨a.prod b, h1, h2⟩
end GlobalTheory.UnitLemma.ProdCount
