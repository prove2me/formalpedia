-- Prove2me | solution 1 for GlobalTheory.PrimeSection.ker_eq_map_of_isPushout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:46:33.352502+00:00
-- url     : https://prove2.me/submissions/e437c4bc-b339-4173-bf70-5b64e01a40e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
namespace GlobalTheory.PrimeSection
theorem _root_.solution {A B C P : CommRingCat.{u}} {α : A ⟶ B} {β : A ⟶ C} {γ : B ⟶ P}
    {δ : C ⟶ P} (h : IsPushout α β γ δ) (hβ : Function.Surjective β) :
    RingHom.ker γ.hom = (RingHom.ker β.hom).map α.hom := by
  refine le_antisymm (fun z hz ↦ ?_) (Ideal.map_le_iff_le_comap.2 fun a ha ↦ ?_)
  · let J := (RingHom.ker β.hom).map α.hom
    have hJ : RingHom.ker β.hom ≤ RingHom.ker ((Ideal.Quotient.mk J).comp α.hom) := fun a ha ↦
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
    let ψ : C →+* B ⧸ J := RingHom.liftOfSurjective β.hom hβ ⟨_, hJ⟩
    have w : α ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) = β ≫ CommRingCat.ofHom ψ := by
      ext a
      exact (RingHom.liftOfSurjective_comp_apply β.hom hβ ⟨_, hJ⟩ a).symm
    have := congrArg (fun φ : B ⟶ CommRingCat.of (B ⧸ J) ↦ φ z) (h.inl_desc _ _ w)
    rw [CommRingCat.comp_apply, show γ z = 0 from hz, map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm
  · have := congrArg (fun φ : A ⟶ P ↦ φ a) h.w
    simp only [CommRingCat.comp_apply] at this
    rw [show β a = 0 from ha, map_zero] at this
    exact this
end GlobalTheory.PrimeSection
