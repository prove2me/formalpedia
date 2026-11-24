-- Prove2me | solution 1 for GlobalTheory.Retract.of_hasRingHomProperty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:34:16.341801+00:00
-- url     : https://prove2.me/submissions/0281cc99-74f4-4252-bbaf-7c1d6d0e4570

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Theorems.Thm_GlobalTheory_Retract_exists_affine_le
import Theorems.Thm_GlobalTheory_Retract_exists_algHom_retract
import Theorems.Thm_GlobalTheory_Retract_exists_baseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory GlobalTheory.Retract
variable {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {i : X ⟶ Y} {r : Y ⟶ X}
namespace GlobalTheory.Retract
theorem _root_.solution (P : MorphismProperty Scheme.{u})
    {Q : ∀ {R A : Type u} [CommRing R] [CommRing A], (R →+* A) → Prop} [HasRingHomProperty P Q]
    (hQ : ∀ {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
      (s : A →ₐ[R] B) (p : B →ₐ[R] A), p.comp s = AlgHom.id R A →
        Q (algebraMap R B) → Q (algebraMap R A))
    (hir : i ≫ r = 𝟙 X) (hr : r ≫ f = g) (hg : P g) : P f := by
  wlog hS : IsAffine S generalizing X Y S
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P) S.affineCover]
    intro j
    obtain ⟨i', r', h₁, h₂, -, -⟩ := exists_baseChange hir hr
      (IsPullback.of_hasPullback f (S.affineCover.f j))
      (IsPullback.of_hasPullback g (S.affineCover.f j))
    exact this h₁ h₂ (IsZariskiLocalAtTarget.of_isPullback (.of_hasPullback _ _) hg) inferInstance
  choose U V hU hV hxU _ hUV hVU using fun x ↦ exists_affine_le hir x ⊤ trivial
  refine HasRingHomProperty.of_iSup_eq_top (fun x ↦ ⟨U x, hU x⟩) ?_ fun x ↦ ?_
  · exact eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxU x⟩
  · obtain ⟨s, p, -, -, h⟩ := exists_algHom_retract hir hr (W := ⊤) (hUV x) (hVU x) le_top le_top
    letI := (f.appLE ⊤ (U x) le_top).hom.toAlgebra
    letI := (g.appLE ⊤ (V x) le_top).hom.toAlgebra
    exact hQ s p h (HasRingHomProperty.appLE P g hg ⟨⊤, isAffineOpen_top S⟩ ⟨V x, hV x⟩ le_top)
end GlobalTheory.Retract
