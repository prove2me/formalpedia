-- Prove2me | solution 1 for GlobalTheory.PrimeSection.ker_app_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:06:02.496877+00:00
-- url     : https://prove2.me/submissions/2e151060-3414-4ddd-b33d-8887a214f7fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Theorems.Thm_GlobalTheory_PrimeSection_ker_eq_map_of_isPushout

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
theorem _root_.solution {X Z : Scheme.{u}} {A C : CommRingCat.{u}} {β : A ⟶ C}
    (hβ : Function.Surjective β) {c : A} (hc : RingHom.ker β.hom = Ideal.span {c})
    {f : X ⟶ Spec A} {i : Z ⟶ X} {f' : Z ⟶ Spec C} (h : IsPullback i f' f (Spec.map β))
    {U : X.Opens} (hU : IsAffineOpen U) :
    RingHom.ker (i.app U).hom = Ideal.span {X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
      (f.appTop ((Scheme.ΓSpecIso A).inv c))} := by
  have hpo := (isIso_pushoutSection_iff h (US := ⊤) (UT := ⊤) (UX := U) (UY := i ⁻¹ᵁ U) le_top
    le_top (by simp)).1 (isIso_pushoutSection_of_isAffineOpen h _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have hpo' : IsPushout ((Scheme.ΓSpecIso A).inv ≫ f.appLE ⊤ U le_top) β (i.app U)
      ((Scheme.ΓSpecIso C).inv ≫ f'.appLE ⊤ (i ⁻¹ᵁ U) le_top) := by
    refine hpo.of_iso (Scheme.ΓSpecIso A) (Iso.refl _) (Scheme.ΓSpecIso C) (Iso.refl _)
      (by simp) ?_ (by simp [Scheme.Hom.appLE_eq_app]) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  rw [ker_eq_map_of_isPushout hpo' hβ, hc, Ideal.map_span, Set.image_singleton]
  rfl
end GlobalTheory.PrimeSection
