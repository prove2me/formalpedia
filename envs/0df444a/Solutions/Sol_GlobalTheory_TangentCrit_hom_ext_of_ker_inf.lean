-- Prove2me | solution 1 for GlobalTheory.TangentCrit.hom_ext_of_ker_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:11.964159+00:00
-- url     : https://prove2.me/submissions/9680b866-3f32-4fd9-a0a5-4bc21c4832ed

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.TangentCrit
open AlgebraicGeometry CategoryTheory Limits
universe u
namespace GlobalTheory.TangentCrit
theorem _root_.solution {D E₁ E₂ : CommRingCat.{u}} (p₁ : D ⟶ E₁) (p₂ : D ⟶ E₂)
    (hs : Function.Surjective (Spec.map p₁)) (h : ∀ d, p₁ d = 0 → p₂ d = 0 → d = 0)
    {X : Scheme.{u}} {g g' : Spec D ⟶ X} (h₁ : Spec.map p₁ ≫ g = Spec.map p₁ ≫ g')
    (h₂ : Spec.map p₂ ≫ g = Spec.map p₂ ≫ g') : g = g' := by
  have hsurj : Function.Surjective (equalizer.ι g g') := by
    intro y
    obtain ⟨z, rfl⟩ := hs y
    exact ⟨equalizer.lift _ h₁ z, by rw [← Scheme.Hom.comp_apply, equalizer.lift_ι]⟩
  have : IsClosedImmersion (equalizer.ι g g') :=
    .of_isPreimmersion _ (by rw [hsurj.range_eq]; exact isClosed_univ)
  have key : ∀ {E : CommRingCat.{u}} (p : D ⟶ E) (_ : Spec.map p ≫ g = Spec.map p ≫ g')
      (d : Γ(Spec D, ⊤)), (equalizer.ι g g').appTop d = 0 → p ((Scheme.ΓSpecIso D).hom d) = 0 := by
    intro E p hp d hd
    have e : (Spec.map p).appTop d = 0 := by
      rw [← equalizer.lift_ι _ hp, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hd, map_zero]
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply, e, map_zero]
  have : IsIso (equalizer.ι g g') := by
    refine IsClosedImmersion.isIso_of_injective_of_isAffine ((injective_iff_map_eq_zero _).mpr ?_)
    intro d hd
    apply (Scheme.ΓSpecIso D).commRingCatIsoToRingEquiv.injective
    rw [map_zero]
    exact h _ (key p₁ h₁ d hd) (key p₂ h₂ d hd)
  rw [← cancel_epi (equalizer.ι g g'), equalizer.condition]
end GlobalTheory.TangentCrit
