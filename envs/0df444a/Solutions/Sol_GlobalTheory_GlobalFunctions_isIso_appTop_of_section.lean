-- Prove2me | solution 1 for GlobalTheory.GlobalFunctions.isIso_appTop_of_section
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:26:06.456302+00:00
-- url     : https://prove2.me/submissions/bffe9713-5803-4914-8a80-1ca0a51116ef

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Theorems.Thm_GlobalTheory_GlobalFunctions_isIso_appTop_of_cover
import Theorems.Thm_GlobalTheory_ProperFunctions_appLE_top_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.GlobalFunctions
variable {X S T : Scheme.{0}}
namespace GlobalTheory.GlobalFunctions
theorem _root_.solution (hI : FibreInjective) (hD : SmoothDescent) (p : X ⟶ S)
    [IsAffine S] [Smooth p] [IsProper p] [GeometricallyIntegral p] (i : T ⟶ X) [IsAffine T]
    [Smooth i] [Surjective i] (s : S ⟶ T) (hs : s ≫ i ≫ p = 𝟙 S) : IsIso p.appTop := by
  have : IsAffineHom i := IsAffineHom.of_comp i p
  let Z := pullback i i
  have : IsAffine Z := isAffine_of_isAffineHom (pullback.fst i i)
  have h1 : (i ≫ p).appTop.hom.Smooth := by
    rw [← ProperFunctions.appLE_top_top _ le_top]
    exact (i ≫ p).smooth_appLE (isAffineOpen_top _) (isAffineOpen_top _) _
  have h2 : (pullback.fst i i ≫ i ≫ p).appTop.hom.Smooth := by
    rw [← ProperFunctions.appLE_top_top _ le_top]
    exact (pullback.fst i i ≫ i ≫ p).smooth_appLE (isAffineOpen_top _) (isAffineOpen_top _) _
  algebraize [(i ≫ p).appTop.hom, (pullback.fst i i ≫ i ≫ p).appTop.hom]
  let f : Γ(T, ⊤) →ₐ[Γ(S, ⊤)] Γ(Z, ⊤) :=
    { (pullback.fst i i).appTop.hom with
      commutes' := fun c ↦ congr($(Scheme.Hom.comp_appTop (pullback.fst i i) (i ≫ p)) c).symm }
  let g : Γ(T, ⊤) →ₐ[Γ(S, ⊤)] Γ(Z, ⊤) :=
    { (pullback.snd i i).appTop.hom with
      commutes' := fun c ↦ by
        have h := Scheme.Hom.comp_appTop (pullback.snd i i) (i ≫ p)
        rw [← pullback.condition_assoc] at h
        exact congr($h c).symm }
  let r : Γ(T, ⊤) →ₐ[Γ(S, ⊤)] Γ(S, ⊤) :=
    { s.appTop.hom with
      commutes' := fun c ↦ by
        have h := Scheme.Hom.comp_appTop s (i ≫ p)
        rw [hs, Scheme.Hom.id_appTop] at h
        exact congr($h c).symm }
  have : GeometricallyIntegral (p ≫ S.isoSpec.hom) :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral)
      (IsPullback.of_horiz_isIso (fst := 𝟙 X) (f := p) (g := S.isoSpec.inv) ⟨by simp⟩) ‹_›
  have H : IsPullback (Spec.map (pullback.fst i i).appTop) (Spec.map (pullback.snd i i).appTop)
      (T.isoSpec.inv ≫ i) (T.isoSpec.inv ≫ i) :=
    (IsPullback.of_hasPullback i i).of_iso Z.isoSpec T.isoSpec T.isoSpec (.refl _)
      (Scheme.isoSpec_hom_naturality _).symm (Scheme.isoSpec_hom_naturality _).symm
      (by simp) (by simp)
  have hφ : (T.isoSpec.inv ≫ i) ≫ p ≫ S.isoSpec.hom = Spec.map (i ≫ p).appTop := by
    rw [Category.assoc, Iso.inv_comp_eq, Scheme.isoSpec_hom_naturality, Category.assoc]
  have := isIso_appTop_of_cover hI hD (R := Γ(S, ⊤)) (p ≫ S.isoSpec.hom) (T.isoSpec.inv ≫ i)
    f g H hφ r
  rw [Scheme.Hom.comp_appTop] at this
  have : IsIso S.isoSpec.hom.appTop := inferInstanceAs (IsIso (S.isoSpec.hom.app ⊤))
  exact IsIso.of_isIso_comp_left S.isoSpec.hom.appTop p.appTop
end GlobalTheory.GlobalFunctions
