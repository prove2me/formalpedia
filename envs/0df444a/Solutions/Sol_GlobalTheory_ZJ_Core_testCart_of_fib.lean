-- Prove2me | solution 1 for GlobalTheory.ZJ.Core.testCart_of_fib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:58:38.85783+00:00
-- url     : https://prove2.me/submissions/9a7571f9-3f4b-4dd2-b46a-7ab4c3c7561d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TestCartOfSpecialFibreSurjective
import Theorems.Thm_GlobalTheory_ZJ_surjective_of_isClosedImmersion_of_points
import Theorems.Thm_GlobalTheory_ZJ_isIso_of_genericFibre_of_specialFibre
import Theorems.Thm_GlobalTheory_ZJ_isPullback_of_comp_mono
import Theorems.Thm_GlobalTheory_ZJ_isAlgClosed_residueField_OO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.ZJ
namespace GlobalTheory.ZJ
namespace Core
theorem _root_.solution :
    ∀ C : Core, C.Fib → SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart := by
  intro C hF hS p _ y τ
  have := isAlgClosed_residueField_OO p
  have := C.proper
  have := τ.smooth
  have := τ.sep
  have := τ.qc
  have := τ.j_loc
  have : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have : Smooth τ.H.hom := SmoothOfRelativeDimension.smooth C.g _
  have : IsSeparated C.GG.hom := inferInstanceAs (IsSeparated (C.G.ι ≫ C.P.hom))
  let K := FractionRing τ.V
  let t : Sp K ⟶ Sp τ.V := spMap (algebraMap τ.V K)
  let q : Sp (kb p) ⟶ Sp τ.V := rPt p ≫ spMap τ.j
  have hqy : q ≫ τ.y₀ = rPt p ≫ y := by rw [Category.assoc, τ.fac]
  let h : τ.H.left ⟶ pullback C.GG.hom τ.y₀ := pullback.lift τ.f τ.H.hom τ.f_over
  have h₁ : h ≫ pullback.fst _ _ = τ.f := pullback.lift_fst _ _ _
  have h₂ : h ≫ pullback.snd _ _ = τ.H.hom := pullback.lift_snd _ _ _

  have hA : IsPullback C.a C.A.hom C.GG.hom C.U.ι :=
    isPullback_of_comp_mono C.cart
  have hφ : IsPullback τ.φ (pullback.snd τ.H.hom t) C.A.hom τ.yK := τ.φ_cart.1
  have := C.ab.geomConnected
  have : ConnectedSpace ↥(pullback τ.H.hom t) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ hφ
  have hK : IsPullback (pullback.fst τ.H.hom t ≫ h) (pullback.snd τ.H.hom t) (pullback.snd C.GG.hom τ.y₀) t := by
    refine IsPullback.of_right ?_ (by rw [Category.assoc, h₂, pullback.condition])
      (IsPullback.of_hasPullback C.GG.hom τ.y₀)
    have := hφ.paste_horiz hA
    rw [τ.φ_f, τ.yK_fac] at this
    rw [Category.assoc, h₁]
    exact this

  let h' : pullback τ.H.hom q ⟶ pullback C.GG.hom (rPt p ≫ y) :=
    pullback.lift (pullback.fst _ _ ≫ τ.f) (pullback.snd _ _) (by
      rw [Category.assoc, τ.f_over, pullback.condition_assoc, hqy])
  have h₁' : h' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f := pullback.lift_fst _ _ _
  have h₂' : h' ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have : IsClosedImmersion h' := τ.imm h' h₁' h₂'
  let b : pullback C.GG.hom (rPt p ≫ y) ⟶ pullback C.GG.hom τ.y₀ :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ q) (by
      rw [Category.assoc, hqy, pullback.condition])
  have b₁ : b ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have b₂ : b ≫ pullback.snd _ _ = pullback.snd _ _ ≫ q := pullback.lift_snd _ _ _
  have hX : IsPullback b (pullback.snd _ _) (pullback.snd C.GG.hom τ.y₀) q := by
    refine IsPullback.of_right ?_ b₂ (IsPullback.of_hasPullback C.GG.hom τ.y₀)
    rw [b₁, hqy]
    exact .of_hasPullback _ _
  have hsurj : Function.Surjective h' := by
    refine surjective_of_isClosedImmersion_of_points h' (pullback.snd _ _) fun x hx ↦ ?_
    obtain ⟨c, hc₁, hc₂⟩ := hF p y τ (x ≫ pullback.fst _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hx, Category.id_comp])
    refine ⟨pullback.lift c (𝟙 _) (by rw [Category.id_comp]; exact hc₁), pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc, h₁', pullback.lift_fst_assoc, hc₂]
    · rw [Category.assoc, h₂', pullback.lift_snd, hx]
  have hq : IsLocalRing.closedPoint τ.V ∈ Set.range q := by
    refine ⟨IsLocalRing.closedPoint (kb p), ?_⟩
    exact IsLocalRing.comap_closedPoint ((IsLocalRing.residue (OO p)).comp τ.j)
  have : IsIso h := isIso_of_genericFibre_of_specialFibre τ.V K h (pullback.snd _ _) τ.H.hom h₂ hK hq hX
    (a := pullback.fst _ _) (h' := h') (by rw [h₂']; exact .of_hasPullback _ _)
    (pullback.hom_ext (by simp only [Category.assoc, h₁, b₁, h₁'])
      (by simp only [Category.assoc, h₂, b₂, reassoc_of% h₂', pullback.condition]))
    ⟨h'.isClosedEmbedding.injective, hsurj⟩
  exact IsPullback.of_iso_pullback ⟨τ.f_over⟩ (asIso h) h₁ h₂
end Core
end GlobalTheory.ZJ
