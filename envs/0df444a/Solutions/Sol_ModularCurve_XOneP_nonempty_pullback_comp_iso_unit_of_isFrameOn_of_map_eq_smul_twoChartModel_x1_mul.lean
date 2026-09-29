-- Prove2me | solution 1 for ModularCurve.XOneP.nonempty_pullback_comp_iso_unit_of_isFrameOn_of_map_eq_smul_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/252d5f15-66f1-512e-86eb-0a998f5c181c

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_iso_tensorUnit_of_map_eq_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_nonempty_pullback_comp_iso_unit_of_isFrameOn_of_map_eq_smul_twoChartModel_x1_mul
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve"
open MvPolynomial

namespace CTKit
universe uu
variable {C X U M : Scheme.{uu}} (g : C ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι] (f : U ⟶ M)

noncomputable def Ψ (W : M.Opens) : Γ(M, W) →+* Γ(C, g ⁻¹ᵁ (ι ''ᵁ (f ⁻¹ᵁ W))) :=
  (g.app (ι ''ᵁ (f ⁻¹ᵁ W))).hom.comp (((ι.appIso (f ⁻¹ᵁ W)).inv).hom.comp (f.app W).hom)

theorem Ψ_apply (W : M.Opens) (s : Γ(M, W)) : Ψ g ι f W s = g.app _ ((ι.appIso (f ⁻¹ᵁ W)).inv (f.app W s)) := rfl

theorem le_of_le {W W' : M.Opens} (h : W' ≤ W) : g ⁻¹ᵁ (ι ''ᵁ (f ⁻¹ᵁ W')) ≤ g ⁻¹ᵁ (ι ''ᵁ (f ⁻¹ᵁ W)) :=
  g.preimage_mono (ι.image_mono (f.preimage_mono h))

theorem Ψ_res {W W' : M.Opens} (h : W' ≤ W) (s : Γ(M, W)) :
    Ψ g ι f W' (M.presheaf.map (homOfLE h).op s) = C.presheaf.map (homOfLE (le_of_le g ι f h)).op (Ψ g ι f W s) := by
  rw [Ψ_apply, Ψ_apply]
  have e1 : f.app W' (M.presheaf.map (homOfLE h).op s) = U.presheaf.map (homOfLE (f.preimage_mono h)).op (f.app W s) := by
    show (M.presheaf.map (homOfLE h).op ≫ f.app W') s = _
    rw [Scheme.Hom.naturality]; rfl
  have e2 : (ι.appIso (f ⁻¹ᵁ W')).inv (U.presheaf.map (homOfLE (f.preimage_mono h)).op (f.app W s)) =
      X.presheaf.map (homOfLE (ι.image_mono (f.preimage_mono h))).op ((ι.appIso (f ⁻¹ᵁ W)).inv (f.app W s)) := by
    show (U.presheaf.map (homOfLE (f.preimage_mono h)).op ≫ (ι.appIso (f ⁻¹ᵁ W')).inv) _ = _
    rw [Scheme.Hom.appIso_inv_naturality]
    rfl
  have e3 : ∀ y, g.app (ι ''ᵁ (f ⁻¹ᵁ W')) (X.presheaf.map (homOfLE (ι.image_mono (f.preimage_mono h))).op y) =
      C.presheaf.map (homOfLE (le_of_le g ι f h)).op (g.app (ι ''ᵁ (f ⁻¹ᵁ W)) y) := fun y => by
    show (X.presheaf.map (homOfLE (ι.image_mono (f.preimage_mono h))).op ≫ g.app _) y = _
    rw [Scheme.Hom.naturality]; rfl
  rw [e1, e2, e3]

theorem Ψ_top_of_app_top (y : Γ(X, ⊤)) (s : Γ(M, ⊤)) (hs : f.app ⊤ s = ι.appTop y) :
    Ψ g ι f ⊤ s = C.presheaf.map (homOfLE (le_top : g ⁻¹ᵁ (ι ''ᵁ (f ⁻¹ᵁ ⊤)) ≤ ⊤)).op (g.appTop y) := by
  rw [Ψ_apply, hs]
  have e2 : (ι.appIso (f ⁻¹ᵁ ⊤)).inv (ι.appTop y) = X.presheaf.map (homOfLE (ι.image_le_opensRange _ |>.trans le_top)).op y := by
    show (ι.app ⊤ ≫ (ι.appIso (ι ⁻¹ᵁ ⊤)).inv) y = _
    rw [Scheme.Hom.app_appIso_inv]
    rfl
  rw [e2]
  show (X.presheaf.map _ ≫ g.app _) y = _
  rw [Scheme.Hom.naturality]
  rfl

theorem appTop_SpecMap {R S : CommRingCat.{uu}} (ψ : R ⟶ S) (r : R) :
    (Spec.map ψ).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (ψ r) := by
  have h := Scheme.ΓSpecIso_inv_naturality ψ
  calc (Spec.map ψ).appTop ((Scheme.ΓSpecIso R).inv r) = ((Scheme.ΓSpecIso R).inv ≫ (Spec.map ψ).appTop) r := rfl
    _ = (ψ ≫ (Scheme.ΓSpecIso S).inv) r := by rw [h]
    _ = (Scheme.ΓSpecIso S).inv (ψ r) := rfl

end CTKit

namespace PsiLight

universe v

theorem psi_values {C X U M : Scheme.{v}} (g : C ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι] (f : U ⟶ M)
    {A Q : Type*} [CommRing A] [CommRing Q] [Algebra A Q]
    (φ : Q →+* Γ(M, ⊤)) (χ : A →+* Γ(C, ⊤))
    (hΨc : ∀ z : A, CTKit.Ψ g ι f ⊤ (φ (algebraMap A Q z)) =
      C.presheaf.map (homOfLE (le_top : g ⁻¹ᵁ (ι ''ᵁ (f ⁻¹ᵁ ⊤)) ≤ ⊤)).op (χ z))
    (uQ vQ : Q) (x' y' w : A) (hx0 : χ x' = 0) (hy0 : χ y' = 0) :
    CTKit.Ψ g ι f ⊤ (φ (uQ - algebraMap A Q x')) = CTKit.Ψ g ι f ⊤ (φ uQ) ∧
    CTKit.Ψ g ι f ⊤ (φ (uQ - algebraMap A Q (w * x'))) = CTKit.Ψ g ι f ⊤ (φ uQ) ∧
    CTKit.Ψ g ι f ⊤ (φ (algebraMap A Q y' - vQ)) = -CTKit.Ψ g ι f ⊤ (φ vQ) ∧
    CTKit.Ψ g ι f ⊤ (φ (algebraMap A Q y' - algebraMap A Q w * vQ)) =
      -(C.presheaf.map (homOfLE (le_top : g ⁻¹ᵁ (ι ''ᵁ (f ⁻¹ᵁ ⊤)) ≤ ⊤)).op (χ w) * CTKit.Ψ g ι f ⊤ (φ vQ)) := by
  have hwx0 : χ (w * x') = 0 := by rw [map_mul, hx0, mul_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [map_sub, map_sub, hΨc, hx0, map_zero, sub_zero]
  · rw [map_sub, map_sub, hΨc, hwx0, map_zero, sub_zero]
  · rw [map_sub, map_sub, hΨc, hy0, map_zero, zero_sub]
  · rw [map_sub, map_mul, map_sub, map_mul, hΨc, hΨc, hy0, map_zero, zero_sub]

theorem comp_key {C X U M : Scheme.{v}} (g : C ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι] (f : U ⟶ M)
    (a b aw bw uM vM : Γ(M, ⊤)) (cw : Γ(C, ⊤)) (gM : Γ(M, M.basicOpen a ⊔ M.basicOpen b))
    (hga : M.presheaf.map (homOfLE (le_sup_left : M.basicOpen a ≤ M.basicOpen a ⊔ M.basicOpen b)).op gM *
        M.presheaf.map (homOfLE (le_top : M.basicOpen a ≤ ⊤)).op a = M.presheaf.map (homOfLE (le_top : M.basicOpen a ≤ ⊤)).op aw)
    (hgb : M.presheaf.map (homOfLE (le_sup_right : M.basicOpen b ≤ M.basicOpen a ⊔ M.basicOpen b)).op gM *
        M.presheaf.map (homOfLE (le_top : M.basicOpen b ≤ ⊤)).op b = M.presheaf.map (homOfLE (le_top : M.basicOpen b ≤ ⊤)).op bw)
    (hΨa : CTKit.Ψ g ι f ⊤ a = CTKit.Ψ g ι f ⊤ uM) (hΨaw : CTKit.Ψ g ι f ⊤ aw = CTKit.Ψ g ι f ⊤ uM)
    (hΨb : CTKit.Ψ g ι f ⊤ b = -CTKit.Ψ g ι f ⊤ vM)
    (hΨbw : CTKit.Ψ g ι f ⊤ bw = -(C.presheaf.map (homOfLE (le_top : g ⁻¹ᵁ (ι ''ᵁ (f ⁻¹ᵁ ⊤)) ≤ ⊤)).op cw * CTKit.Ψ g ι f ⊤ vM)) :
    (∀ (V : C.Opens) (hV : V ≤ g ⁻¹ᵁ (ι ''ᵁ (f ⁻¹ᵁ (M.basicOpen a)))),
      C.presheaf.map (homOfLE (hV.trans (CTKit.le_of_le g ι f (le_sup_left : M.basicOpen a ≤ M.basicOpen a ⊔ M.basicOpen b)))).op
        (CTKit.Ψ g ι f (M.basicOpen a ⊔ M.basicOpen b) gM) = 1) ∧
    (∀ (V : C.Opens) (hV : V ≤ g ⁻¹ᵁ (ι ''ᵁ (f ⁻¹ᵁ (M.basicOpen b)))),
      C.presheaf.map (homOfLE (hV.trans (CTKit.le_of_le g ι f (le_sup_right : M.basicOpen b ≤ M.basicOpen a ⊔ M.basicOpen b)))).op
        (CTKit.Ψ g ι f (M.basicOpen a ⊔ M.basicOpen b) gM) =
      C.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op cw) := by
  have rr : ∀ {V₁ V₂ V₃ : C.Opens} (h₁₂ : V₁ ≤ V₂) (h₂₃ : V₂ ≤ V₃) (x : Γ(C, V₃)),
      C.presheaf.map (homOfLE h₁₂).op (C.presheaf.map (homOfLE h₂₃).op x) =
        C.presheaf.map (homOfLE (h₁₂.trans h₂₃)).op x := by
    intros; rw [← CategoryTheory.comp_apply, ← Functor.map_comp]; rfl

  have eqa := congrArg (CTKit.Ψ g ι f (M.basicOpen a)) hga
  rw [RingHom.map_mul, CTKit.Ψ_res g ι f (le_sup_left : M.basicOpen a ≤ M.basicOpen a ⊔ M.basicOpen b) gM,
    CTKit.Ψ_res g ι f (le_top : M.basicOpen a ≤ ⊤) a, CTKit.Ψ_res g ι f (le_top : M.basicOpen a ≤ ⊤) aw, hΨa, hΨaw] at eqa
  have hua : IsUnit (CTKit.Ψ g ι f (M.basicOpen a) (M.presheaf.map (homOfLE (le_top : M.basicOpen a ≤ ⊤)).op a)) :=
    (RingedSpace.isUnit_res_basicOpen _ a).map _
  rw [CTKit.Ψ_res g ι f (le_top : M.basicOpen a ≤ ⊤) a, hΨa] at hua
  have hGa := hua.mul_right_cancel (eqa.trans (one_mul _).symm)

  have eqb := congrArg (CTKit.Ψ g ι f (M.basicOpen b)) hgb
  rw [RingHom.map_mul, CTKit.Ψ_res g ι f (le_sup_right : M.basicOpen b ≤ M.basicOpen a ⊔ M.basicOpen b) gM,
    CTKit.Ψ_res g ι f (le_top : M.basicOpen b ≤ ⊤) b, CTKit.Ψ_res g ι f (le_top : M.basicOpen b ≤ ⊤) bw, hΨb, hΨbw] at eqb
  have hub : IsUnit (CTKit.Ψ g ι f (M.basicOpen b) (M.presheaf.map (homOfLE (le_top : M.basicOpen b ≤ ⊤)).op b)) :=
    (RingedSpace.isUnit_res_basicOpen _ b).map _
  rw [CTKit.Ψ_res g ι f (le_top : M.basicOpen b ≤ ⊤) b, hΨb] at hub
  rw [RingHom.map_neg, RingHom.map_neg, RingHom.map_mul, mul_neg, neg_inj, rr] at eqb
  rw [RingHom.map_neg, IsUnit.neg_iff] at hub
  have hGb := hub.mul_right_cancel eqb
  refine ⟨fun V hV => ?_, fun V hV => ?_⟩
  · rw [← rr hV (CTKit.le_of_le g ι f (le_sup_left : M.basicOpen a ≤ M.basicOpen a ⊔ M.basicOpen b)), hGa, map_one]
  · rw [← rr hV (CTKit.le_of_le g ι f (le_sup_right : M.basicOpen b ≤ M.basicOpen a ⊔ M.basicOpen b)), hGb, rr]

theorem app_overlap_eq {C X U M : Scheme.{v}} (g : C ⟶ X) (ι : U ⟶ X) [IsOpenImmersion ι] (f : U ⟶ M)
    (W O : M.Opens) (hOW : O ≤ W) (s : Γ(M, W)) (V : X.Opens) (hle : V ≤ ι ''ᵁ (f ⁻¹ᵁ O)) :
    g.app V (X.presheaf.map (homOfLE hle).op ((ι.appIso (f ⁻¹ᵁ O)).inv (f.app O (M.presheaf.map (homOfLE hOW).op s)))) =
      C.presheaf.map (homOfLE ((g.preimage_mono hle).trans (CTKit.le_of_le g ι f hOW))).op (CTKit.Ψ g ι f W s) := by
  have rrY : ∀ {V₁ V₂ V₃ : C.Opens} (h₁₂ : V₁ ≤ V₂) (h₂₃ : V₂ ≤ V₃) (x : Γ(C, V₃)),
      C.presheaf.map (homOfLE h₁₂).op (C.presheaf.map (homOfLE h₂₃).op x) =
        C.presheaf.map (homOfLE (h₁₂.trans h₂₃)).op x := by
    intros; rw [← CategoryTheory.comp_apply, ← Functor.map_comp]; rfl
  have h1 : g.app V (X.presheaf.map (homOfLE hle).op ((ι.appIso (f ⁻¹ᵁ O)).inv (f.app O (M.presheaf.map (homOfLE hOW).op s)))) =
      C.presheaf.map (homOfLE (g.preimage_mono hle)).op (CTKit.Ψ g ι f O (M.presheaf.map (homOfLE hOW).op s)) := by
    show (X.presheaf.map (homOfLE hle).op ≫ g.app V) _ = _
    rw [Scheme.Hom.naturality]
    rfl
  rw [h1, CTKit.Ψ_res g ι f hOW s]
  exact rrY _ _ _

end PsiLight

theorem comp_main {Pl k : Type} [CommRing Pl] [IsLocalRing Pl] [Field k]
    (πk : Pl →+* k) (hπk : Function.Surjective πk)
    {X Ci : Scheme.{0}} (sX : X ⟶ Spec (CommRingCat.of Pl)) (gi : Ci ⟶ X)
    (cκ : Ci ⟶ Spec (CommRingCat.of k)) (hgi_snd : gi ≫ sX = cκ ≫ Spec.map (CommRingCat.ofHom πk))
    (i : Fin 2) (tt : Pl)
    (U : X.Opens) (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme tt)
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap Pl (CrossingQuotient Pl tt))) = U.ι ≫ sX)
    (hor : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range gi.base →
      (if i = 0 then CrossingQuotient.V tt else CrossingQuotient.U tt) ∈ (f.base y).asIdeal)
    (x' y' : Pl) (hx' : x' ∈ IsLocalRing.maximalIdeal Pl) (hy' : y' ∈ IsLocalRing.maximalIdeal Pl) (w : Plˣ) :
    letI Q := CrossingQuotient Pl tt
    letI Mdl : Scheme.{0} := CrossingQuotient.crossingScheme tt
    letI φ : Q →+* Γ(Mdl, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
    letI a : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap Pl Q x')
    letI b : Γ(Mdl, ⊤) := φ (algebraMap Pl Q y' - CrossingQuotient.V _)
    letI aw : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap Pl Q ((w : Pl) * x'))
    letI bw : Γ(Mdl, ⊤) := φ (algebraMap Pl Q y' - algebraMap Pl Q (w : Pl) * CrossingQuotient.V _)
    letI O : Mdl.Opens := (Mdl.basicOpen a ⊔ Mdl.basicOpen b) ⊓ (Mdl.basicOpen aw ⊔ Mdl.basicOpen bw)
    ∀ (gM : Γ(Mdl, Mdl.basicOpen a ⊔ Mdl.basicOpen b)),
      Mdl.presheaf.map (homOfLE (le_sup_left : Mdl.basicOpen a ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM *
          Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen a ≤ ⊤)).op a =
        Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen a ≤ ⊤)).op aw →
      Mdl.presheaf.map (homOfLE (le_sup_right : Mdl.basicOpen b ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM *
          Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen b ≤ ⊤)).op b =
        Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen b ≤ ⊤)).op bw →
    ∀ (W₂ W₃ : X.Opens), W₂ ⊔ W₃ = ⊤ → W₂ ≤ U → ∀ (hle : W₂ ⊓ W₃ ≤ U.ι ''ᵁ (f ⁻¹ᵁ O)),
    letI t : Γ(X, W₂ ⊓ W₃) := X.presheaf.map (homOfLE hle).op
      ((U.ι.appIso (f ⁻¹ᵁ O)).inv (f.app O (Mdl.presheaf.map (homOfLE (inf_le_left : O ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM)))
    ∀ (L : X.Modules) (aL : Γ(L, W₂)) (bL : Γ(L, W₃)),
      Scheme.Modules.IsFrameOn aL W₂ → Scheme.Modules.IsFrameOn bL W₃ →
      L.presheaf.map (homOfLE (inf_le_right : W₂ ⊓ W₃ ≤ W₃)).op bL =
        t • L.presheaf.map (homOfLE (inf_le_left : W₂ ⊓ W₃ ≤ W₂)).op aL →
      Nonempty ((Scheme.Modules.pullback gi).obj L ≅ 𝟙_ Ci.Modules) := by
  classical
  intro gM hga hgb W₂ W₃ hcov hW₂U hle L aL bL haL hbL htr

  let Q := CrossingQuotient Pl tt
  let Mdl : Scheme.{0} := CrossingQuotient.crossingScheme tt
  let φ : Q →+* Γ(Mdl, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
  let a : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap Pl Q x')
  let b : Γ(Mdl, ⊤) := φ (algebraMap Pl Q y' - CrossingQuotient.V _)
  let aw : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap Pl Q ((w : Pl) * x'))
  let bw : Γ(Mdl, ⊤) := φ (algebraMap Pl Q y' - algebraMap Pl Q (w : Pl) * CrossingQuotient.V _)
  let O : Mdl.Opens := (Mdl.basicOpen a ⊔ Mdl.basicOpen b) ⊓ (Mdl.basicOpen aw ⊔ Mdl.basicOpen bw)
  let gO : Γ(Mdl, O) := Mdl.presheaf.map (homOfLE (inf_le_left : O ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM
  let t : Γ(X, W₂ ⊓ W₃) := X.presheaf.map (homOfLE hle).op ((U.ι.appIso (f ⁻¹ᵁ O)).inv (f.app O gO))

  let cst : k →+* Γ(Ci, ⊤) := cκ.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (k))).inv.hom

  let κi : k := if i = 0 then 1 else πk (w : Pl)
  have hκi : IsUnit κi := by
    by_cases hi : i = 0
    · simp only [κi, if_pos hi]; exact isUnit_one
    · simp only [κi, if_neg hi]; exact (Units.isUnit w).map _

  have key : gi.app (W₂ ⊓ W₃) t = Ci.presheaf.map (homOfLE (le_top : gi ⁻¹ᵁ (W₂ ⊓ W₃) ≤ ⊤)).op (cst κi) := by

    let sM : Mdl ⟶ Spec (CommRingCat.of Pl) := Spec.map (CommRingCat.ofHom (algebraMap Pl Q))
    have hφalg : ∀ z : Pl, φ (algebraMap Pl Q z) = sM.appTop ((Scheme.ΓSpecIso (CommRingCat.of Pl)).inv z) :=
      fun z => (CTKit.appTop_SpecMap (CommRingCat.ofHom (algebraMap Pl Q)) z).symm
    have hfconst : ∀ z : Pl, f.app ⊤ (φ (algebraMap Pl Q z)) =
        U.ι.appTop (sX.appTop ((Scheme.ΓSpecIso (CommRingCat.of Pl)).inv z)) := by
      intro z
      rw [hφalg]
      show (f ≫ sM).appTop _ = (U.ι ≫ sX).appTop _
      rw [hf]
    have hΨc : ∀ z : Pl, CTKit.Ψ gi U.ι f ⊤ (φ (algebraMap Pl Q z)) =
        Ci.presheaf.map (homOfLE (le_top : gi ⁻¹ᵁ (U.ι ''ᵁ (f ⁻¹ᵁ ⊤)) ≤ ⊤)).op (cst (πk z)) := by
      intro z
      rw [CTKit.Ψ_top_of_app_top gi U.ι f _ _ (hfconst z)]
      congr 1
      show (gi ≫ sX).appTop _ = cκ.appTop ((Scheme.ΓSpecIso _).inv (πk z))
      rw [hgi_snd]
      show cκ.appTop ((Spec.map (CommRingCat.ofHom (πk))).appTop _) = _
      rw [CTKit.appTop_SpecMap]
      rfl

    have hker : RingHom.ker πk = IsLocalRing.maximalIdeal Pl :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective πk hπk)
    have hx0 : πk x' = 0 := by rw [← RingHom.mem_ker, hker]; exact hx'
    have hy0 : πk y' = 0 := by rw [← RingHom.mem_ker, hker]; exact hy'

    obtain ⟨hΨa, hΨaw, hΨb, hΨbw⟩ := PsiLight.psi_values gi U.ι f φ (cst.comp (πk)) hΨc
      (CrossingQuotient.U _) (CrossingQuotient.V _) x' y' (w : Pl)
      (by show cst (πk x') = 0; rw [hx0, map_zero])
      (by show cst (πk y') = 0; rw [hy0, map_zero])
    obtain ⟨hGa, hGb⟩ := PsiLight.comp_key gi U.ι f a b aw bw _ _ _ gM hga hgb hΨa hΨaw hΨb hΨbw
    have hG := PsiLight.app_overlap_eq gi U.ι f (Mdl.basicOpen a ⊔ Mdl.basicOpen b) O inf_le_left gM (W₂ ⊓ W₃) hle

    have hmax : ∀ (z : Ci) (y : U), U.ι.base y = gi.base z → ∀ m ∈ IsLocalRing.maximalIdeal Pl,
        algebraMap Pl Q m ∈ (f.base y).asIdeal := by
      intro z y hyz m hm
      have h1 : (sM.base (f.base y)).asIdeal = Ideal.comap (algebraMap Pl Q) (f.base y).asIdeal := rfl
      have h2 : sM.base (f.base y) = (Spec.map (CommRingCat.ofHom (πk))).base (cκ.base z) := by
        show (f ≫ sM).base y = (cκ ≫ Spec.map (CommRingCat.ofHom (πk))).base z
        rw [hf, ← hgi_snd, Scheme.Hom.comp_base, Scheme.Hom.comp_base, TopCat.coe_comp, TopCat.coe_comp,
          Function.comp_apply, Function.comp_apply, hyz]
      have h3 : ((Spec.map (CommRingCat.ofHom (πk))).base (cκ.base z)).asIdeal = IsLocalRing.maximalIdeal Pl := by
        show Ideal.comap (πk) (cκ.base z).asIdeal = _
        rw [show (cκ.base z).asIdeal = ⊥ from Ideal.eq_bot_of_prime _, ← RingHom.ker_eq_comap_bot, hker]
      rw [← Ideal.mem_comap, ← h1, h2, h3]
      exact hm

    have hDa : ∀ q : Mdl, q ∈ Mdl.basicOpen a → (CrossingQuotient.U _ - algebraMap Pl Q x') ∉ q.asIdeal := by
      intro q hq
      have : Mdl.basicOpen a = PrimeSpectrum.basicOpen (CrossingQuotient.U _ - algebraMap Pl Q x') :=
        AlgebraicGeometry.basicOpen_eq_of_affine _
      rw [this] at hq
      exact hq
    have hDb : ∀ q : Mdl, q ∈ Mdl.basicOpen b → (algebraMap Pl Q y' - CrossingQuotient.V _) ∉ q.asIdeal := by
      intro q hq
      have : Mdl.basicOpen b = PrimeSpectrum.basicOpen (algebraMap Pl Q y' - CrossingQuotient.V _) :=
        AlgebraicGeometry.basicOpen_eq_of_affine _
      rw [this] at hq
      exact hq

    fin_cases i
    ·
      have hsub : gi ⁻¹ᵁ (U.ι ''ᵁ (f ⁻¹ᵁ O)) ≤ gi ⁻¹ᵁ (U.ι ''ᵁ (f ⁻¹ᵁ Mdl.basicOpen a)) := by
        rintro z ⟨y, hyO, hyz⟩
        refine ⟨y, ?_, hyz⟩
        rcases hyO.1 with hya | hyb
        · exact hya
        · exfalso
          apply hDb _ hyb
          have hV : CrossingQuotient.V tt ∈ (f.base y).asIdeal := by simpa using hor y ⟨z, hyz.symm⟩
          have hy'mem := hmax z y hyz y' hy'
          exact Ideal.sub_mem _ hy'mem hV
      rw [hG]
      refine (hGa _ ((gi.preimage_mono hle).trans hsub)).trans ?_
      simp only [κi, Fin.zero_eta, Fin.isValue, ↓reduceIte, map_one]
    ·
      have hsub : gi ⁻¹ᵁ (U.ι ''ᵁ (f ⁻¹ᵁ O)) ≤ gi ⁻¹ᵁ (U.ι ''ᵁ (f ⁻¹ᵁ Mdl.basicOpen b)) := by
        rintro z ⟨y, hyO, hyz⟩
        refine ⟨y, ?_, hyz⟩
        rcases hyO.1 with hya | hyb
        · exfalso
          apply hDa _ hya
          have hU : CrossingQuotient.U tt ∈ (f.base y).asIdeal := by simpa using hor y ⟨z, hyz.symm⟩
          have hx'mem := hmax z y hyz x' hx'
          exact Ideal.sub_mem _ hU hx'mem
        · exact hyb
      rw [hG]
      refine (hGb _ ((gi.preimage_mono hle).trans hsub)).trans ?_
      simp only [κi, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, RingHom.coe_comp, Function.comp_apply]

  let sU := Scheme.Modules.pullbackLocalSection gi aL
  let sV := Scheme.Modules.pullbackLocalSection gi bL
  have hsU : Scheme.Modules.IsFrameOn sU (gi ⁻¹ᵁ W₂) := haL.pullbackLocalSection gi
  have hsV : Scheme.Modules.IsFrameOn sV (gi ⁻¹ᵁ W₃) := hbL.pullbackLocalSection gi
  have hcov' : gi ⁻¹ᵁ W₂ ⊔ gi ⁻¹ᵁ W₃ = ⊤ := by rw [← Scheme.Hom.preimage_sup, hcov]; rfl

  have htr' : ((Scheme.Modules.pullback gi).obj L).presheaf.map (homOfLE (inf_le_right : gi ⁻¹ᵁ W₂ ⊓ gi ⁻¹ᵁ W₃ ≤ gi ⁻¹ᵁ W₃)).op sV =
      Ci.presheaf.map (homOfLE (le_top : gi ⁻¹ᵁ W₂ ⊓ gi ⁻¹ᵁ W₃ ≤ ⊤)).op (cst κi) •
        ((Scheme.Modules.pullback gi).obj L).presheaf.map (homOfLE (inf_le_left : gi ⁻¹ᵁ W₂ ⊓ gi ⁻¹ᵁ W₃ ≤ gi ⁻¹ᵁ W₂)).op sU := by
    have e1 := Scheme.Modules.map_homOfLE_pullbackLocalSection gi (inf_le_right : W₂ ⊓ W₃ ≤ W₃) bL
    have e2 := Scheme.Modules.map_homOfLE_pullbackLocalSection gi (inf_le_left : W₂ ⊓ W₃ ≤ W₂) aL
    rw [htr, Scheme.Modules.pullbackLocalSection_smul, key, ← e2] at e1
    exact e1
  have hunit : IsUnit (Ci.presheaf.map (homOfLE (le_top : gi ⁻¹ᵁ W₂ ⊓ gi ⁻¹ᵁ W₃ ≤ ⊤)).op (cst κi)) := (hκi.map cst).map _
  obtain ⟨u, hu⟩ := hunit
  refine AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_iso_tensorUnit_of_map_eq_mul hcov' hsU hsV (↑u⁻¹) ?_
    (Ci.presheaf.map (homOfLE (le_top : gi ⁻¹ᵁ W₂ ≤ ⊤)).op (cst (hκi.unit⁻¹ : (k)ˣ)))
    1 (((hκi.unit⁻¹).isUnit.map cst).map _) isUnit_one ?_
  ·
    rw [htr', ← hu, smul_smul, Units.inv_mul, one_smul]
  ·
    rw [map_one, mul_one]
    apply Units.eq_inv_of_mul_eq_one_left
    rw [hu]
    have hh : (Ci.presheaf.map (homOfLE (inf_le_left : gi ⁻¹ᵁ W₂ ⊓ gi ⁻¹ᵁ W₃ ≤ gi ⁻¹ᵁ W₂)).op)
        ((Ci.presheaf.map (homOfLE (le_top : gi ⁻¹ᵁ W₂ ≤ ⊤)).op) (cst ↑hκi.unit⁻¹)) =
        Ci.presheaf.map (homOfLE (le_top : gi ⁻¹ᵁ W₂ ⊓ gi ⁻¹ᵁ W₃ ≤ ⊤)).op (cst ↑hκi.unit⁻¹) := by
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp]; rfl
    erw [hh]
    rw [← map_mul, ← map_mul, IsUnit.mul_val_inv, map_one, map_one]

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : Function.Surjective πk)

    (bc : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom πk))

    (e : ℕ) (he : 1 ≤ e)
    (U : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ))).Opens)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme ((ρ ϖ) ^ e))
    (hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥Pl (CrossingQuotient ↥Pl ((ρ ϖ) ^ e)))) =
      U.ι ≫ pullback.snd _ _)
    (hor₃ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (i₁.1 ≫ bc).base →
      CrossingQuotient.V ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal)
    (hor₄ : ∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (i₂.1 ≫ bc).base →
      CrossingQuotient.U ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal)

    (x' y' : ↥Pl) (hxy : x' * y' = (ρ ϖ) ^ e)
    (hx' : x' ∈ IsLocalRing.maximalIdeal ↥Pl) (hy' : y' ∈ IsLocalRing.maximalIdeal ↥Pl) (w : (↥Pl)ˣ) :
    letI X : Scheme.{0} := pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ))
    letI Q := CrossingQuotient ↥Pl ((ρ ϖ) ^ e)
    letI Mdl : Scheme.{0} := CrossingQuotient.crossingScheme ((ρ ϖ) ^ e)
    letI φ : Q →+* Γ(Mdl, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of Q)).inv.hom
    letI a : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥Pl Q x')
    letI b : Γ(Mdl, ⊤) := φ (algebraMap ↥Pl Q y' - CrossingQuotient.V _)
    letI aw : Γ(Mdl, ⊤) := φ (CrossingQuotient.U _ - algebraMap ↥Pl Q ((w : ↥Pl) * x'))
    letI bw : Γ(Mdl, ⊤) := φ (algebraMap ↥Pl Q y' - algebraMap ↥Pl Q (w : ↥Pl) * CrossingQuotient.V _)
    letI O : Mdl.Opens := (Mdl.basicOpen a ⊔ Mdl.basicOpen b) ⊓ (Mdl.basicOpen aw ⊔ Mdl.basicOpen bw)

    ∀ (gM : Γ(Mdl, Mdl.basicOpen a ⊔ Mdl.basicOpen b)),
      Mdl.presheaf.map (homOfLE (le_sup_left : Mdl.basicOpen a ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM *
          Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen a ≤ ⊤)).op a =
        Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen a ≤ ⊤)).op aw →
      Mdl.presheaf.map (homOfLE (le_sup_right : Mdl.basicOpen b ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM *
          Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen b ≤ ⊤)).op b =
        Mdl.presheaf.map (homOfLE (le_top : Mdl.basicOpen b ≤ ⊤)).op bw →

    ∀ (W₂ W₃ : X.Opens), W₂ ⊔ W₃ = ⊤ → W₂ ≤ U → ∀ (hle : W₂ ⊓ W₃ ≤ U.ι ''ᵁ (f ⁻¹ᵁ O)),
    letI t : Γ(X, W₂ ⊓ W₃) := X.presheaf.map (homOfLE hle).op
      ((U.ι.appIso (f ⁻¹ᵁ O)).inv (f.app O (Mdl.presheaf.map (homOfLE (inf_le_left : O ≤ Mdl.basicOpen a ⊔ Mdl.basicOpen b)).op gM)))

    ∀ (L : X.Modules) (aL : Γ(L, W₂)) (bL : Γ(L, W₃)),
      Scheme.Modules.IsFrameOn aL W₂ → Scheme.Modules.IsFrameOn bL W₃ →
      L.presheaf.map (homOfLE (inf_le_right : W₂ ⊓ W₃ ≤ W₃)).op bL =
        t • L.presheaf.map (homOfLE (inf_le_left : W₂ ⊓ W₃ ≤ W₂)).op aL →
      Nonempty ((Scheme.Modules.pullback (i₁.1 ≫ bc)).obj L ≅ SheafOfModules.unit C₁.ringCatSheaf) ∧
      Nonempty ((Scheme.Modules.pullback (i₂.1 ≫ bc)).obj L ≅ SheafOfModules.unit C₂.ringCatSheaf) := by
  intro gM hga hgb W₂ W₃ hcov hW₂U hle Lm aL bL haL hbL htr
  have hg₁ : (i₁.1 ≫ bc) ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)) = c₁ ≫ Spec.map (CommRingCat.ofHom πk) := by
    rw [Category.assoc, hbc₂, ← Category.assoc, i₁.2]
  have hg₂ : (i₂.1 ≫ bc) ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)) = c₂ ≫ Spec.map (CommRingCat.ofHom πk) := by
    rw [Category.assoc, hbc₂, ← Category.assoc, i₂.2]
  refine ⟨?_, ?_⟩
  · exact comp_main πk hπk (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ))) (i₁.1 ≫ bc) c₁ hg₁ 0 ((ρ ϖ) ^ e)
      U f hf (fun y hy => by simpa using hor₃ y hy) x' y' hx' hy' w gM hga hgb W₂ W₃ hcov hW₂U hle Lm aL bL haL hbL htr
  · exact comp_main πk hπk (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ))) (i₂.1 ≫ bc) c₂ hg₂ 1 ((ρ ϖ) ^ e)
      U f hf (fun y hy => by simpa using hor₄ y hy) x' y' hx' hy' w gM hga hgb W₂ W₃ hcov hW₂U hle Lm aL bL haL hbL htr

end S_ModularCurve_XOneP_nonempty_pullback_comp_iso_unit_of_isFrameOn_of_map_eq_smul_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_nonempty_pullback_comp_iso_unit_of_isFrameOn_of_map_eq_smul_twoChartModel_x1_mul (solution)
