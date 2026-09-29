-- Prove2me | solution 1 for ModularCurve.XOneP.exists_relativeGroupLaw_isClosedImmersion_iff_postComp_pullbackHom_eq_one_splitTorus_specialFibre_baseChange_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/a69eb704-0a20-53e1-9d95-d64ad2b58a57

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOps
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_HopfAlgebra_FVectStructure
import Definitions.Def_HopfAlgebra_RaynaudNormalFormDatum
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_torus_isClosedImmersion_ker_restrictPair_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_SplitTorus_forall_torusPt_mul_of_torusPtId_mul_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_SplitTorus_exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_opens_section_restrictPair_of_twoGluedSmoothCurves
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_relativeGroupLaw_isClosedImmersion_iff_postComp_pullbackHom_eq_one_splitTorus_specialFibre_baseChange_x1_mul
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve"

open AlgebraicGeometry.SplitTorus

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard

namespace KEpi

theorem exists_opens_lift_of_twoGluedSmoothCurves
    {k : Type u} [Field k] [IsAlgClosed k]
    {X C₁ C₂ : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) [IsProper x] (hXred : IsReduced X)
    (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ x) (i₂ : SchemeHomOver c₂ x) [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hjs : ∀ z : X, z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hcr : IsReduced (pullback i₁.1 i₂.1)) (s : ℕ) (hs : Nat.card ↥(pullback i₁.1 i₂.1) = s) (hs0 : 0 < s)
    (ε : SchemeHomOver (𝟙 _) x) (ε₁ : SchemeHomOver (𝟙 _) c₁) (hε : ε₁.1 ≫ i₁.1 = ε.1)
    (ε₂ : SchemeHomOver (𝟙 _) c₂)
    (D : RelativePic0Designation k x) (hD : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (D₁ : RelativePic0Designation k c₁) (hD₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)
    (D₂ : RelativePic0Designation k c₂) (hD₂ : RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂)
    (ν₁ : SchemeHomOver D.toBase D₁.toBase) (ν₂ : SchemeHomOver D.toBase D₂.toBase)
    (hν₁ : ν₁ = RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε hD hD₁)
    (hν₂ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t D.toBase),
        Nonempty ((hD₂.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hD.poincare.pullbackAlong a).L))) :
    ∀ {T' : Scheme.{u}} (t : T' ⟶ Spec (CommRingCat.of k)) (x₁ : SchemeHomOver t D₁.toBase) (x₂ : SchemeHomOver t D₂.toBase)
      (z : T'), ∃ (U : T'.Opens) (_ : z ∈ U) (a : SchemeHomOver (U.ι ≫ t) D.toBase),
        (NeronModelInfra.schemeHomOverComp a ν₁).1 = U.ι ≫ x₁.1 ∧ (NeronModelInfra.schemeHomOverComp a ν₂).1 = U.ι ≫ x₂.1 := by
  intro T' t x₁ x₂ z

  let b : T' ⟶ pullback D₁.toBase D₂.toBase := pullback.lift x₁.1 x₂.1 (x₁.2.trans x₂.2.symm)

  obtain ⟨V, hbV, σ, hσ⟩ :=
    exists_opens_section_restrictPair_of_twoGluedSmoothCurves x hXred c₁ c₂ i₁ i₂ hjs hcr s hs hs0 ε ε₁ hε ε₂ D hD D₁ hD₁ D₂ hD₂
      ν₁ ν₂ hν₁ hν₂ (b.base z)
  have hb1 : b ≫ pullback.fst D₁.toBase D₂.toBase = x₁.1 := pullback.lift_fst _ _ _
  have hb2 : b ≫ pullback.snd D₁.toBase D₂.toBase = x₂.1 := pullback.lift_snd _ _ _

  refine ⟨b ⁻¹ᵁ V, hbV, ⟨(b ∣_ V) ≫ σ, ?_⟩, ?_, ?_⟩
  ·
    have h1 : σ ≫ D.toBase = V.ι ≫ pullback.fst D₁.toBase D₂.toBase ≫ D₁.toBase := by
      rw [← ν₁.2, ← Category.assoc σ ν₁.1, show ν₁.1 = pullback.lift ν₁.1 ν₂.1 (ν₁.2.trans ν₂.2.symm) ≫
        pullback.fst D₁.toBase D₂.toBase from (pullback.lift_fst _ _ _).symm, ← Category.assoc σ, hσ, Category.assoc]
    rw [Category.assoc, h1, ← Category.assoc, morphismRestrict_ι, Category.assoc, ← Category.assoc b, hb1, x₁.2]
  · show ((b ∣_ V) ≫ σ) ≫ ν₁.1 = (b ⁻¹ᵁ V).ι ≫ x₁.1
    have h1 : σ ≫ ν₁.1 = V.ι ≫ pullback.fst D₁.toBase D₂.toBase := by
      rw [show ν₁.1 = pullback.lift ν₁.1 ν₂.1 (ν₁.2.trans ν₂.2.symm) ≫ pullback.fst D₁.toBase D₂.toBase from
        (pullback.lift_fst _ _ _).symm, ← Category.assoc, hσ]
    rw [Category.assoc, h1, ← Category.assoc, morphismRestrict_ι, Category.assoc, hb1]
  · show ((b ∣_ V) ≫ σ) ≫ ν₂.1 = (b ⁻¹ᵁ V).ι ≫ x₂.1
    have h2 : σ ≫ ν₂.1 = V.ι ≫ pullback.snd D₁.toBase D₂.toBase := by
      rw [show ν₂.1 = pullback.lift ν₁.1 ν₂.1 (ν₁.2.trans ν₂.2.symm) ≫ pullback.snd D₁.toBase D₂.toBase from
        (pullback.lift_snd _ _ _).symm, ← Category.assoc, hσ]
    rw [Category.assoc, h2, ← Category.assoc, morphismRestrict_ι, Category.assoc, hb2]

end KEpi

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SplitTorus AlgebraicGeometry.SmoothProperCurve

namespace KTorus

private noncomputable def unitsΓ (R : Type u) [CommRing R] (d : ℕ) :
    (Fin d → Γ(Spec (CommRingCat.of R), ⊤)ˣ) ≃* (Fin d → Rˣ) :=
  MulEquiv.piCongrRight fun _ =>
    Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toMulEquiv

private theorem unitsΓ_apply (R : Type u) [CommRing R] (d : ℕ) (w : Fin d → Γ(Spec (CommRingCat.of R), ⊤)ˣ) (i : Fin d) :
    (unitsΓ R d w i : R) = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (w i : Γ(Spec (CommRingCat.of R), ⊤)) := rfl

private noncomputable def restrictPt (k : Type u) [Field k] (d : ℕ) {R R' : Type u} [CommRing R] [Algebra k R]
    [CommRing R'] [Algebra k R'] (a : R →ₐ[k] R') (x : SchemeHomOver (specMap k R) (torusStr k d)) :
    SchemeHomOver (specMap k R') (torusStr k d) :=
  ⟨Spec.map (CommRingCat.ofHom a.toRingHom) ≫ x.1, by
    rw [Category.assoc, x.2]
    show Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact a.comp_algebraMap⟩

theorem exists_law_and_points (k : Type u) [Field k] (d : ℕ) :
    ∃ (LT : RelativeGroupLaw k (torusStr k d))
      (eT : ∀ (R : Type u) [CommRing R] [Algebra k R], (Fin d → Rˣ) ≃ SchemeHomOver (specMap k R) (torusStr k d)),
      (∀ (R : Type u) [CommRing R] [Algebra k R] (u v : Fin d → Rˣ), eT R (u * v) = LT.mul _ (eT R u) (eT R v)) ∧
      (∀ (R R' : Type u) [CommRing R] [Algebra k R] [CommRing R'] [Algebra k R'] (a : R →ₐ[k] R') (u : Fin d → Rˣ),
        (eT R' (fun i => Units.map a.toRingHom.toMonoidHom (u i))).1 =
          Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (eT R u).1) ∧
      (∀ (S' : Type u) [CommRing S'] [Algebra k S'] (χ χ' : WithConv (torusCoord k d →ₐ[k] S')),
        torusPt k S' d (χ * χ').ofConv = LT.mul _ (torusPt k S' d χ.ofConv) (torusPt k S' d χ'.ofConv)) ∧
      (∀ (S' : Type u) [CommRing S'] [Algebra k S'],
        torusPt k S' d (1 : WithConv (torusCoord k d →ₐ[k] S')).ofConv = LT.one _) := by
  obtain ⟨L, -, hE, hconv, hone, -, -⟩ :=
    AlgebraicGeometry.SplitTorus.exists_relativeGroupLaw_isCommutative_torusPt_convMul_schemeNsmul_eq k d
  choose e hpin hmul using @hE

  let eT : ∀ (R : Type u) [CommRing R] [Algebra k R], (Fin d → Rˣ) ≃ SchemeHomOver (specMap k R) (torusStr k d) :=
    fun R _ _ => ((e (specMap k R)).trans (unitsΓ R d).toEquiv).symm
  have heT : ∀ (R : Type u) [CommRing R] [Algebra k R] (u : Fin d → Rˣ),
      unitsΓ R d (e (specMap k R) (eT R u)) = u := fun R _ _ u =>
    ((e (specMap k R)).trans (unitsΓ R d).toEquiv).apply_symm_apply u
  refine ⟨L, eT, ?_, ?_, hconv, hone⟩
  ·
    intro R _ _ u v
    apply ((e (specMap k R)).trans (unitsΓ R d).toEquiv).injective
    rw [Equiv.apply_symm_apply]
    show u * v = unitsΓ R d (e (specMap k R) (L.mul _ (eT R u) (eT R v)))
    rw [hmul, map_mul, heT, heT]
  ·
    intro R R' _ _ _ _ a u
    suffices h : eT R' (fun i => Units.map a.toRingHom.toMonoidHom (u i)) = restrictPt k d a (eT R u) by
      rw [h]; rfl
    show ((e (specMap k R')).trans (unitsΓ R' d).toEquiv).symm _ = _
    rw [Equiv.symm_apply_eq]
    funext i
    apply Units.ext
    show (Units.map a.toRingHom.toMonoidHom (u i) : R') = (unitsΓ R' d (e (specMap k R') (restrictPt k d a (eT R u))) i : R')
    rw [unitsΓ_apply, hpin, Units.coe_map]

    have key : ((Scheme.ΓSpecIso (CommRingCat.of (torusCoord k d))).inv ≫ (restrictPt k d a (eT R u)).1.appTop).hom
        (AddMonoidAlgebra.single (Pi.single i 1) 1) =
        (Spec.map (CommRingCat.ofHom a.toRingHom)).appTop.hom
          (((Scheme.ΓSpecIso (CommRingCat.of (torusCoord k d))).inv ≫ (eT R u).1.appTop).hom
            (AddMonoidAlgebra.single (Pi.single i 1) 1)) := by
      show ((Scheme.ΓSpecIso (CommRingCat.of (torusCoord k d))).inv ≫
          (Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (eT R u).1).appTop).hom _ = _
      rw [Scheme.Hom.comp_appTop, ← Category.assoc, CategoryTheory.comp_apply]
    rw [key, ← hpin, ← CategoryTheory.comp_apply, Scheme.ΓSpecIso_naturality, CategoryTheory.comp_apply]
    show (a : R → R') (u i) = a.toRingHom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (e (specMap k R) (eT R u) i))
    rw [← unitsΓ_apply, heT]
    rfl

end KTorus

namespace KAsm

theorem exists_eq_torusPt {k : Type} [Field k] (d : ℕ) (R : Type) [CommRing R] [Algebra k R]
    (x : SchemeHomOver (specMap k R) (torusStr k d)) :
    ∃ χ : torusCoord k d →ₐ[k] R, torusPt k R d χ = x := by

  let φ : CommRingCat.of (torusCoord k d) ⟶ CommRingCat.of R := Spec.preimage x.1
  have hφ : Spec.map φ = x.1 := Spec.map_preimage x.1
  have hx := x.2

  have hcomm : (CommRingCat.ofHom (algebraMap k (torusCoord k d))) ≫ φ = CommRingCat.ofHom (algebraMap k R) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ]
    exact hx
  refine ⟨{ φ.hom with commutes' := fun a => ?_ }, ?_⟩
  · have := congrArg (fun f => f.hom a) hcomm
    simpa using this
  · apply Subtype.ext
    change Spec.map (CommRingCat.ofHom _) = x.1
    rw [← hφ]
    rfl

theorem comp_mul_eq_mul_comp_of_forall_torusPt {k : Type} [Field k] (d : ℕ)
    (LT : RelativeGroupLaw k (torusStr k d))
    (hconv : ∀ (S' : Type) [CommRing S'] [Algebra k S'] (χ χ' : WithConv (torusCoord k d →ₐ[k] S')),
        torusPt k S' d (χ * χ').ofConv = LT.mul _ (torusPt k S' d χ.ofConv) (torusPt k S' d χ'.ofConv))
    {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of k)) (L : RelativeGroupLaw k f) (τ : SchemeHomOver (torusStr k d) f)
    (hτ : ∀ (T : Type) [CommRing T] [Algebra k T] (χ χ' : WithConv (torusCoord k d →ₐ[k] T)),
      NeronModelInfra.schemeHomOverComp (torusPt k T d (χ * χ').ofConv) τ =
        L.mul _ (NeronModelInfra.schemeHomOverComp (torusPt k T d χ.ofConv) τ)
          (NeronModelInfra.schemeHomOverComp (torusPt k T d χ'.ofConv) τ))
    {T' : Scheme.{0}} (s : T' ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver s (torusStr k d)) :
    NeronModelInfra.schemeHomOverComp (LT.mul s x y) τ =
      L.mul s (NeronModelInfra.schemeHomOverComp x τ) (NeronModelInfra.schemeHomOverComp y τ) := by

  have affine : ∀ (R : Type) [CommRing R] [Algebra k R] (x y : SchemeHomOver (specMap k R) (torusStr k d)),
      NeronModelInfra.schemeHomOverComp (LT.mul _ x y) τ =
        L.mul _ (NeronModelInfra.schemeHomOverComp x τ) (NeronModelInfra.schemeHomOverComp y τ) := by
    intro R _ _ x y
    obtain ⟨χ, rfl⟩ := exists_eq_torusPt d R x
    obtain ⟨χ', rfl⟩ := exists_eq_torusPt d R y
    have h1 := hconv R (WithConv.toConv χ) (WithConv.toConv χ')
    have h2 := hτ R (WithConv.toConv χ) (WithConv.toConv χ')
    rw [← h1]
    exact h2

  have key : ∀ (R : CommRingCat.{0}) (φ : Spec R ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver φ (torusStr k d)),
      (NeronModelInfra.schemeHomOverComp (LT.mul φ x y) τ).1 =
        (L.mul φ (NeronModelInfra.schemeHomOverComp x τ) (NeronModelInfra.schemeHomOverComp y τ)).1 := by
    intro R φ x y
    letI : Algebra k R := (Spec.preimage φ).hom.toAlgebra
    have hφ : specMap k R = φ := by
      change Spec.map (CommRingCat.ofHom (algebraMap k R)) = φ
      have : CommRingCat.ofHom (algebraMap k ↑R) = Spec.preimage φ := rfl
      rw [this, Spec.map_preimage]
    have hψ : 𝟙 (Spec R) ≫ specMap k R = φ := by rw [Category.id_comp, hφ]
    let x' : SchemeHomOver (specMap k R) (torusStr k d) := ⟨x.1, x.2.trans hφ.symm⟩
    let y' : SchemeHomOver (specMap k R) (torusStr k d) := ⟨y.1, y.2.trans hφ.symm⟩
    have hx : GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ x' = x := Subtype.ext (Category.id_comp _)
    have hy : GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ y' = y := Subtype.ext (Category.id_comp _)
    have eL := congrArg Subtype.val (LT.mul_natural (specMap k R) φ (𝟙 _) hψ x' y')
    have eR := congrArg Subtype.val (L.mul_natural (specMap k R) φ (𝟙 _) hψ
      (NeronModelInfra.schemeHomOverComp x' τ) (NeronModelInfra.schemeHomOverComp y' τ))
    have cx : GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ (NeronModelInfra.schemeHomOverComp x' τ) =
        NeronModelInfra.schemeHomOverComp x τ := Subtype.ext (Category.id_comp _)
    have cy : GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ (NeronModelInfra.schemeHomOverComp y' τ) =
        NeronModelInfra.schemeHomOverComp y τ := Subtype.ext (Category.id_comp _)
    rw [hx, hy] at eL
    rw [cx, cy] at eR
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp] at eL eR
    have ha := congrArg Subtype.val (affine R x' y')
    change (LT.mul φ x y).1 ≫ τ.1 = _
    rw [← eL, ← eR]
    exact ha

  apply Subtype.ext
  refine Scheme.Cover.hom_ext T'.affineCover _ _ fun i => ?_
  have eL := congrArg Subtype.val (LT.mul_natural s (T'.affineCover.f i ≫ s) (T'.affineCover.f i) rfl x y)
  have eR := congrArg Subtype.val (L.mul_natural s (T'.affineCover.f i ≫ s) (T'.affineCover.f i) rfl
    (NeronModelInfra.schemeHomOverComp x τ) (NeronModelInfra.schemeHomOverComp y τ))
  simp only [GoodReductionJacobian.schemeHomOverComp_coe] at eL eR
  have ek := key _ (T'.affineCover.f i ≫ s)
    (GoodReductionJacobian.schemeHomOverComp (T'.affineCover.f i) rfl x)
    (GoodReductionJacobian.schemeHomOverComp (T'.affineCover.f i) rfl y)

  have cx : GoodReductionJacobian.schemeHomOverComp (T'.affineCover.f i) rfl (NeronModelInfra.schemeHomOverComp x τ) =
      NeronModelInfra.schemeHomOverComp (GoodReductionJacobian.schemeHomOverComp (T'.affineCover.f i) rfl x) τ :=
    Subtype.ext (Category.assoc _ _ _).symm
  have cy : GoodReductionJacobian.schemeHomOverComp (T'.affineCover.f i) rfl (NeronModelInfra.schemeHomOverComp y τ) =
      NeronModelInfra.schemeHomOverComp (GoodReductionJacobian.schemeHomOverComp (T'.affineCover.f i) rfl y) τ :=
    Subtype.ext (Category.assoc _ _ _).symm
  rw [cx, cy] at eR
  change T'.affineCover.f i ≫ ((LT.mul s x y).1 ≫ τ.1) = T'.affineCover.f i ≫ _
  rw [← Category.assoc, eL, eR]
  exact ek

end KAsm

open KAsm in
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

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)) (D.baseChange k))
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation k c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange k).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t (D.baseChange k).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]
    (hXred : IsReduced (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))) :
    ∃ (T : Scheme.{0}) (tT : T ⟶ Spec (CommRingCat.of k)) (LT : RelativeGroupLaw k tT)
      (jT : SchemeHomOver tT (D.baseChange k).toBase)
      (eT : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin (n - 1) → Rˣ) ≃ SchemeHomOver (specMap k R) tT),

      IsClosedImmersion jT.1 ∧
      (∀ {T' : Scheme.{0}} (s : T' ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver s tT),
        NeronModelInfra.schemeHomOverComp (LT.mul s x y) jT =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps).mul s
            (NeronModelInfra.schemeHomOverComp x jT) (NeronModelInfra.schemeHomOverComp y jT)) ∧

      (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t (D.baseChange k).toBase),
        (∃ y : SchemeHomOver t tT, NeronModelInfra.schemeHomOverComp y jT = x) ↔
          (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) x =
              (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₁.some).one t ∧
            postComp ν₂ x = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hrep₂.some).one t)) ∧

      (∀ (R : Type) [CommRing R] [Algebra k R] (u v : Fin (n - 1) → Rˣ),
        eT R (u * v) = LT.mul _ (eT R u) (eT R v)) ∧
      (∀ (R R' : Type) [CommRing R] [Algebra k R] [CommRing R'] [Algebra k R'] (a : R →ₐ[k] R') (u : Fin (n - 1) → Rˣ),
        (eT R' (fun i => Units.map a.toRingHom.toMonoidHom (u i))).1 =
          Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (eT R u).1) ∧

      (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of k)) (x₁ : SchemeHomOver t D₁.toBase) (x₂ : SchemeHomOver t D₂.toBase)
        (z : T'), ∃ (U : T'.Opens) (_ : z ∈ U) (x : SchemeHomOver (U.ι ≫ t) (D.baseChange k).toBase),
          (postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) x).1 = U.ι ≫ x₁.1 ∧
          (postComp ν₂ x).1 = U.ι ≫ x₂.1) := by
  classical

  obtain ⟨τ, hτci, hτmul, hτker⟩ :=
    AlgebraicGeometry.RelPicard.exists_torus_isClosedImmersion_ker_restrictPair_of_twoGluedSmoothCurves
      (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) hXred c₁ c₂ i₁ i₂ hcover hred n hn hn0
      (sectionBaseChange k ε) ε₁ hε₁ ε₂ (D.baseChange k) hreps D₁ hrep₁.some D₂ hrep₂.some
      (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) ν₂ rfl hν₂
  obtain ⟨LT, eT, heT_mul, heT_nat, hconv, hone⟩ := KTorus.exists_law_and_points k (n - 1)
  haveI : IsSeparated (D.baseChange k).toBase := by
    rw [RelativePic0Designation.baseChange_toBase]; infer_instance
  have hτmul' := AlgebraicGeometry.SplitTorus.forall_torusPt_mul_of_torusPtId_mul_of_isAlgClosed
    (D.baseChange k).toBase (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hreps) (n - 1) τ hτmul
  refine ⟨_, torusStr k (n - 1), LT, τ, eT, hτci, ?_, ?_, heT_mul, heT_nat, ?_⟩
  ·
    intro T' s x y
    exact KAsm.comp_mul_eq_mul_comp_of_forall_torusPt (n - 1) LT hconv _ _ τ hτmul' s x y
  ·
    intro T' t x
    have h := hτker t x
    constructor
    · rintro ⟨y, hy⟩
      have h' := h.mpr ⟨y, hy⟩
      exact ⟨Subtype.ext (congrArg Subtype.val h'.1), Subtype.ext (congrArg Subtype.val h'.2)⟩
    · rintro ⟨h1, h2⟩
      exact h.mp ⟨Subtype.ext (congrArg Subtype.val h1), Subtype.ext (congrArg Subtype.val h2)⟩
  ·
    intro T' t x₁ x₂ z
    obtain ⟨U, hz, a, h1, h2⟩ := KEpi.exists_opens_lift_of_twoGluedSmoothCurves
      (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) hXred c₁ c₂ i₁ i₂ hcover hred n hn hn0
      (sectionBaseChange k ε) ε₁ hε₁ ε₂ (D.baseChange k) hreps D₁ hrep₁.some D₂ hrep₂.some
      (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) ν₂ rfl hν₂ t x₁ x₂ z
    exact ⟨U, hz, a, h1, h2⟩

end S_ModularCurve_XOneP_exists_relativeGroupLaw_isClosedImmersion_iff_postComp_pullbackHom_eq_one_splitTorus_specialFibre_baseChange_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_relativeGroupLaw_isClosedImmersion_iff_postComp_pullbackHom_eq_one_splitTorus_specialFibre_baseChange_x1_mul (solution)
