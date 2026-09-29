-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.red_jChartFin_eq_evalAt_jGeomGen_nodeEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/51679e5d-f18b-5c73-ad1f-83eef25443de

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_red_jChartFin_eq_evalAt_jGeomGen_nodeEquiv

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel ModularCurve.IgusaScheme ModularCurve.PlaceSpecialization

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

namespace CoordSS

universe u v

theorem stalkClosedPointTo_comp_germ {R : CommRingCat.{u}} [IsLocalRing R] {X Y : Scheme.{u}}
    (q : Spec R ⟶ X) (g : X ⟶ Y) (U : Y.Opens) (hU : (q ≫ g).base (IsLocalRing.closedPoint R) ∈ U) (f : Γ(Y, U)) :
    (Scheme.stalkClosedPointTo (q ≫ g)).hom ((Y.presheaf.germ U _ hU).hom f) =
      (Scheme.stalkClosedPointTo q).hom ((X.presheaf.germ (g ⁻¹ᵁ U) (q.base (IsLocalRing.closedPoint R)) hU).hom
        ((g.app U).hom f)) := by
  rw [Scheme.stalkClosedPointTo_comp]
  show ((Y.presheaf.germ U _ hU ≫ g.stalkMap _) ≫ Scheme.stalkClosedPointTo q).hom f = _
  erw [Scheme.Hom.germ_stalkMap g U (q.base (IsLocalRing.closedPoint R)) hU]
  rfl

theorem algebraMap_germ_eq_germToFunctionField {X : Scheme.{u}} [IsIntegral X] (U : X.Opens) (x : X) (hx : x ∈ U)
    [Nonempty (Scheme.Opens.toScheme U)] (f : Γ(X, U)) :
    algebraMap (X.presheaf.stalk x) X.functionField ((X.presheaf.germ U x hx).hom f) = (X.germToFunctionField U).hom f := by
  change ((X.presheaf.germ U x hx) ≫ X.presheaf.stalkSpecializes _).hom f = _
  rw [TopCat.Presheaf.germ_stalkSpecializes]

theorem stalkClosedPointTo_germ_chart {K : Type u} [Field K] {Y : Scheme.{u}} {B : Type u} [CommRing B]
    (ι : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion ι] (ψ : B →+* K)
    (q : Spec (CommRingCat.of K) ⟶ Y) (hq : q = Spec.map (CommRingCat.ofHom ψ) ≫ ι)
    (hU : q.base (IsLocalRing.closedPoint K) ∈ ι ''ᵁ ⊤) (b : B) :
    (Scheme.stalkClosedPointTo q).hom ((Y.presheaf.germ (ι ''ᵁ ⊤) _ hU).hom
      ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))) = ψ b := by
  subst hq
  rw [stalkClosedPointTo_comp_germ]
  have h1 : (ι.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)) =
      ((Spec (CommRingCat.of B)).presheaf.map (eqToHom (ι.preimage_image_eq ⊤)).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b) := by
    have := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)) (Scheme.Hom.appIso_inv_app ι ⊤)
    simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using this
  rw [h1]
  have h2 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))
    (TopCat.Presheaf.germ_res (Spec (CommRingCat.of B)).presheaf (eqToHom (ι.preimage_image_eq ⊤))
      ((Spec.map (CommRingCat.ofHom ψ)).base (IsLocalRing.closedPoint K)) hU)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
  rw [h2]
  have h3 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))
    (Scheme.germ_stalkClosedPointTo_Spec (R := CommRingCat.of B) (S := CommRingCat.of K) (CommRingCat.ofHom ψ))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h3
  refine h3.trans ?_
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (CommRingCat.of B)).inv, Iso.inv_hom_id]
  rfl

theorem read_chart {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (M : CurveModel K L) {Y : Scheme.{u}} (g : M.C ⟶ Y) {B : Type u} [CommRing B]
    (ι : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion ι]
    [Nonempty (Scheme.Opens.toScheme (g ⁻¹ᵁ (ι ''ᵁ ⊤)))]
    (pt : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) (ψ : B →+* K)
    (hpt : pt.1 ≫ g = Spec.map (CommRingCat.ofHom ψ) ≫ ι) (b : B) :
    ∃ h : M.ffEquiv.symm (M.C.germToFunctionField (g ⁻¹ᵁ (ι ''ᵁ ⊤))
        ((g.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)))) ∈
        (M.pointEquivPlace pt).toValuationSubring,
      IsLocalRing.residue (M.pointEquivPlace pt).toValuationSubring ⟨_, h⟩ =
        algebraMap K (M.pointEquivPlace pt).ResidueField (ψ b) ∧
      (M.pointEquivPlace pt).evalAt (M.ffEquiv.symm (M.C.germToFunctionField (g ⁻¹ᵁ (ι ''ᵁ ⊤))
        ((g.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))))) = ψ b := by
  have hx : pt.1.base (IsLocalRing.closedPoint K) ∈ g ⁻¹ᵁ (ι ''ᵁ ⊤) := by
    show (pt.1 ≫ g).base (IsLocalRing.closedPoint K) ∈ ι ''ᵁ ⊤
    rw [hpt]
    exact ⟨(Spec.map (CommRingCat.ofHom ψ)).base (IsLocalRing.closedPoint K), trivial, rfl⟩
  have key := M.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo pt
    ((M.C.presheaf.germ (g ⁻¹ᵁ (ι ''ᵁ ⊤)) _ hx).hom
      ((g.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b))))
  have hval : (Scheme.stalkClosedPointTo pt.1).hom ((M.C.presheaf.germ (g ⁻¹ᵁ (ι ''ᵁ ⊤)) _ hx).hom
      ((g.app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of B)).inv b)))) = ψ b := by
    rw [← stalkClosedPointTo_comp_germ pt.1 g (ι ''ᵁ ⊤) hx]
    exact stalkClosedPointTo_germ_chart ι ψ (pt.1 ≫ g) hpt hx b
  rw [algebraMap_germ_eq_germToFunctionField _ _ hx, hval] at key
  exact key

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}

theorem exists_section_of_closedPoint {K : Type u} [Field K] [IsAlgClosed K] {L : Type v} [Field L] [Algebra K L]
    (M : CurveModel K L) (P0 : closedPoints M.C) :
    ∃ pt : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      M.pointEquivPlace pt = M.placeOfPoint P0 ∧ pt.1.base (IsLocalRing.closedPoint K) = P0.1 := by
  haveI : Smooth M.toBase := SmoothOfRelativeDimension.smooth (n := 1) (f := M.toBase)
  obtain ⟨pt, hpt⟩ : ∃ pt : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      pointEquivClosedPoint M.toBase pt = P0 := ⟨_, Equiv.apply_symm_apply _ _⟩
  refine ⟨pt, ?_, congrArg (fun z : closedPoints M.C => z.1) hpt⟩
  rw [CurveModel.pointEquivPlace_apply, hpt]

theorem section_eq_comp_efib_comp0 (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : R p →+* κ)
    (uκ : Spec (CommRingCat.of κ) ⟶ fibre (N₀ := N₀) toκ) (h₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (pt : {q : Spec (CommRingCat.of κ) ⟶ (𝔓.Mfib κ toκ).C // q ≫ (𝔓.Mfib κ toκ).toBase = 𝟙 _})
    (y0 : ↥(fibre0 (N₀ := N₀) toκ))
    (hpt : pt.1.base (IsLocalRing.closedPoint κ) = (inv (𝔓.efib κ toκ)).base y0)
    (hy0 : (𝔓.comp κ toκ 0).base y0 = uκ.base (IsLocalRing.closedPoint κ)) :
    uκ = pt.1 ≫ 𝔓.efib κ toκ ≫ 𝔓.comp κ toκ 0 := by
  haveI := 𝔓.lfp
  haveI : LocallyOfFiniteType (toBase N₀ p) := inferInstance
  haveI : LocallyOfFiniteType (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom toκ))) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have hinv : (𝔓.efib κ toκ).base ((inv (𝔓.efib κ toκ)).base y0) = y0 := by
    have := Scheme.Hom.comp_apply (inv (𝔓.efib κ toκ)) (𝔓.efib κ toκ) y0
    rw [IsIso.inv_hom_id] at this
    simpa using this.symm
  refine ext_of_apply_closedPoint_eq (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom toκ))) h₂ ?_ ?_
  · rw [Category.assoc, Category.assoc, 𝔓.comp_over κ toκ 0, 𝔓.hefib κ toκ]
    exact pt.2
  · rw [← hy0]
    show _ = (𝔓.comp κ toκ 0).base ((𝔓.efib κ toκ).base (pt.1.base (IsLocalRing.closedPoint κ)))
    rw [hpt, hinv]

theorem section_comp_efib_fst_eq (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : R p →+* κ)
    {A : Type} [CommRing A] (red : A →+* κ) (φ : ↥(chartAlgFin (N₀ * p) p) →+* A)
    (uκ : Spec (CommRingCat.of κ) ⟶ fibre (N₀ := N₀) toκ)
    (h₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom red) ≫ (Spec.map (CommRingCat.ofHom φ) ≫ ιFin (N₀ * p) p))
    (pt : {q : Spec (CommRingCat.of κ) ⟶ (𝔓.Mfib κ toκ).C // q ≫ (𝔓.Mfib κ toκ).toBase = 𝟙 _})
    (huκ : uκ = pt.1 ≫ 𝔓.efib κ toκ ≫ 𝔓.comp κ toκ 0) :
    pt.1 ≫ (𝔓.efib κ toκ ≫ pullback.fst (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom toκ))) =
      Spec.map (CommRingCat.ofHom (red.comp (φ.comp 𝔓.iota0.toRingHom))) ≫ ιFin N₀ p := by
  have e1 : (pt.1 ≫ 𝔓.efib κ toκ ≫ 𝔓.comp κ toκ 0) ≫ fibreMap0 𝔓.π toκ ≫
        pullback.fst (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom toκ)) =
      pt.1 ≫ (𝔓.efib κ toκ ≫ pullback.fst (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom toκ))) := by
    simp only [Category.assoc]
    rw [← Category.assoc (𝔓.comp κ toκ 0), 𝔓.comp_pi κ toκ, Category.id_comp]
  rw [← e1, ← huκ, DRLevel.fibreMap0_fst, ← Category.assoc, h₁]
  simp only [Category.assoc, 𝔓.pi_chart]
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem iota0_jChartFin (𝔓 : DRModelPackageLevel N₀ p hpN₀) :
    𝔓.iota0.toRingHom (jChartFin N₀ p) = jChartFin (N₀ * p) p := by

  apply Subtype.ext
  apply Subtype.ext
  show (((𝔓.iota0 (jChartFin N₀ p) : ↥(chartAlgFin (N₀ * p) p)) : ↥(modularFunctionFieldFull (N₀ * p))) :
      LaurentSeries ℚ) = (((jChartFin (N₀ * p) p : ↥(chartAlgFin (N₀ * p) p)) : ↥(modularFunctionFieldFull (N₀ * p))) :
      LaurentSeries ℚ)
  rw [𝔓.iota0_spec (jChartFin N₀ p), IgusaScheme.coe_jChartFin N₀ p, IgusaScheme.coe_jFull N₀,
    IgusaScheme.coe_jChartFin (N₀ * p) p, IgusaScheme.coe_jFull (N₀ * p)]

theorem red_jChartFin_eq_evalAt_nodeEquiv (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : R p →+* κ)
    {A : Type} [CommRing A] (red : A →+* κ)
    (f : Spec (CommRingCat.of A) ⟶ X N₀ p)
    (φ : ↥(chartAlgFin (N₀ * p) p) →+* A) (hf : f = Spec.map (CommRingCat.ofHom φ) ≫ ιFin (N₀ * p) p)
    (uκ : Spec (CommRingCat.of κ) ⟶ fibre (N₀ := N₀) toκ)
    (h₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom red) ≫ f) (h₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (n : ↥(pullback (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1)))
    (hn : (pullback.fst (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1) ≫ 𝔓.comp κ toκ 0).base n =
      uκ.base (IsLocalRing.closedPoint κ)) :
    red (φ (jChartFin (N₀ * p) p)) =
      ((𝔓.nodeEquiv κ toκ n : ↥(ssPlaces p N₀ κ)) : Place κ ↥(modularFunctionFieldC κ N₀)).evalAt (jGeomGen κ N₀) := by
  subst hf
  obtain ⟨hP0, hplace⟩ := (𝔓.node_pin κ toκ n).1
  obtain ⟨pt, hptP, hptbase⟩ := exists_section_of_closedPoint (𝔓.Mfib κ toκ) ⟨_, hP0⟩
  rw [hplace] at hptP
  have huκ := section_eq_comp_efib_comp0 𝔓 κ toκ uκ h₂ pt _ hptbase hn
  have hg := section_comp_efib_fst_eq 𝔓 κ toκ red φ uκ h₁ pt huκ
  haveI := 𝔓.Mfib_chart_nonempty κ toκ
  obtain ⟨-, -, hev⟩ := read_chart (𝔓.Mfib κ toκ)
    (𝔓.efib κ toκ ≫ pullback.fst (toBase0 N₀ p) (Spec.map (CommRingCat.ofHom toκ))) (ιFin N₀ p) pt _ hg (jChartFin N₀ p)
  have hpin := (𝔓.Mfib_pin κ toκ (jChartFin N₀ p)).1 rfl
  rw [hpin, hptP] at hev
  rw [hev, RingHom.comp_apply, RingHom.comp_apply, iota0_jChartFin]

end CoordSS

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (toκ : R p →+* κ)
    {A : Type} [CommRing A] (red : A →+* κ)
    (f : Spec (CommRingCat.of A) ⟶ X N₀ p)
    (φ : ↥(chartAlgFin (N₀ * p) p) →+* A) (hf : f = Spec.map (CommRingCat.ofHom φ) ≫ ιFin (N₀ * p) p)
    (uκ : Spec (CommRingCat.of κ) ⟶ fibre (N₀ := N₀) toκ)
    (h₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom red) ≫ f) (h₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (n : ↥(pullback (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1)))
    (hn : (pullback.fst (𝔓.comp κ toκ 0) (𝔓.comp κ toκ 1) ≫ 𝔓.comp κ toκ 0).base n =
      uκ.base (IsLocalRing.closedPoint κ)) :
    red (φ (jChartFin (N₀ * p) p)) =
      ((𝔓.nodeEquiv κ toκ n : ↥(ssPlaces p N₀ κ)) : Place κ ↥(modularFunctionFieldC κ N₀)).evalAt (jGeomGen κ N₀) :=
  CoordSS.red_jChartFin_eq_evalAt_nodeEquiv 𝔓 κ toκ red f φ hf uκ h₁ h₂ n hn

end

#print axioms solution

end S_ModularCurve_DRModelPackageLevel_red_jChartFin_eq_evalAt_jGeomGen_nodeEquiv
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_red_jChartFin_eq_evalAt_jGeomGen_nodeEquiv (solution)
