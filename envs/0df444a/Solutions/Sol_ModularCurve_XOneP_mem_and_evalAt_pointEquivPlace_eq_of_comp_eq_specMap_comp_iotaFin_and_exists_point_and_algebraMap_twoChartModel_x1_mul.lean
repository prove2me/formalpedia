-- Prove2me | solution 1 for ModularCurve.XOneP.mem_and_evalAt_pointEquivPlace_eq_of_comp_eq_specMap_comp_iotaFin_and_exists_point_and_algebraMap_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/64fd4932-0c59-5266-8222-23c0216909f1

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

import Theorems.Thm_AlgebraicCurve_CurveModel_ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_mem_and_evalAt_pointEquivPlace_eq_of_comp_eq_specMap_comp_iotaFin_and_exists_point_and_algebraMap_twoChartModel_x1_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve AlgebraicCurve

namespace K5Tools

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

theorem stalkClosedPointTo_germ_sec
    {X : Scheme} {R K : CommRingCat} [IsLocalRing K] (ι : Spec R ⟶ X) [IsOpenImmersion ι] (ψ : R ⟶ K)
    (g : Spec K ⟶ X) (hg : g = Spec.map ψ ≫ ι) (hV : g.base (IsLocalRing.closedPoint K) ∈ ι ''ᵁ ⊤) (a : R) :
    (Scheme.stalkClosedPointTo g).hom
      ((X.presheaf.germ (ι ''ᵁ ⊤) _ hV).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso R).inv a))) = ψ a := by
  subst hg
  have h1 := Scheme.Hom.germ_stalkMap ι (ι ''ᵁ ⊤) ((Spec.map ψ).base (IsLocalRing.closedPoint K)) hV
  have e : (ι.appIso ⊤).inv ≫ X.presheaf.germ (ι ''ᵁ ⊤) (ι.base ((Spec.map ψ).base (IsLocalRing.closedPoint K))) hV ≫
      Scheme.stalkClosedPointTo (Spec.map ψ ≫ ι) = (Scheme.ΓSpecIso R).hom ≫ ψ := by
    rw [Scheme.stalkClosedPointTo_comp, reassoc_of% h1, Scheme.Hom.appIso_inv_app_assoc,
      TopCat.Presheaf.germ_res_assoc, Scheme.germ_stalkClosedPointTo_Spec]
  have e' := CategoryTheory.ConcreteCategory.congr_hom e ((Scheme.ΓSpecIso R).inv a)
  simp only [CommRingCat.comp_apply] at e'
  exact e'.trans (by rw [CategoryTheory.Iso.inv_hom_id_apply])

end K5Tools

theorem K5_eval
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)]
    [Algebra A (AlgebraicClosure ℚ)]

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)
    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))] :
    (∀ (x : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _})
        (ψ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* AlgebraicClosure ℚ),
      x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j →
      ∀ r : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        (Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv r))))) ∈ (Mη.pointEquivPlace x).toValuationSubring ∧
        (Mη.pointEquivPlace x).evalAt
          (Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv r))))) = ψ r) := by
  classical

  let Φ : Mη.C ⟶ ModularCurve.TwoChartModel A (↥K) j :=
    eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))
  let V : (ModularCurve.TwoChartModel A (↥K) j).Opens := (ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤
  let U : Mη.C.Opens := Φ ⁻¹ᵁ V
  let sec : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) → Γ(ModularCurve.TwoChartModel A (↥K) j, V) := fun r =>
    ((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
      ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv r)
  haveI : Nonempty ↥U := Mη_chart_nonempty
  intro x ψ hx r
  have hx₀ : Φ.base (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) ∈ V := by
    change (x.1 ≫ Φ).base _ ∈ (V : Set _)
    rw [hx]
    exact ⟨(Spec.map (CommRingCat.ofHom ψ)).base _, trivial, rfl⟩
  let x₀ : ↥U := ⟨x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)), hx₀⟩
  let s := (Mη.C.presheaf.germ U x₀.1 x₀.2) (Φ.app V (sec r))
  have hgerm : Mη.C.germToFunctionField U (Φ.app V (sec r)) = algebraMap _ Mη.C.functionField s := by
    have hsp := CategoryTheory.ConcreteCategory.congr_hom
      (TopCat.Presheaf.germ_stalkSpecializes Mη.C.presheaf (U := U) x₀.2
        ((genericPoint_spec Mη.C).specializes (Set.mem_univ _))) (Φ.app V (sec r))
    rw [CommRingCat.comp_apply] at hsp
    exact hsp.symm
  obtain ⟨hmem, -, heval⟩ :=
    AlgebraicCurve.CurveModel.ffEquiv_symm_mem_and_evalAt_pointEquivPlace_eq_stalkClosedPointTo Mη x s
  change Mη.ffEquiv.symm (Mη.C.germToFunctionField U (Φ.app V (sec r))) ∈ _ ∧
    (Mη.pointEquivPlace x).evalAt (Mη.ffEquiv.symm (Mη.C.germToFunctionField U (Φ.app V (sec r)))) = ψ r
  rw [hgerm]
  refine ⟨hmem, ?_⟩
  rw [heval]

  change (Scheme.stalkClosedPointTo x.1).hom ((Mη.C.presheaf.germ U _ hx₀).hom ((Φ.app V).hom (sec r))) = ψ r
  have h1 := Scheme.Hom.germ_stalkMap Φ V (x.1.base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) hx₀
  rw [← CommRingCat.comp_apply (Φ.app V), ← h1, CommRingCat.comp_apply, ← CommRingCat.comp_apply (Scheme.Hom.stalkMap Φ _),
    ← Scheme.stalkClosedPointTo_comp]
  exact K5Tools.stalkClosedPointTo_germ_sec (ModularCurve.TwoChart.ιFin A (↥K) j) (CommRingCat.ofHom ψ) (x.1 ≫ Φ) hx hx₀ r

theorem K5_conv
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)]
    [Algebra A (AlgebraicClosure ℚ)]

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)
    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))] :
    (∀ ψ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* AlgebraicClosure ℚ,
      ψ.comp (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) = algebraMap A (AlgebraicClosure ℚ) →
      ∃ x : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _},
        x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
          Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j) := by
  classical

  let Φ : Mη.C ⟶ ModularCurve.TwoChartModel A (↥K) j :=
    eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))
  let V : (ModularCurve.TwoChartModel A (↥K) j).Opens := (ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤
  let U : Mη.C.Opens := Φ ⁻¹ᵁ V
  let sec : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) → Γ(ModularCurve.TwoChartModel A (↥K) j, V) := fun r =>
    ((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
      ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv r)
  haveI : Nonempty ↥U := Mη_chart_nonempty
  intro ψ hψ
  let g : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ ModularCurve.TwoChartModel A (↥K) j :=
    Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j
  have hg : g ≫ ModularCurve.TwoChart.modelTo A (↥K) j = 𝟙 _ ≫ specMap A (AlgebraicClosure ℚ) := by
    change (Spec.map _ ≫ ModularCurve.TwoChart.ιFin A (↥K) j) ≫ _ = 𝟙 _ ≫ Spec.map _
    rw [Category.assoc, ModularCurve.TwoChart.ιFin_modelTo, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ,
      Category.id_comp]
  let pt := pullback.lift g (𝟙 _) hg
  have hsnd : inv eη ≫ Mη.toBase = pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) := by
    rw [← heη, IsIso.inv_hom_id_assoc]
  refine ⟨⟨pt ≫ inv eη, ?_⟩, ?_⟩
  · rw [Category.assoc, hsnd, pullback.lift_snd]
  · change (pt ≫ inv eη) ≫ eη ≫ pullback.fst _ _ = g
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]

theorem K5_const
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)]
    [Algebra A (AlgebraicClosure ℚ)]

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)
    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))] :
    (∀ a : A,
      (Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) a)))))) =
        algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) (algebraMap A (AlgebraicClosure ℚ) a)) := by
  classical

  let Φ : Mη.C ⟶ ModularCurve.TwoChartModel A (↥K) j :=
    eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))
  let V : (ModularCurve.TwoChartModel A (↥K) j).Opens := (ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤
  let U : Mη.C.Opens := Φ ⁻¹ᵁ V
  let sec : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) → Γ(ModularCurve.TwoChartModel A (↥K) j, V) := fun r =>
    ((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
      ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv r)
  haveI : Nonempty ↥U := Mη_chart_nonempty
  intro a
  apply Mη.ffEquiv.injective
  rw [RingEquiv.apply_symm_apply, Mη.ffEquiv_algebraMap]

  let cX : Γ(ModularCurve.TwoChartModel A (↥K) j, ⊤) :=
    (ModularCurve.TwoChart.modelTo A (↥K) j).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)

  have h2 : (ModularCurve.TwoChartModel A (↥K) j).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫
      ((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).hom = (ModularCurve.TwoChart.ιFin A (↥K) j).appTop := by
    rw [Scheme.Hom.appIso_hom, Scheme.Hom.naturality_assoc, ← Functor.map_comp]
    change (ModularCurve.TwoChart.ιFin A (↥K) j).appTop ≫ _ = (ModularCurve.TwoChart.ιFin A (↥K) j).appTop ≫ 𝟙 _
    congr 1

  have h4 : (ModularCurve.TwoChart.ιFin A (↥K) j).appTop cX =
      (Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv
        (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) a) := by
    change ((ModularCurve.TwoChart.modelTo A (↥K) j).appTop ≫ (ModularCurve.TwoChart.ιFin A (↥K) j).appTop)
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = _
    rw [← Scheme.Hom.comp_appTop, ModularCurve.TwoChart.ιFin_modelTo]
    have n := CategoryTheory.ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)))) a
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at n
    exact n.symm
  have hsec : sec (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) a) =
      (ModularCurve.TwoChartModel A (↥K) j).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op cX := by
    have h3 := CategoryTheory.ConcreteCategory.congr_hom h2 cX
    rw [CommRingCat.comp_apply, h4] at h3
    change ((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv _ = _
    rw [← h3, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

  have hΦ : Φ ≫ ModularCurve.TwoChart.modelTo A (↥K) j = Mη.toBase ≫ specMap A (AlgebraicClosure ℚ) := by
    change (eη ≫ pullback.fst _ _) ≫ _ = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, heη]
  have htop : Φ.appTop cX =
      Mη.toBase.appTop ((Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure ℚ))).inv (algebraMap A (AlgebraicClosure ℚ) a)) := by
    change ((ModularCurve.TwoChart.modelTo A (↥K) j).appTop ≫ Φ.appTop) _ = _
    rw [← Scheme.Hom.comp_appTop, hΦ, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    congr 1
    have n := CategoryTheory.ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A (AlgebraicClosure ℚ)))) a
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at n
    exact n.symm

  have hηU : genericPoint Mη.C ∈ U :=
    ((genericPoint_spec Mη.C).mem_open_set_iff U.2).mpr (by
      obtain ⟨⟨y, hy⟩⟩ := Mη_chart_nonempty
      exact ⟨y, Set.mem_univ _, hy⟩)
  have hmor : (ModularCurve.TwoChartModel A (↥K) j).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op ≫ Φ.app V ≫
      Mη.C.presheaf.germ U (genericPoint Mη.C) hηU =
      Φ.appTop ≫ Mη.C.presheaf.germ ⊤ (genericPoint Mη.C) trivial := by
    rw [Φ.naturality_assoc, TopCat.Presheaf.germ_res]
    rfl
  have hfin := CategoryTheory.ConcreteCategory.congr_hom hmor cX
  simp only [CommRingCat.comp_apply] at hfin
  change (Mη.C.presheaf.germ U (genericPoint Mη.C) _) (Φ.app V (sec (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) a))) = _
  rw [hsec, hfin, htop]
  rfl

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M]
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)]
    [Algebra A (AlgebraicClosure ℚ)]

    (Mη : CurveModel (AlgebraicClosure ℚ) (ModularCurve.x1FunctionFieldBar (M * p)))
    (eη : Mη.C ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) [IsIso eη]
    (heη : eη ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) = Mη.toBase)
    [Mη_chart_nonempty : Nonempty (Scheme.Opens.toScheme ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))] :
    (∀ (x : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _})
        (ψ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* AlgebraicClosure ℚ),
      x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
        Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j →
      ∀ r : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        (Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv r))))) ∈ (Mη.pointEquivPlace x).toValuationSubring ∧
        (Mη.pointEquivPlace x).evalAt
          (Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv r))))) = ψ r) ∧
    (∀ ψ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* AlgebraicClosure ℚ,
      ψ.comp (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) = algebraMap A (AlgebraicClosure ℚ) →
      ∃ x : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // s ≫ Mη.toBase = 𝟙 _},
        x.1 ≫ eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ)) =
          Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j) ∧
    (∀ a : A,
      (Mη.ffEquiv.symm
          (Mη.C.germToFunctionField ((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((eη ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (AlgebraicClosure ℚ))).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv (algebraMap A ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) a)))))) =
        algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar (M * p)) (algebraMap A (AlgebraicClosure ℚ) a)) := by
  exact ⟨K5_eval p M L K A j Mη eη heη, K5_conv p M L K A j Mη eη heη, K5_const p M L K A j Mη eη heη⟩

end S_ModularCurve_XOneP_mem_and_evalAt_pointEquivPlace_eq_of_comp_eq_specMap_comp_iotaFin_and_exists_point_and_algebraMap_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_mem_and_evalAt_pointEquivPlace_eq_of_comp_eq_specMap_comp_iotaFin_and_exists_point_and_algebraMap_twoChartModel_x1_mul (solution)
