-- Prove2me | solution 1 for ModularCurve.exists_curveModel_iso_genericFibre_galoisCompat_chartPin_twoChartIntegralModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/d7a37fb1-7579-5e19-a245-d31644297b8e

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Theorems.Thm_ModularCurve_exists_algEquiv_tensor_chartAlg_chartRing_laurentBaseChange
import Theorems.Thm_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_of_coe_eq_coeffEmb
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_curveModel_iso_genericFibre_galoisCompat_chartPin_twoChartIntegralModel
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve

universe u

namespace B1PrimeExport

section ExportTools
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

theorem appIso_hom_res_app_appIso_inv_apply
    {X Y : Scheme} (f : Y ⟶ X) {A B : CommRingCat} (ι : Spec A ⟶ X) [IsOpenImmersion ι]
    (g : Spec B ⟶ Y) [IsOpenImmersion g] (θ : A ⟶ B) (hfac : g ≫ f = Spec.map θ ≫ ι) (a : A)
    (V' : (Spec B).Opens) (hV' : g ''ᵁ V' ≤ f ⁻¹ᵁ (ι ''ᵁ ⊤)) :
    (g.appIso V').hom (Y.presheaf.map (homOfLE hV').op
      ((f.app (ι ''ᵁ ⊤)) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a)))) =
    (Spec B).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso B).inv (θ a)) := by
  let V : X.Opens := ι ''ᵁ ⊤
  let r := (Scheme.ΓSpecIso A).inv a
  show (g.appIso V').hom (Y.presheaf.map (homOfLE hV').op ((f.app V) ((ι.appIso ⊤).inv r))) = _

  have e1 := CategoryTheory.ConcreteCategory.congr_hom (g.appIso_hom V')
    (Y.presheaf.map (homOfLE hV').op ((f.app V) ((ι.appIso ⊤).inv r)))
  rw [CategoryTheory.comp_apply] at e1
  rw [e1]

  have e2 := CategoryTheory.ConcreteCategory.congr_hom (g.naturality (homOfLE hV').op) ((f.app V) ((ι.appIso ⊤).inv r))
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e2
  rw [e2]

  have e3 := CategoryTheory.ConcreteCategory.congr_hom
    ((Scheme.Hom.comp_app g f V).symm.trans ((Scheme.Hom.congr_app hfac V).trans
      (congrArg (· ≫ (Spec B).presheaf.map _) (Scheme.Hom.comp_app (Spec.map θ) ι V))))
    ((ι.appIso ⊤).inv r)
  erw [e3]
  erw [CategoryTheory.comp_apply, CategoryTheory.comp_apply]

  have e4 := CategoryTheory.ConcreteCategory.congr_hom (ι.appIso_inv_app ⊤) r
  rw [CategoryTheory.comp_apply] at e4
  erw [e4]

  have e5 := CategoryTheory.ConcreteCategory.congr_hom
    ((Spec.map θ).naturality (eqToHom (ι.preimage_image_eq ⊤)).op) r
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e5
  erw [e5]

  have e6 := CategoryTheory.ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality θ) a
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e6
  erw [← e6]

  simp only [← CategoryTheory.comp_apply]
  rfl

end ExportTools

section ExportGenerator
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicCurve AlgebraicCurve.CurveModel
open scoped IntermediateField

theorem glued_ffEquiv_symm_germToFunctionField
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
    [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]
    {X : Scheme.{u}} (f : glued K t ⟶ X) {A₀ : CommRingCat.{u}}
    (ι : Spec A₀ ⟶ X) [IsOpenImmersion ι]
    (θ : A₀ ⟶ CommRingCat.of ↥(chartRing K ({t} : Set L)))
    (hfac : ι₀ K t ≫ f = Spec.map θ ≫ ι) (a : A₀)
    [hne : Nonempty (f ⁻¹ᵁ (ι ''ᵁ ⊤))] :
    (((gluedFunctionFieldEquiv K t).symm
      ((glued K t).germToFunctionField (f ⁻¹ᵁ (ι ''ᵁ ⊤))
        ((f.app (ι ''ᵁ ⊤)) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A₀).inv a))))) : L) =
      ((θ a : ↥(chartRing K ({t} : Set L))) : L) := by
  set U : (glued K t).Opens := f ⁻¹ᵁ (ι ''ᵁ ⊤) with hU
  set σ : Γ(glued K t, U) := (f.app (ι ''ᵁ ⊤)) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A₀).inv a)) with hσ
  let V' : (X₀ K t).Opens := (ι₀ K t) ⁻¹ᵁ U
  have hV'U : (ι₀ K t) ''ᵁ V' ≤ U := by
    rintro _ ⟨x, hx, rfl⟩; exact hx

  have hηU : genericPoint (glued K t) ∈ U := by
    obtain ⟨⟨x, hx⟩⟩ := hne
    exact ((genericPoint_spec (glued K t)).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩
  have hξV' : genericPoint (X₀ K t) ∈ V' := by
    show (ι₀ K t).base (genericPoint (X₀ K t)) ∈ U
    rw [genericPoint_eq_of_isOpenImmersion]
    exact hηU
  have hη : genericPoint (glued K t) ∈ (ι₀ K t) ''ᵁ V' :=
    ⟨genericPoint (X₀ K t), hξV', genericPoint_eq_of_isOpenImmersion _⟩

  have step1 : (glued K t).germToFunctionField U σ =
      (glued K t).presheaf.germ ((ι₀ K t) ''ᵁ V') (genericPoint (glued K t)) hη
        (((ι₀ K t).appIso V').inv (((ι₀ K t).appIso V').hom
          ((glued K t).presheaf.map (homOfLE hV'U).op σ))) := by
    rw [Iso.hom_inv_id_apply, TopCat.Presheaf.germ_res_apply]

  have step2 : ((ι₀ K t).appIso V').hom ((glued K t).presheaf.map (homOfLE hV'U).op σ) =
      (X₀ K t).presheaf.map (homOfLE le_top).op (secTop K (chartRing K ({t} : Set L)) (θ a)) :=
    appIso_hom_res_app_appIso_inv_apply f ι (ι₀ K t) θ hfac a V' hV'U
  rw [step1, step2]

  rw [ffEquiv_symm_germ_appIso_inv K t (chartRing K ({t} : Set L)) (ι₀ K t) (incl₀ K t)
    (fun b => coe_chartIncl K _ b) rfl V' _ (genericPoint (X₀ K t)) hξV' hη]

  rw [germ_res_secTop]
  exact thetaHom_toStalk K t (chartRing K ({t} : Set L)) (incl₀ K t) (fun b => coe_chartIncl K _ b) _ _

theorem ofGenerator_ffEquiv_symm_germToFunctionField
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
    [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    (ht : Transcendental K t)
    {X : Scheme.{u}} (f : (CurveModel.ofGenerator K t ht).C ⟶ X) {A₀ : CommRingCat.{u}}
    (ι : Spec A₀ ⟶ X) [IsOpenImmersion ι]
    (θ : A₀ ⟶ CommRingCat.of ↥(chartRing K ({t} : Set L)))
    (hfac : ι₀ K t ≫ f = Spec.map θ ≫ ι) (a : A₀)
    [hne : Nonempty (f ⁻¹ᵁ (ι ''ᵁ ⊤))] :
    (((CurveModel.ofGenerator K t ht).ffEquiv.symm
      ((CurveModel.ofGenerator K t ht).C.germToFunctionField (f ⁻¹ᵁ (ι ''ᵁ ⊤))
        ((f.app (ι ''ᵁ ⊤)) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A₀).inv a))))) : L) =
      ((θ a : ↥(chartRing K ({t} : Set L))) : L) :=
  @glued_ffEquiv_symm_germToFunctionField K _ L _ _ t _ _ X f A₀ ι _ θ hfac a hne

end ExportGenerator

end B1PrimeExport

open B1PrimeExport in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (p : ℕ) [Fact p.Prime]
    (j : ↥F₀) [Fact (j ≠ 0)] (htj : Transcendental ℚ j)
    (hfd : FiniteDimensional ↥(IntermediateField.adjoin ℚ ({j} : Set ↥F₀)) ↥F₀)
    (hreg : ∀ x : ↥F₀, IsAlgebraic ℚ x → ∃ c : ℚ, x = algebraMap ℚ ↥F₀ c) :
    ∃ (M : CurveModel (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))
      (e : M.C ⟶ pullback (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
        (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))))
      (_ : IsIso e),
      e ≫ pullback.snd _ _ = M.toBase ∧
      (∀ (g : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ))
        (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.C // s ≫ M.toBase = 𝟙 _}),
        x'.1 ≫ e ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom (g : (AlgebraicClosure ℚ) →+* (AlgebraicClosure ℚ))) ≫ x.1 ≫ e ≫ pullback.fst _ _ →
        M.pointEquivPlace x' = arithmeticGalois (L := (AlgebraicClosure ℚ)) F₀ g • M.pointEquivPlace x) ∧
      ∃ (_ : Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
          (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
            ((TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) ''ᵁ ⊤)))),
        ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j),
          ((M.ffEquiv.symm
              (M.C.germToFunctionField
                ((e ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
                    (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
                  ((TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) ''ᵁ ⊤))
                (((e ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
                    (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))).app
                    ((TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) ''ᵁ ⊤)).hom
                  (((TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).appIso ⊤).inv
                    ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j))).inv a))))
              : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) : LaurentSeries (AlgebraicClosure ℚ)) =
            coeffEmb (AlgebraicClosure ℚ) ((a : ↥F₀) : LaurentSeries ℚ) := by
  classical

  let jb : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) :=
    ⟨coeffEmb (AlgebraicClosure ℚ) ((j : ↥F₀) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (j : ↥F₀).2⟩
  have hjb : (jb : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) ((j : ↥F₀) : LaurentSeries ℚ) := rfl
  haveI := hfd
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  obtain ⟨htrans, hfdL⟩ :=
    ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_of_coe_eq_coeffEmb (AlgebraicClosure ℚ) F₀ j htj jb hjb
  haveI := hfdL
  haveI hne0 : Fact (jb ≠ 0) := ⟨fun h => htrans (by rw [h]; exact isAlgebraic_zero)⟩
  haveI hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) := by
    have h : IntermediateField.adjoin (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) =
        IntermediateField.adjoin (AlgebraicClosure ℚ) ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_simple_le_iff]
        exact inv_mem (IntermediateField.mem_adjoin_simple_self _ _)
      · rw [IntermediateField.adjoin_simple_le_iff]
        simpa using inv_mem (IntermediateField.mem_adjoin_simple_self (AlgebraicClosure ℚ) (jb⁻¹))
    rw [h]; infer_instance

  obtain ⟨⟨eFin, hFin⟩, ⟨eInf, hInf⟩⟩ := ModularCurve.exists_algEquiv_tensor_chartAlg_chartRing_laurentBaseChange F₀ p j jb hjb

  obtain ⟨e, hiso, heeta, hcF, -, hgal⟩ :=
    ModularCurve.exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat F₀ p j jb hjb htrans eFin hFin eInf hInf

  let θr : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) →+* ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) :=
    eFin.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ↥(GaloisRep.ratLocalizedAt p)) (A := AlgebraicClosure ℚ) (B := ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j))).toRingHom
  have hθr : ∀ a, ((θr a : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) =
      ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥F₀) : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥F₀).2⟩ :=
    fun a => hFin a
  let θ : CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) ⟶ CommRingCat.of ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) :=
    CommRingCat.ofHom θr
  have hfac : AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) jb ≫ (e ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _) = Spec.map θ ≫ (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) := hcF
  have hUne : ∀ ξ : ↥(AlgebraicCurve.CurveModel.X₀ (AlgebraicClosure ℚ) jb),
      (AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) jb).base ξ ∈ (e ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) ''ᵁ ⊤) := by
    intro ξ
    have e := congrArg (fun g => g.base ξ) hfac
    exact ⟨(Spec.map θ).base ξ, trivial, e.symm⟩
  have hne : Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) ''ᵁ ⊤))) :=
    ⟨⟨(AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) jb).base (Classical.arbitrary _), hUne _⟩⟩
  have hMη : ∀ a : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j),
      (((CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).ffEquiv.symm
          ((CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).C.germToFunctionField
            ((e ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) ''ᵁ ⊤))
            (((e ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ))))).app ((TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) ''ᵁ ⊤)).hom
              (((TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j))).inv a))))
          : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥F₀) : LaurentSeries ℚ) := by
    intro a
    have key := ofGenerator_ffEquiv_symm_germToFunctionField (AlgebraicClosure ℚ) jb htrans (e ≫ pullback.fst (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) _) (TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) θ hfac a
    refine (congrArg (fun y : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) => (y : LaurentSeries (AlgebraicClosure ℚ))) key).trans ?_
    simp only [θ, CommRingCat.hom_ofHom, hθr]
  exact ⟨CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans, e, hiso, heeta, hgal, hne, hMη⟩

end S_ModularCurve_exists_curveModel_iso_genericFibre_galoisCompat_chartPin_twoChartIntegralModel
end P2MW
export P2MW.S_ModularCurve_exists_curveModel_iso_genericFibre_galoisCompat_chartPin_twoChartIntegralModel (solution)
