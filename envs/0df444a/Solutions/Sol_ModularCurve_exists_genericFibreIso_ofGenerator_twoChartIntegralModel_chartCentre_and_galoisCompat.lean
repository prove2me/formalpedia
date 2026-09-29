-- Prove2me | solution 1 for ModularCurve.exists_genericFibreIso_ofGenerator_twoChartIntegralModel_chartCentre_and_galoisCompat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/616f6e6a-1d75-5347-a18e-9996bd2e146c

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_JacJ1_ChartAlgebra
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat
import Theorems.Thm_ModularCurve_exists_algEquiv_tensor_chartAlg_chartRing_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_CurveModel_coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iota0
import Theorems.Thm_AlgebraicCurve_CurveModel_coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iotaInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_genericFibreIso_ofGenerator_twoChartIntegralModel_chartCentre_and_galoisCompat
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IntermediateField ModularCurve AlgebraicCurve AlgebraicCurve.CurveModel
open scoped TensorProduct

universe u

namespace XHG

theorem ringHom_eq_of_specMap_eq {A B : Type u} [CommRing A] [CommRing B] {f g : A →+* B}
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

end XHG

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (p : ℕ) [Fact p.Prime]
    (j : ↥F₀) [Fact (j ≠ 0)]
    (jb : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))
    (hjb : (jb : LaurentSeries (AlgebraicClosure ℚ)) =
      coeffEmb (AlgebraicClosure ℚ) ((j : ↥F₀) : LaurentSeries ℚ))
    (htrans : Transcendental (AlgebraicClosure ℚ) jb) [Fact (jb ≠ 0)]
    [FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
      ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)]
    [FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({jb⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))
      ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)] :
    ∃ (eη : (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).C ⟶
        pullback (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
          (Spec.map (CommRingCat.ofHom
            (algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ)))))
      (_ : IsIso eη),
      eη ≫ pullback.snd _ _ = (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).toBase ∧
      (∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
            (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).C //
            q ≫ (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).toBase = 𝟙 _})
        (β : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) →+*
          AlgebraicClosure ℚ),
        x.1 ≫ eη ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom β) ≫
            TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j →
        ∀ b : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j),
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥F₀).2⟩ :
              ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) -
            algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) (β b) ∈
          ((CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).pointEquivPlace
            x).toValuationSubring.nonunits) ∧
      (∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
            (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).C //
            q ≫ (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).toBase = 𝟙 _})
        (β : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) →+*
          AlgebraicClosure ℚ),
        x.1 ≫ eη ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom β) ≫
            TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j →
        ∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j),
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥F₀).2⟩ :
              ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) -
            algebraMap (AlgebraicClosure ℚ) ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀) (β b) ∈
          ((CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).pointEquivPlace
            x).toValuationSubring.nonunits) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
            (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).C //
            q ≫ (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).toBase = 𝟙 _}),
        x'.1 ≫ eη ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
            x.1 ≫ eη ≫ pullback.fst _ _ →
        (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).pointEquivPlace x' =
          arithmeticGalois (L := AlgebraicClosure ℚ) F₀ σ •
            (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).pointEquivPlace x) := by
  classical
  obtain ⟨⟨eFin, hFin⟩, ⟨eInf, hInf⟩⟩ :=
    ModularCurve.exists_algEquiv_tensor_chartAlg_chartRing_laurentBaseChange F₀ p j jb hjb
  obtain ⟨eη, hiso, heη, hchartFin, hchartInf, hgal⟩ :=
    ModularCurve.exists_genericFibreIso_twoChartIntegralModel_chartPin_and_galoisCompat
      F₀ p j jb hjb htrans eFin hFin eInf hInf
  refine ⟨eη, hiso, heη, ?_, ?_, hgal⟩
  ·
    intro x β hx b

    have hβ : β.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)) =
        algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) := by
      apply XHG.ringHom_eq_of_specMap_eq
      have h1 := eq_whisker hx (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
      simp only [Category.assoc] at h1
      rw [pullback.condition, reassoc_of% heη, reassoc_of% x.2, TwoChartIntegralModel.ιFin_toBase,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h1
      exact h1.symm

    let βa : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ :=
      { toRingHom := β, commutes' := fun r => RingHom.congr_fun hβ r }
    let βt : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
        →ₐ[AlgebraicClosure ℚ] AlgebraicClosure ℚ :=
      Algebra.TensorProduct.lift (AlgHom.id (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)) βa (fun _ _ => Commute.all _ _)
    have hβt : ∀ c, βt (1 ⊗ₜ c) = β c := by
      intro c
      simp [βt, βa, Algebra.TensorProduct.lift_tmul]
    let χ : ↥(CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) →ₐ[AlgebraicClosure ℚ]
        AlgebraicClosure ℚ := βt.comp (eFin.symm : _ →ₐ[AlgebraicClosure ℚ] _)
    have hχ : ∀ c, χ (eFin (1 ⊗ₜ c)) = β c := by
      intro c
      simp [χ, hβt]

    have hxfac : x.1 = Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ CurveModel.ι₀ (AlgebraicClosure ℚ) jb := by
      haveI := hiso
      rw [← cancel_mono eη]
      apply pullback.hom_ext
      · simp only [Category.assoc]
        erw [Category.assoc]
        erw [hx, hchartFin]
        rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 3
        ext c
        simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply]
        exact (hχ c).symm
      · simp only [Category.assoc]
        rw [heη, x.2]
        change 𝟙 _ = Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ CurveModel.ι₀ (AlgebraicClosure ℚ) jb ≫
          CurveModel.gluedToBase (AlgebraicClosure ℚ) jb
        rw [CurveModel.ι₀_gluedToBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe,
          AlgHom.comp_algebraMap]
        change 𝟙 _ = Spec.map (CommRingCat.ofHom (RingHom.id (AlgebraicClosure ℚ)))
        rw [CommRingCat.ofHom_id]; exact (Spec.map_id _).symm

    have hz : (pointEquivClosedPoint (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).toBase x).1 =
        (CurveModel.ι₀ (AlgebraicClosure ℚ) jb).base
          ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) := by
      rw [pointEquivClosedPoint_apply_coe]
      conv_lhs => rw [hxfac]
      rfl
    have key := AlgebraicCurve.CurveModel.coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iota0
      (AlgebraicClosure ℚ) jb (CurveModel.gluedPlaceOfPoint (AlgebraicClosure ℚ) jb htrans)
      (CurveModel.range_stalk_eq_gluedPlaceOfPoint (AlgebraicClosure ℚ) jb htrans) χ
      (pointEquivClosedPoint (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).toBase x) hz
      (eFin (1 ⊗ₜ b))
    rw [CurveModel.pointEquivPlace_apply]
    have hcb : ((eFin (1 ⊗ₜ b) : ↥(CurveModel.chartRing (AlgebraicClosure ℚ) ({jb} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) =
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥F₀).2⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) := hFin b
    rw [← hcb, ← hχ b]
    exact key.2
  ·
    intro x β hx b

    have hβ : β.comp (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)) =
        algebraMap ↥(GaloisRep.ratLocalizedAt p) (AlgebraicClosure ℚ) := by
      apply XHG.ringHom_eq_of_specMap_eq
      have h1 := eq_whisker hx (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
      simp only [Category.assoc] at h1
      rw [pullback.condition, reassoc_of% heη, reassoc_of% x.2, TwoChartIntegralModel.ιInf_toBase,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp] at h1
      exact h1.symm

    let βa : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j) →ₐ[↥(GaloisRep.ratLocalizedAt p)] AlgebraicClosure ℚ :=
      { toRingHom := β, commutes' := fun r => RingHom.congr_fun hβ r }
    let βt : (AlgebraicClosure ℚ) ⊗[↥(GaloisRep.ratLocalizedAt p)] ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥F₀ j)
        →ₐ[AlgebraicClosure ℚ] AlgebraicClosure ℚ :=
      Algebra.TensorProduct.lift (AlgHom.id (AlgebraicClosure ℚ) (AlgebraicClosure ℚ)) βa (fun _ _ => Commute.all _ _)
    have hβt : ∀ c, βt (1 ⊗ₜ c) = β c := by
      intro c
      simp [βt, βa, Algebra.TensorProduct.lift_tmul]
    let χ : ↥(CurveModel.chartRing (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀))) →ₐ[AlgebraicClosure ℚ]
        AlgebraicClosure ℚ := βt.comp (eInf.symm : _ →ₐ[AlgebraicClosure ℚ] _)
    have hχ : ∀ c, χ (eInf (1 ⊗ₜ c)) = β c := by
      intro c
      simp [χ, hβt]

    have hxfac : x.1 = Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ CurveModel.ιInf (AlgebraicClosure ℚ) jb := by
      haveI := hiso
      rw [← cancel_mono eη]
      apply pullback.hom_ext
      · simp only [Category.assoc]
        erw [Category.assoc]
        erw [hx, hchartInf]
        rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 3
        ext c
        simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply]
        exact (hχ c).symm
      · simp only [Category.assoc]
        rw [heη, x.2]
        change 𝟙 _ = Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ CurveModel.ιInf (AlgebraicClosure ℚ) jb ≫
          CurveModel.gluedToBase (AlgebraicClosure ℚ) jb
        rw [CurveModel.ιInf_gluedToBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe,
          AlgHom.comp_algebraMap]
        change 𝟙 _ = Spec.map (CommRingCat.ofHom (RingHom.id (AlgebraicClosure ℚ)))
        rw [CommRingCat.ofHom_id]; exact (Spec.map_id _).symm

    have hz : (pointEquivClosedPoint (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).toBase x).1 =
        (CurveModel.ιInf (AlgebraicClosure ℚ) jb).base
          ((Spec.map (CommRingCat.ofHom χ.toRingHom)).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ))) := by
      rw [pointEquivClosedPoint_apply_coe]
      conv_lhs => rw [hxfac]
      rfl
    have key := AlgebraicCurve.CurveModel.coe_mem_and_sub_algebraMap_mem_nonunits_of_range_stalk_eq_iotaInf
      (AlgebraicClosure ℚ) jb (CurveModel.gluedPlaceOfPoint (AlgebraicClosure ℚ) jb htrans)
      (CurveModel.range_stalk_eq_gluedPlaceOfPoint (AlgebraicClosure ℚ) jb htrans) χ
      (pointEquivClosedPoint (CurveModel.ofGenerator (AlgebraicClosure ℚ) jb htrans).toBase x) hz
      (eInf (1 ⊗ₜ b))
    rw [CurveModel.pointEquivPlace_apply]
    have hcb : ((eInf (1 ⊗ₜ b) : ↥(CurveModel.chartRing (AlgebraicClosure ℚ) ({jb⁻¹} : Set ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)))) : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) =
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥F₀) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥F₀).2⟩ : ↥(laurentBaseChange (AlgebraicClosure ℚ) F₀)) := hInf b
    rw [← hcb, ← hχ b]
    exact key.2

end S_ModularCurve_exists_genericFibreIso_ofGenerator_twoChartIntegralModel_chartCentre_and_galoisCompat
end P2MW
export P2MW.S_ModularCurve_exists_genericFibreIso_ofGenerator_twoChartIntegralModel_chartCentre_and_galoisCompat (solution)
