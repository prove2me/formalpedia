-- Prove2me | solution 1 for NumberField.AdelicFourier.map_ringEquiv_mixedSpace_pi_eq_volume
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2af1ad6b-b91e-52c2-b597-0c86ca6d63ff

import Definitions.Def_NumberField_AdelicFourier
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_map_ringEquiv_mixedSpace_pi_eq_volume

set_option autoImplicit false

open NumberField NumberField.InfinitePlace MeasureTheory IsDedekindDomain

open scoped Classical in
theorem solution
    (F : Type) [Field F] [NumberField F]
    [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)] :
    Measure.map (fun y : (∀ w : InfinitePlace F, w.Completion) ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F y)
        (Measure.pi fun w : InfinitePlace F ↦
          if hw : w.IsReal then Measure.map (Completion.ringEquivRealOfIsReal hw).symm volume
          else Measure.map (Completion.ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm volume)
      = (volume : Measure (mixedEmbedding.mixedSpace F)) := by
  classical

  let eR : ∀ v : {v : InfinitePlace F // v.IsReal}, v.1.Completion ≃ᵐ ℝ := fun v ↦
    (Completion.isometryEquivRealOfIsReal v.2).toHomeomorph.toMeasurableEquiv
  let eC : ∀ v : {v : InfinitePlace F // ¬ v.IsReal}, v.1.Completion ≃ᵐ ℂ := fun v ↦
    (Completion.isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp v.2)).toHomeomorph.toMeasurableEquiv
  let f : {v : InfinitePlace F // ¬ v.IsReal} ≃ {w : InfinitePlace F // w.IsComplex} :=
    Equiv.subtypeEquivRight fun _ ↦ not_isReal_iff_isComplex
  set μ : ∀ w : InfinitePlace F, Measure w.Completion := fun w ↦
    if hw : w.IsReal then Measure.map (Completion.ringEquivRealOfIsReal hw).symm volume
    else Measure.map (Completion.ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm volume with hμ
  have hμR : ∀ v : {v : InfinitePlace F // v.IsReal}, μ v.1 = Measure.map (eR v).symm volume := fun v ↦ by
    simp only [hμ, dif_pos v.2]
    rfl
  have hμC : ∀ v : {v : InfinitePlace F // ¬ v.IsReal}, μ v.1 = Measure.map (eC v).symm volume := fun v ↦ by
    simp only [hμ, dif_neg v.2]
    rfl
  have hR : ∀ v : {v : InfinitePlace F // v.IsReal}, MeasurePreserving (eR v) (μ v.1) volume := fun v ↦
    ⟨(eR v).measurable, by rw [hμR v, MeasurableEquiv.map_map_symm]⟩
  have hC : ∀ v : {v : InfinitePlace F // ¬ v.IsReal}, MeasurePreserving (eC v) (μ v.1) volume := fun v ↦
    ⟨(eC v).measurable, by rw [hμC v, MeasurableEquiv.map_map_symm]⟩
  haveI hσ : ∀ w : InfinitePlace F, SigmaFinite (μ w) := fun w ↦ by
    by_cases hw : w.IsReal
    · exact (hR ⟨w, hw⟩).sigmaFinite
    · exact (hC ⟨w, hw⟩).sigmaFinite

  have h1 := measurePreserving_piEquivPiSubtypeProd μ (fun v : InfinitePlace F ↦ v.IsReal)
  have h2 : MeasurePreserving
      (fun (a : ∀ v : {v : InfinitePlace F // v.IsReal}, v.1.Completion) (v : {v : InfinitePlace F // v.IsReal}) ↦
        eR v (a v))
      (Measure.pi fun v : {v : InfinitePlace F // v.IsReal} ↦ μ v.1)
      (Measure.pi fun _ : {v : InfinitePlace F // v.IsReal} ↦ (volume : Measure ℝ)) :=
    measurePreserving_pi _ _ fun v ↦ hR v
  have h3 : MeasurePreserving
      (fun (b : ∀ v : {v : InfinitePlace F // ¬ v.IsReal}, v.1.Completion) (v : {v : InfinitePlace F // ¬ v.IsReal}) ↦
        eC v (b v))
      (Measure.pi fun v : {v : InfinitePlace F // ¬ v.IsReal} ↦ μ v.1)
      (Measure.pi fun _ : {v : InfinitePlace F // ¬ v.IsReal} ↦ (volume : Measure ℂ)) :=
    measurePreserving_pi _ _ fun v ↦ hC v
  have h4 := measurePreserving_piCongrLeft (fun _ : {w : InfinitePlace F // w.IsComplex} ↦ (volume : Measure ℂ)) f
  have htot := (h2.prod (h4.comp h3)).comp h1

  have hfun : (fun y : (∀ w : InfinitePlace F, w.Completion) ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F y) =
      (Prod.map
        (fun (a : ∀ v : {v : InfinitePlace F // v.IsReal}, v.1.Completion) (v : {v : InfinitePlace F // v.IsReal}) ↦
          eR v (a v))
        ((MeasurableEquiv.piCongrLeft (fun _ : {w : InfinitePlace F // w.IsComplex} ↦ ℂ) f) ∘
          fun (b : ∀ v : {v : InfinitePlace F // ¬ v.IsReal}, v.1.Completion) (v : {v : InfinitePlace F // ¬ v.IsReal}) ↦
            eC v (b v))) ∘
        (MeasurableEquiv.piEquivPiSubtypeProd (fun v : InfinitePlace F ↦ v.Completion) fun v ↦ v.IsReal) := by
    funext y
    rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    refine Prod.ext (funext fun v ↦ rfl) (funext fun w ↦ ?_)
    show Completion.extensionEmbedding w.1 (y w.1) =
      (MeasurableEquiv.piCongrLeft (fun _ : {w : InfinitePlace F // w.IsComplex} ↦ ℂ) f)
        (fun v : {v : InfinitePlace F // ¬ v.IsReal} ↦ eC v (y v.1)) w
    rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, cast_eq]
    rfl
  rw [hfun]
  exact htot.map_eq

end S_NumberField_AdelicFourier_map_ringEquiv_mixedSpace_pi_eq_volume
end P2MW
export P2MW.S_NumberField_AdelicFourier_map_ringEquiv_mixedSpace_pi_eq_volume (solution)
