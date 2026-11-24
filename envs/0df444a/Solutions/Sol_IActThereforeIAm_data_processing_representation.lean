-- Prove2me | solution 1 for IActThereforeIAm.data_processing_representation
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T03:02:40.100302+00:00
-- url     : https://prove2.me/submissions/fcaa89eb-4039-48b9-9b2f-09f1933ea3cd

import Mathlib
import Definitions.Def_IActThereforeIAm_Basic

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff
namespace IActThereforeIAm

lemma dp_mi_le {Ω α β α' β' : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace α'] [MeasurableSpace β'] (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y) (f : α → α') (g : β → β')
    (hf : Measurable f) (hg : Measurable g) :
    mutualInfo P (fun w => f (X w)) (fun w => g (Y w)) ≤ mutualInfo P X Y := by
  unfold mutualInfo
  have e1 : P.map (fun w => (f (X w), g (Y w))) =
      (P.map fun w => (X w, Y w)).map (Prod.map f g) := by
    rw [Measure.map_map (hf.prodMap hg) (hX.prodMk hY)]; rfl
  have e2 : (P.map (fun w => f (X w))).prod (P.map (fun w => g (Y w))) =
      ((P.map X).prod (P.map Y)).map (Prod.map f g) := by
    rw [← Measure.map_prod_map _ _ hf hg, Measure.map_map hf hX, Measure.map_map hg hY]; rfl
  rw [e1, e2]
  exact InformationTheory.klDiv_map_le _ _ (hf.prodMap hg)

theorem data_processing_representation {d : ℕ} {A X : Type*} [MeasurableSpace A]
    [MeasurableSpace X] (M : LatentSCM d A) (hM : M.IsValid) (g : (Fin d → ℝ) → X)
    (hg : Measurable g) (h : X → Fin d → ℝ) (hh : Measurable h) :
    reprInfo M g h ≤ mutualInfo M.jointLaw (fun w => w.2) (fun w => (h (g w.1.1), w.1.2)) ∧
    mutualInfo M.jointLaw (fun w => w.2) (fun w => (h (g w.1.1), w.1.2)) ≤ latentInfo M := by
  haveI := hM.1
  haveI := hM.2.1
  haveI : IsFiniteMeasure M.jointLaw := by unfold LatentSCM.jointLaw; infer_instance
  constructor
  · exact dp_mi_le M.jointLaw (fun w => w.2) (fun w => (h (g w.1.1), w.1.2)) measurable_snd
      (((hh.comp hg).comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_fst)) (fun s => h (g s)) id (hh.comp hg) measurable_id
  · exact dp_mi_le M.jointLaw (fun w => w.2) (fun w => w.1) measurable_snd measurable_fst
      id (fun p => (h (g p.1), p.2)) measurable_id
      (((hh.comp hg).comp measurable_fst).prodMk measurable_snd)

end IActThereforeIAm

open IActThereforeIAm in
theorem solution {d : ℕ} {A X : Type*} [MeasurableSpace A]
    [MeasurableSpace X] (M : LatentSCM d A) (hM : M.IsValid) (g : (Fin d → ℝ) → X)
    (hg : Measurable g) (h : X → Fin d → ℝ) (hh : Measurable h) :
    reprInfo M g h ≤ mutualInfo M.jointLaw (fun w => w.2) (fun w => (h (g w.1.1), w.1.2)) ∧
    mutualInfo M.jointLaw (fun w => w.2) (fun w => (h (g w.1.1), w.1.2)) ≤ latentInfo M :=
  IActThereforeIAm.data_processing_representation M hM g hg h hh
