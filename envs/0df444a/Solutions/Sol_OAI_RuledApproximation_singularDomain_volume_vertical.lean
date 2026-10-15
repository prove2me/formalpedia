-- Prove2me | solution 1 for OAI.RuledApproximation.singularDomain_volume_vertical
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:54:17.161656+00:00
-- url     : https://prove2.me/submissions/c2d214b1-0502-48f3-8eae-76d95b21ca83

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/ConeVolume.lean:L101-L115
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.singularDomain_volume_vertical. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
import Definitions.Def_OAI_Geometry_RuledCovering_SingularField
import Definitions.Def_OAI_Geometry_RuledCovering_PlanarIntegration
import Definitions.Def_OAI_Geometry_RuledCovering_ConeVolume
import Theorems.Thm_OAI_RuledApproximation_singularDomain_isCompact

-- ---- from OAI.Geometry.RuledCovering.PlanarIntegration ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma pairPlane_measurePreserving : MeasurePreserving pairPlaneEquiv volume volume :=
  (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_finTwoArrow ℝ).symm

lemma plane_integral_pair (f : Plane → ℝ) :
    (∫ z, f z) = ∫ q : ℝ × ℝ, f (vec2 q.1 q.2) :=
  (pairPlane_measurePreserving.integral_comp pairPlaneEquiv.measurableEmbedding f).symm

lemma plane_integrable_pair (f : Plane → ℝ) :
    Integrable (fun q : ℝ × ℝ => f (vec2 q.1 q.2)) ↔ Integrable f :=
  pairPlane_measurePreserving.integrable_comp_emb pairPlaneEquiv.measurableEmbedding

lemma plane_setIntegral_vertical {S : Set Plane} (hS : MeasurableSet S)
    {f : Plane → ℝ} (hf : IntegrableOn f S) :
    (∫ z in S, f z) = ∫ b : ℝ, ∫ r in {r : ℝ | vec2 b r ∈ S}, f (vec2 b r) := by
  rw [← integral_indicator hS,plane_integral_pair]
  rw [Measure.volume_eq_prod,integral_prod _ (by simpa only [Measure.volume_eq_prod] using (plane_integrable_pair _).mpr (hf.integrable_indicator hS))]
  apply integral_congr_ae
  filter_upwards with b
  have hm : MeasurableSet {r : ℝ | vec2 b r ∈ S} := hS.preimage (pairPlaneEquiv.measurable.comp (measurable_const.prodMk measurable_id))
  rw [← integral_indicator hm]
  rfl

lemma plane_setIntegral_vertical_interval {S : Set Plane} (hS : MeasurableSet S)
    {f : Plane → ℝ} (hf : IntegrableOn f S) {s : Set ℝ} (hs : MeasurableSet s)
    {l u : ℝ → ℝ} (heq : ∀ z : Plane, z ∈ S ↔ z 0 ∈ s ∧ z 1 ∈ Icc (l (z 0)) (u (z 0))) :
    (∫ z in S, f z) = ∫ b in s, ∫ r in Icc (l b) (u b), f (vec2 b r) := by
  rw [plane_setIntegral_vertical hS hf,← integral_indicator hs]
  congr 1
  funext b
  by_cases hb : b ∈ s
  · rw [Set.indicator_of_mem hb]
    apply setIntegral_congr_set
    filter_upwards with r
    apply propext
    change vec2 b r ∈ S ↔ r ∈ Icc (l b) (u b)
    simpa only [vec2_apply_zero,vec2_apply_one,hb,true_and] using heq (vec2 b r)
  · rw [Set.indicator_of_notMem hb]
    have he : {r : ℝ | vec2 b r ∈ S} = ∅ := by
      ext r
      simpa [hb] using heq (vec2 b r)
    simp [he]

lemma plane_volume_vertical_interval {S : Set Plane} (hS : MeasurableSet S)
    (hfin : volume S ≠ ⊤) {s : Set ℝ} (hs : MeasurableSet s)
    {l u : ℝ → ℝ} (heq : ∀ z : Plane, z ∈ S ↔ z 0 ∈ s ∧ z 1 ∈ Icc (l (z 0)) (u (z 0))) :
    volume.real S = ∫ b in s, max (u b-l b) 0 := by
  have hi := plane_setIntegral_vertical_interval hS (integrableOn_const (C := (1:ℝ)) hfin) hs heq
  simpa [measureReal_def,Real.volume_Icc,ENNReal.toReal_ofReal'] using hi

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.ConeVolume ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singularDomain_volume_vertical (p gamma c : ℝ)
    (hcap : ∀ b : ℝ, |b| ≤ 2 → (1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ) ≤ 2) :
    volume.real (singularDomain p gamma c) = ∫ b in Icc (-2:ℝ) 2,
      max ((1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ)-max (c^gamma) |b|) 0 := by
  apply plane_volume_vertical_interval (singularDomain_isCompact p gamma c).measurableSet
    (singularDomain_isCompact p gamma c).measure_lt_top.ne measurableSet_Icc
  intro z
  unfold singularDomain
  simp only [mem_ofPred_eq,mem_Icc,max_le_iff]
  constructor
  · intro hz
    have hb := abs_le.mp (hz.2.2.1.trans hz.2.1)
    exact ⟨hb,⟨⟨hz.1,hz.2.2.1⟩,hz.2.2.2⟩⟩
  · rintro ⟨hb,⟨⟨hd,hb'⟩,hceil⟩⟩
    exact ⟨hd,hceil.trans (hcap (z 0) (abs_le.mpr hb)),hb',hceil⟩

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.singularDomain_volume_vertical := @_root_.OAI.RuledApproximation.singularDomain_volume_vertical
