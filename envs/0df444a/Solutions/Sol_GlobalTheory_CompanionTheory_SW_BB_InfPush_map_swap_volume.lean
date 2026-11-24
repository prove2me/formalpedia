-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.InfPush.map_swap_volume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:10:51.695845+00:00
-- url     : https://prove2.me/submissions/a6cdeb3c-b8e8-4c63-b2a4-f902cf88dabb

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHomeomorphRankOneTuplesStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyRealStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanCoordinateMeasureTransport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.InfPush
namespace GlobalTheory.CompanionTheory.SW.BB.InfPush
theorem _root_.solution (ι κ : Type) [Fintype ι] [Fintype κ] :
    (volume : Measure (ι → κ → ℝ)).map (fun f k i => f i k) = (volume : Measure (κ → ι → ℝ)) := by
  let s : (ι → κ → ℝ) ≃+ (κ → ι → ℝ) :=
    { toFun := fun f k i => f i k
      invFun := fun g i k => g k i
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hs : Continuous s := continuous_pi fun k => continuous_pi fun i =>
    (continuous_apply k).comp (continuous_apply i)
  have hs' : Continuous s.symm := continuous_pi fun i => continuous_pi fun k =>
    (continuous_apply i).comp (continuous_apply k)
  have h0 : (volume : Measure (κ → ℝ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  have h0' : (volume : Measure (ι → ℝ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  have hV : (volume : Measure (ι → κ → ℝ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  have hV' : (volume : Measure (κ → ι → ℝ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  have hH : ((volume : Measure (ι → κ → ℝ)).map s).IsAddHaarMeasure :=
    s.isAddHaarMeasure_map _ hs hs'
  have hc := Measure.isAddLeftInvariant_eq_smul ((volume : Measure (ι → κ → ℝ)).map s)
    (volume : Measure (κ → ι → ℝ))
  set c := Measure.addHaarScalarFactor ((volume : Measure (ι → κ → ℝ)).map s)
    (volume : Measure (κ → ι → ℝ)) with hcdef
  let B : Set (κ → ι → ℝ) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc 0 1
  let B' : Set (ι → κ → ℝ) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc 0 1
  have hB : MeasurableSet B := MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ =>
    measurableSet_Icc
  have hpre : s ⁻¹' B = B' := by
    ext f
    simp only [B, B', Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    exact forall_comm
  have vB : (volume : Measure (κ → ι → ℝ)) B = 1 := by
    simp only [B]
    rw [volume_pi_pi]
    refine Finset.prod_eq_one fun _ _ => ?_
    rw [volume_pi_pi]
    refine Finset.prod_eq_one fun _ _ => ?_
    simp
  have vB' : (volume : Measure (ι → κ → ℝ)) B' = 1 := by
    simp only [B']
    rw [volume_pi_pi]
    refine Finset.prod_eq_one fun _ _ => ?_
    rw [volume_pi_pi]
    refine Finset.prod_eq_one fun _ _ => ?_
    simp
  have h1 : ((volume : Measure (ι → κ → ℝ)).map s) B = 1 := by
    rw [Measure.map_apply hs.measurable hB, hpre, vB']
  have hc1 : c = 1 := by
    rw [hc] at h1
    simp only [Measure.smul_apply, vB] at h1
    simpa using h1
  rw [hc1, one_smul] at hc
  exact hc
end GlobalTheory.CompanionTheory.SW.BB.InfPush
