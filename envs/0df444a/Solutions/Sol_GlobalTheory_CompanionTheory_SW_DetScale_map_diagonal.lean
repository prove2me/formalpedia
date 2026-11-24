-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.DetScale.map_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:15:16.571562+00:00
-- url     : https://prove2.me/submissions/e9207986-2d25-4462-ab4d-337ee8a9387b

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarMapLinearScalingByDeterminant
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_DetScale_measurable_mulVec
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_DetScale_char_smul_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.DetScale
open Matrix
open scoped Pointwise
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R]
  [BorelSpace R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.DetScale
theorem _root_.solution (lam : Measure R) [lam.IsAddHaarMeasure] (d : ι → Rˣ) :
    distribHaarChar R (∏ i, d i) •
        (Measure.pi fun _ : ι => lam).map (fun x => diagonal (fun i => (d i : R)) *ᵥ x) =
      Measure.pi fun _ : ι => lam := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  rw [Measure.smul_apply, Measure.map_apply (measurable_mulVec _) (MeasurableSet.univ_pi hs)]
  have h1 : (fun x : ι → R => diagonal (fun i => (d i : R)) *ᵥ x) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ fun i => (fun y : R => (d i : R) * y) ⁻¹' s i := by
    ext f
    simp [mulVec_diagonal]
  have hm : ∀ i, Measurable fun x : R => (d i : R) * x := fun i =>
    (continuous_const.mul continuous_id).measurable
  rw [h1, Measure.pi_pi, map_prod, ENNReal.smul_def, smul_eq_mul, ENNReal.coe_finset_prod,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 := congrArg (fun m : Measure R => m (s i)) (char_smul_map lam (d i))
  simp only [Measure.smul_apply, Measure.map_apply (hm i) (hs i)] at h2
  rw [← h2]
  rfl
end GlobalTheory.CompanionTheory.SW.DetScale
