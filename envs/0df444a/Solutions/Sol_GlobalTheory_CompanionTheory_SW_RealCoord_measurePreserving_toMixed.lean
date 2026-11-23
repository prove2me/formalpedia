-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.RealCoord.measurePreserving_toMixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:49.476421+00:00
-- url     : https://prove2.me/submissions/7f84e0e3-5bcc-4513-8133-ff3b8b0ba3c6

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdeleHaarMapEqScaledVolume

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.RealCoord
open InfinitePlace InfinitePlace.Completion
variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
open scoped Classical
namespace GlobalTheory.CompanionTheory.SW.RealCoord
theorem _root_.solution : MeasurePreserving (toMixed F) volume volume := by
  let f : {w : InfinitePlace F // w.IsReal} ≃ InfinitePlace F :=
    Equiv.subtypeUnivEquiv IsTotallyReal.isReal
  have h1 := (volume_measurePreserving_piCongrLeft (fun _ : InfinitePlace F => ℝ) f).symm
  have h2 : MeasurePreserving (fun y : InfinitePlace F → ℝ => fun w : {w : InfinitePlace F // w.IsReal} => y w.1)
      volume volume := by
    convert h1 using 1
    funext y w
    rfl
  refine ⟨?_, ?_⟩
  · exact h2.measurable.prodMk measurable_const
  · have hm : Measurable (fun x : {w : InfinitePlace F // w.IsReal} → ℝ =>
        (x, (0 : {w : InfinitePlace F // w.IsComplex} → ℂ))) := by fun_prop
    rw [Measure.volume_eq_prod, volume_pi (α := fun _ : {w : InfinitePlace F // w.IsComplex} => ℂ),
      Measure.pi_of_empty _ (0 : {w : InfinitePlace F // w.IsComplex} → ℂ), Measure.prod_dirac, ← h2.map_eq,
      Measure.map_map hm h2.measurable]
    rfl
end GlobalTheory.CompanionTheory.SW.RealCoord
