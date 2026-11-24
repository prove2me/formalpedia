-- Prove2me | solution 1 for GlobalTheory.map_pi_eq_of_map_addHaar_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:20:00.734022+00:00
-- url     : https://prove2.me/submissions/7bba2937-c05f-479d-9e99-ab86f65cc21f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MapPiEqOfMapAddHaarEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (φ : G →+ G) (hφ : Continuous φ)
    (h : ∀ ν : Measure G, ν.IsAddHaarMeasure → ν.map φ = ν) (m : ℕ)
    (μ : @Measure (Fin m → G) (borel _))
    (hμ : @Measure.IsAddHaarMeasure (Fin m → G) _ _ (borel _) μ) :
    @Measure.map _ _ (borel _) (borel _) (fun x i => φ (x i)) μ = μ := by
  have hb : (MeasurableSpace.pi : MeasurableSpace (Fin m → G)) = borel _ := BorelSpace.measurable_eq
  revert μ hμ
  rw [← hb]
  intro μ hμ
  let ν : Measure G := Measure.addHaar
  have hν : ν.IsAddHaarMeasure := inferInstance
  have hp : MeasurePreserving φ ν ν := ⟨hφ.measurable, h ν hν⟩
  have hpi : MeasurePreserving (fun (x : Fin m → G) i => φ (x i)) (Measure.pi fun _ => ν) (Measure.pi fun _ => ν) :=
    measurePreserving_pi _ _ (fun _ => hp)
  have hH : (Measure.pi fun _ : Fin m => ν).IsAddHaarMeasure := inferInstance
  have he := Measure.isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : Fin m => ν)
  generalize Measure.addHaarScalarFactor μ (Measure.pi fun _ : Fin m => ν) = c at he
  subst he
  rw [Measure.map_smul, hpi.map_eq]
end GlobalTheory
