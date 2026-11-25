-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure.sphereMeasure_map_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:56:15.568654+00:00
-- url     : https://prove2.me/submissions/35a24637-992d-4c63-aca6-7036af7be103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SphereBlockLogMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory NumberField MvPolynomial
open scoped ENNReal NNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
theorem _root_.solution {N : ℕ}
    (e : EuclideanSpace ℂ (Fin (N + 1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (N + 1))) :
    (sphereMeasure N).map (sphereMap e) = sphereMeasure N := by
  have hc : Continuous (sphereMap e) :=
    Continuous.subtype_mk (e.continuous.comp continuous_subtype_val) _
  let e' : EuclideanSpace ℂ (Fin (N + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin (N + 1)) :=
    { e.toLinearEquiv.restrictScalars ℝ with norm_map' := e.norm_map }
  have hs : (sphereSurface N).map (sphereMap e) = sphereSurface N := by
    ext s hs
    rw [Measure.map_apply hc.measurable hs, sphereSurface,
      Measure.toSphere_apply' _ (hc.measurable hs), Measure.toSphere_apply' _ hs]
    congr 1
    rw [← e'.measurePreserving.measure_preimage_emb e'.toHomeomorph.measurableEmbedding
      (Set.Ioo (0 : ℝ) 1 • ((Subtype.val : UnitSphere N → EuclideanSpace ℂ (Fin (N + 1))) '' s))]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_smul, Set.mem_image]
    constructor
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨r, hr, _, ⟨_, hz, rfl⟩, (e'.map_smul r z.1).symm⟩
    · rintro ⟨r, hr, y, ⟨z, hz, rfl⟩, hx⟩
      refine ⟨r, hr, _, ⟨sphereMap e.symm z, ?_, rfl⟩, ?_⟩
      · have : sphereMap e (sphereMap e.symm z) = z := Subtype.ext (e.apply_symm_apply z.1)
        simpa [this] using hz
      · apply e'.injective
        rw [← hx, e'.map_smul]
        congr 1
        exact e.apply_symm_apply z.1
  rw [sphereMeasure, Measure.map_smul, hs]
end GlobalTheory.IndefiniteRowSideFullHecke.UnitSphereMeasure
