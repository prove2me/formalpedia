-- Prove2me | solution 1 for NoHair.euclidean_cover_lifts_af_exterior
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T11:10:12.988785+00:00
-- url     : https://prove2.me/submissions/515b0246-fdc4-4206-b541-4c5dc12b7202

import Theorems.Thm_NoHair_asymptotically_flat_end_proper_cylinder
import Theorems.Thm_NoHair_proper_spherical_cylinder_lifts_to_euclidean_sheet
import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

noncomputable section

theorem solution (Q : Type) [m : MetricSpace Q] [ch : ChartedSpace ADMPoint Q] [sm : IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [rb : RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [sr : IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [rm : IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] [cm : CompleteSpace Q] [cn : ConnectedSpace Q]
    [sc : SecondCountableTopology Q]
    (hend : HasScalarFlatZeroADMEnd Q) (p : ADMPoint → Q) (cover : IsCoveringMap p) :
    ∃ U : Set ADMPoint, IsOpen U ∧ ¬ Bornology.IsBounded U ∧ IsCompact (frontier U) ∧ Set.InjOn p U := by
  letI : LocallyPathConnectedSpace Q := ChartedSpace.locallyPathConnectedSpace ADMPoint Q
  letI : PathConnectedSpace Q := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  obtain ⟨e,he,far⟩ := asymptotically_flat_end_proper_cylinder Q hend
  exact proper_spherical_cylinder_lifts_to_euclidean_sheet e he far p cover
