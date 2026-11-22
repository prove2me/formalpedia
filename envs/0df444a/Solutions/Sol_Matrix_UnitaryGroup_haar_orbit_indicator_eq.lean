-- Prove2me | solution 1 for Matrix.UnitaryGroup.haar_orbit_indicator_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:57:36.017131+00:00
-- url     : https://prove2.me/submissions/e3387ca2-f54d-475b-881b-12b4c5200b23

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudy
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_UnitaryTransitive
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Topology.Instances.Matrix
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudyUnique

set_option autoImplicit false
@[expose] public section
public section
open Matrix
open scoped LinearAlgebra.Projectivization
open Matrix Matrix.UnitaryGroup
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
namespace Matrix.UnitaryGroup
theorem _root_.solution
    {B : Set (ℙ ℂ (EuclideanSpace ℂ ι))} (hB : MeasurableSet B)
    (p₀ p : ℙ ℂ (EuclideanSpace ℂ ι)) :
    unitaryHaarProb {U : Matrix.unitaryGroup ι ℂ | U • p ∈ B}
      = unitaryHaarProb {U : Matrix.unitaryGroup ι ℂ | U • p₀ ∈ B} := by
  -- Get a unitary V_p with V_p • p₀ = p via transitivity.
  obtain ⟨V_p, hV_p⟩ :=
    MulAction.exists_smul_eq (Matrix.unitaryGroup ι ℂ) p₀ p
  -- Set equality: {U | U • p ∈ B} = (· * V_p) ⁻¹' {U | U • p₀ ∈ B}.
  have h_set_eq :
      {U : Matrix.unitaryGroup ι ℂ | U • p ∈ B}
        = (· * V_p) ⁻¹' {U | U • p₀ ∈ B} := by
    ext U
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [← hV_p, smul_smul]
  -- Measurability of the inner set (orbit map preimage of Borel).
  have h_S_meas :
      MeasurableSet {U : Matrix.unitaryGroup ι ℂ | U • p₀ ∈ B} :=
    orbit_map_measurable p₀ hB
  rw [h_set_eq, ← MeasureTheory.Measure.map_apply
        (continuous_mul_const V_p).measurable h_S_meas,
      MeasureTheory.map_mul_right_eq_self]
end Matrix.UnitaryGroup
