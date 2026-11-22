-- Prove2me | solution 1 for Matrix.UnitaryGroup.fsMeasure_smul_invariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:57:55.095375+00:00
-- url     : https://prove2.me/submissions/508483ff-de9e-4e5f-a80e-e4614ed29955

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_Unitary
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MeasureSpace
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Matrix_UnitaryHaar
public import Mathlib.Topology.Instances.Matrix
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudy
public import Theorems.Thm_Matrix_UnitaryGroup_smul_comp_orbitMap

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Matrix
open scoped LinearAlgebra.Projectivization
open Matrix Matrix.UnitaryGroup
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Matrix.UnitaryGroup
theorem _root_.solution
    (U' : Matrix.unitaryGroup ι ℂ)
    (p₀ : ℙ ℂ (EuclideanSpace ℂ ι)) :
    Measure.map (fun p => U' • p) (fsMeasure p₀)
      = fsMeasure p₀ := by
  unfold fsMeasure
  rw [Measure.map_map (continuous_const_smul U').measurable
        (orbit_map_measurable p₀)]
  rw [smul_comp_orbitMap]
  rw [← Measure.map_map (orbit_map_measurable p₀)
        (measurable_const_mul U')]
  congr 1
  exact map_mul_left_eq_self unitaryHaarProb U'
end Matrix.UnitaryGroup
