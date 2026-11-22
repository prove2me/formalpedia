-- Prove2me | solution 1 for Matrix.UnitaryGroup.smul_comp_orbitMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:57:11.100131+00:00
-- url     : https://prove2.me/submissions/802ddde4-fd17-4b03-af49-37f5c36c3174

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_Unitary
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MeasureSpace
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Matrix_UnitaryHaar
public import Mathlib.Topology.Instances.Matrix
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudy

set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Matrix
open scoped LinearAlgebra.Projectivization
open Matrix Matrix.UnitaryGroup
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Matrix.UnitaryGroup
theorem _root_.solution (U' : Matrix.unitaryGroup ι ℂ)
    (p₀ : ℙ ℂ (EuclideanSpace ℂ ι)) :
    (fun p => U' • p) ∘ orbitMap p₀ = orbitMap p₀ ∘ (fun U => U' * U) := by
  funext U
  show U' • (U • p₀) = (U' * U) • p₀
  exact smul_smul U' U p₀
end Matrix.UnitaryGroup
