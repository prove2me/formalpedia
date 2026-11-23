-- Prove2me | solution 1 for GlobalTheory.isOpenUnits_and_eventually_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:15:43.456401+00:00
-- url     : https://prove2.me/submissions/df77ac0b-3413-4437-88e1-ad5f8bc27494

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Theorems.Thm_GlobalTheory_isOpenUnits_and_eventually_sq_normed
import Theorems.Thm_GlobalTheory_finiteNormedAlgebra_eq_moduleTopology

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open GlobalTheory
open MeasureTheory Filter Topology
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] [CharZero F] (R : Type) [CommRing R] [Algebra F R] [Module.Finite F R]
    [τ : TopologicalSpace R] [IsModuleTopology F R] :
    IsOpenUnits R ∧ ∀ᶠ v in 𝓝 (1 : R), ∃ s : R, s ^ 2 = v := by
  classical
  have h := eq_moduleTopology F R
  let b := Module.finBasis F R
  letI : NormedRing (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedRing
  letI : NormedAlgebra F (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedAlgebra
  letI N : NormedCommRing R :=
    NormedCommRing.induced R _ (Algebra.leftMulMatrix b) (Algebra.leftMulMatrix_injective b)
  letI : NormedAlgebra F R := NormedAlgebra.induced F R _ (Algebra.leftMulMatrix b)
  have key := _root_.GlobalTheory.isOpenUnits_and_eventually_sq_normed F R
  have h2 := _root_.GlobalTheory.finiteNormedAlgebra_eq_moduleTopology F R
  have h3 : τ = N.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace :=
    h.trans h2.symm
  rw [h3]
  exact key
end _root_.GlobalTheory
end GlobalTheory
