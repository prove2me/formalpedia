-- Prove2me | solution 1 for GlobalTheory.Cube.termMap_mem_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:51.245785+00:00
-- url     : https://prove2.me/submissions/bb851440-1f24-4a0a-ae8e-8434e895bb60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
noncomputable section
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
open CategoryTheory Limits
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
namespace GlobalTheory
namespace _root_.GlobalTheory.Cube
theorem _root_.solution {A B : _root_.GlobalTheory.Cube.{v} ι R} (φ : A ⟶ B) {p : ℕ}
    {x : _root_.GlobalTheory.Cube.Term A p}
    (h : x ∈ LinearMap.ker (_root_.GlobalTheory.Cube.d A p)) :
    _root_.GlobalTheory.Cube.termMap φ p x ∈ LinearMap.ker (_root_.GlobalTheory.Cube.d B p) := by
  rw [LinearMap.mem_ker, ← _root_.GlobalTheory.Cube.termMap_d, LinearMap.mem_ker.1 h,
    map_zero]
end _root_.GlobalTheory.Cube
end GlobalTheory
