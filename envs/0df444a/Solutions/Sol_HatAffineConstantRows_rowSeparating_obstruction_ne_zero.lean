-- Prove2me | solution 1 for HatAffineConstantRows.rowSeparating_obstruction_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:18:30.198427+00:00
-- url     : https://prove2.me/submissions/db4c110d-a605-47e5-a6a2-63e5eaa09146

import Definitions.Def_HatAffineGeneral_Discovery
import Definitions.Def_HatAffineConstantRows_LowDegreeBox
import Definitions.Def_HatAffineConstantRows_ConstantRows
import Theorems.Thm_HatAffineConstantRows_affineObstructionFactor_rowSeparating_ne_zero

set_option autoImplicit true
open scoped BigOperators
open HatAffineConstantRows
universe u v
open Finset
open MvPolynomial
namespace HatAffineConstantRows
theorem _root_.solution
    {K : Type u} [Field K] {m : Nat} {I : Type v} [Fintype I]
    (A : I → Fin m → K) (b : I → K) :
    affineObstruction A b (rowSeparatingOffset A b) ≠ 0 := by
  classical
  rw [affineObstruction, Finset.prod_ne_zero_iff]
  intro i hi
  exact affineObstructionFactor_rowSeparating_ne_zero A b i
end HatAffineConstantRows
