-- Prove2me | solution 1 for GlobalTheory.CuspGL.minpoly_natDegree_dvd_iff_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:04.941509+00:00
-- url     : https://prove2.me/submissions/e03168c2-a5c2-49ec-a1c3-9ff25753e0dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusMinpolyDegreeRootPowerSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F] [Finite F]
open Polynomial
variable {F : Type} [Field F] [Finite F]
namespace GlobalTheory.CuspGL
namespace _root_.GlobalTheory.CuspGL
theorem _root_.solution (α : AlgebraicClosure F) (m : ℕ) :
    (minpoly F α).natDegree ∣ m ↔ α ^ Nat.card F ^ m = α := by
  rw [(minpoly.irreducible (Algebra.IsIntegral.isIntegral α)).natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X,
    minpoly.dvd_iff]
  simp [sub_eq_zero]
end _root_.GlobalTheory.CuspGL
end GlobalTheory.CuspGL
