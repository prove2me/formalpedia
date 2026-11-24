-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.chiH_sym
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:44:30.978009+00:00
-- url     : https://prove2.me/submissions/92d52080-b818-4484-bdba-9282af2d7204

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_HeckeId_sum_add_cc
import Theorems.Thm_GlobalTheory_SW_Base_herm_one
import Theorems.Thm_GlobalTheory_SW_Nbr_herm_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
open Nbr
namespace GlobalTheory.SW.HeckeId
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (a b : Fin N → E)
    (x : Matrix (Fin n) (Fin N) E) : chiH Ψ (sym a b) x = eT (herm 1 (x *ᵥ a) (x *ᵥ b)) := by
  have h : ∀ a b : Fin N → E,
      (x * vecMulVec a (fun i => cc (b i)) * ccT x).trace = herm 1 (x *ᵥ a) (x *ᵥ b) := by
    intro a b
    rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, Nbr.herm_one]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [ccT, cc, Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  rw [chiH, eT, ← sum_add_cc hΨ, herm_symm, sym, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, h, h]
end GlobalTheory.SW.HeckeId
