-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.gidx_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:27:15.943796+00:00
-- url     : https://prove2.me/submissions/944bd3fc-593b-4c62-8c65-ca8dcf443c5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_TwistAdm_relIndex_ne_zero
import Theorems.Thm_GlobalTheory_SW_TwistAdm_std_fg
import Theorems.Thm_P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_IsFrame_relIndex_ne_zero


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
omit [IsCMField E]
namespace GlobalTheory.SW.HeckeId
theorem _root_.solution {m q : ℕ} {X Y : Lt E N} (hX : Agree m X (stdL E N)) (hle : X ≤ Y)
    (hi : X.toAddSubgroup.relIndex Y.toAddSubgroup = q) : gidx Y = q * gidx X := by
  obtain ⟨t, ht, -, -, h2⟩ := hX
  have h0 := TwistAdm.relIndex_ne_zero _ _ TwistAdm.std_fg ht h2
  unfold gidx
  have hle' : X.toAddSubgroup ≤ Y.toAddSubgroup := hle
  generalize X.toAddSubgroup = X at *
  generalize Y.toAddSubgroup = Y at *
  generalize (stdL E N).toAddSubgroup = S at *
  have a1 := AddSubgroup.relIndex_mul_relIndex (S ⊓ X) X Y inf_le_right hle'
  have a2 := AddSubgroup.relIndex_mul_relIndex (S ⊓ X) (S ⊓ Y) Y (inf_le_inf_left _ hle') inf_le_right
  have a3 := AddSubgroup.relIndex_mul_relIndex (S ⊓ X) (S ⊓ Y) S (inf_le_inf_left _ hle') inf_le_left
  rw [AddSubgroup.inf_relIndex_right] at a1 a2
  rw [AddSubgroup.inf_relIndex_left, AddSubgroup.inf_relIndex_left] at a3
  rw [← a3] at h0
  have b1 : (((S ⊓ X).relIndex (S ⊓ Y) : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (left_ne_zero_of_mul h0)
  have b2 : ((Y.relIndex S : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (right_ne_zero_of_mul h0)
  have b3 := congrArg (Nat.cast : ℕ → ℝ) (a1.trans a2.symm)
  rw [← a3, ← hi]
  push_cast at b3 ⊢
  field_simp
  linear_combination -b3
end GlobalTheory.SW.HeckeId
