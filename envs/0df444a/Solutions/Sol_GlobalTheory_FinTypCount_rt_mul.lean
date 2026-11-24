-- Prove2me | solution 1 for GlobalTheory.FinTypCount.rt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:26:37.969922+00:00
-- url     : https://prove2.me/submissions/4e6e7d78-c322-42eb-859d-ef8b7a587f0d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeAleph0SmoothIrreducibleUnitaryAdelic
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NG
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.FinTypCount
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
variable {n : ℕ}
namespace GlobalTheory.FinTypCount
theorem _root_.solution (h h' : GAf L n) (f : GAf L n → ℂ) : rt L n (h * h') f = rt L n h (rt L n h' f) := by
  funext x
  simp [rt, mul_assoc]
end GlobalTheory.FinTypCount
