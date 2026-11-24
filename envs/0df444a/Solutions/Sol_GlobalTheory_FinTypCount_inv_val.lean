-- Prove2me | solution 1 for GlobalTheory.FinTypCount.inv_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:09:49.196141+00:00
-- url     : https://prove2.me/submissions/c85ba130-81c1-4a55-9bf2-b03683f84f4e

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
theorem _root_.solution (g : GAf L n) :
    (((g⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      conjT (conjAL L) (g.1 : Matrix (Fin n) (Fin n) (AL L)) := by
  have hm := g.2
  simp only [GA, UGroup, Subgroup.mem_mk] at hm
  exact Units.inv_eq_of_mul_eq_one_right hm
end GlobalTheory.FinTypCount
