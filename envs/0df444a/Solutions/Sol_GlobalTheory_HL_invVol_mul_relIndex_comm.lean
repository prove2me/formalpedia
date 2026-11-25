-- Prove2me | solution 1 for GlobalTheory.HL.invVol_mul_relIndex_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:41:21.393924+00:00
-- url     : https://prove2.me/submissions/75149ee4-619e-401d-8639-8c51f00bd863

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormOrbitSumLeOfSymmKernel
import Theorems.Thm_GlobalTheory_HL_invVol_mul_pos_le_conj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL
variable {G X : Type} [Group G] [MulAction G X] (St : Subgroup G)
namespace GlobalTheory.HL
theorem _root_.solution {G : Type} [Group G] (K0 A B : Subgroup G)
    (hA : K0.relIndex A ≠ 0) (hA' : A.relIndex K0 ≠ 0)
    (hB : K0.relIndex B ≠ 0) (hB' : B.relIndex K0 ≠ 0) :
    invVol K0 A * (B.relIndex A : ℝ) = invVol K0 B * (A.relIndex B : ℝ) := by
  have h1 : K0.relIndex (A ⊓ B) ≠ 0 := fun h =>
    hA (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h)
  have h2 : (A ⊓ B).relIndex K0 ≠ 0 := Subgroup.relIndex_inf_ne_zero hA' hB'
  have e1 := (invVol_mul_pos_le_conj K0 A (A ⊓ B) hA hA' h1 h2).2.2.1 inf_le_left
  have e2 := (invVol_mul_pos_le_conj K0 B (A ⊓ B) hB hB' h1 h2).2.2.1 inf_le_right
  rw [Subgroup.inf_relIndex_left] at e1
  rw [Subgroup.inf_relIndex_right] at e2
  rw [← e1, ← e2]
end GlobalTheory.HL
