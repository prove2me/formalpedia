-- Prove2me | solution 1 for GlobalTheory.HL.TotalWeight.sumCls_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:01:49.441493+00:00
-- url     : https://prove2.me/submissions/07f4e729-c64c-4ec5-a8b8-35b54ce8c7c2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RmulMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumClsLeEncard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFrameClassesTotalWeightLe
import Theorems.Thm_GlobalTheory_HL_TotalWeight_natCast_pow_le_pow_of_exponent_le
import Theorems.Thm_GlobalTheory_FlagUnipotent_main
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_FrameLevel_main
import Theorems.Thm_GlobalTheory_HL_ClassCount_sumCls_le_encard
import Theorems.Thm_GlobalTheory_HL_Defect_exponents_and_defect
import Theorems.Thm_GlobalTheory_HL_FrameStabLat_main
import Theorems.Thm_GlobalTheory_HL_StabConj_main
import Theorems.Thm_GlobalTheory_IntClsCount_main
import Theorems.Thm_GlobalTheory_LengthDualFunctional_main
import Theorems.Thm_GlobalTheory_LengthQuotientSpanValuation_main
import Theorems.Thm_GlobalTheory_OrbitDenom_main
import Theorems.Thm_GlobalTheory_PowMulMemOrder_main
import Theorems.Thm_GlobalTheory_PowSmulMem_main


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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.TotalWeight
namespace GlobalTheory.HL.TotalWeight
theorem _root_.solution {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k)
    (h : ∃ d Λ, S.IsTerm d Λ) :
    (S.sumCls fun _ => 1) ≤ ENNReal.ofReal (S.Hp ^ (3 * (r + 1) ^ 2)) := by
  obtain ⟨d, Λ, hT⟩ := h
  obtain ⟨ha, hD, -, -, h1, -⟩ := GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT
  have hth : 0 ≤ S.vth := by
    unfold Frames.vth
    split_ifs <;> norm_num
  have hHp : S.Hp = (S.q : ℝ) ^ ((S.vth + S.vD).toNat + S.a.toNat) := by
    unfold Frames.Hp
    rw [← zpow_natCast]
    congr 1
    push_cast
    rw [Int.toNat_of_nonneg ha, Int.toNat_of_nonneg (add_nonneg hth hD)]
    ring
  refine (GlobalTheory.HL.ClassCount.sumCls_le_encard L r k S).trans
    ((GlobalTheory.IntClsCount.main L r k S hD).trans ?_)
  have he : r * (r + 1) ≤ 3 * (r + 1) ^ 2 := by nlinarith
  rw [hHp] at h1 ⊢
  have key := ENNReal.ofReal_le_ofReal (natCast_pow_le_pow_of_exponent_le S.q _ _ _ _ he h1)
  rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast] at key
  exact key
end GlobalTheory.HL.TotalWeight
