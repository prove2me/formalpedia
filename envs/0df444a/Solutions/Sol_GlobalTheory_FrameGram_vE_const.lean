-- Prove2me | solution 1 for GlobalTheory.FrameGram.vE_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:36:49.845942+00:00
-- url     : https://prove2.me/submissions/58c95110-42f8-48e5-8910-66fa4f4cf57a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetGramTwoFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameUnipotentUnitriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameLatticeGramDetAndMinorsOrbitInvariant
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
import Theorems.Thm_GlobalTheory_UnramVal_vE_valuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FrameGram
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FrameGram
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) (r k : ℕ)
    (S : Frames L r k) (c : F) (hc : c ≠ 0) (m : ℕ) :
    vE L S.ϖ (algebraMap F E ((-1) ^ (r + 1) * c * S.th⁻¹ ^ m)) =
      vE L S.ϖ (algebraMap F E c) - m * S.vth := by
  obtain ⟨hadd, hϖ, -, -⟩ := GlobalTheory.UnramVal.vE_valuation L S.ϖ S.ϖ_irr
  have hth : S.th ≠ 0 := (GlobalTheory.FrameBasic.main L r k S).2.2.2.2.2.1
  have h1 : vE L S.ϖ (algebraMap F E 1) = 0 := by
    have := hadd 1 1 one_ne_zero one_ne_zero
    rw [mul_one] at this
    omega
  have hn : vE L S.ϖ (algebraMap F E (-1)) = 0 := by
    have := hadd (-1) (-1) (by simp) (by simp)
    rw [neg_mul_neg, mul_one] at this
    omega
  have ht : vE L S.ϖ (algebraMap F E S.th) = S.vth := by
    unfold Frames.th Frames.vth
    split_ifs
    · exact hϖ
    · exact h1
  have hti : vE L S.ϖ (algebraMap F E S.th⁻¹) = -S.vth := by
    have := hadd S.th S.th⁻¹ hth (inv_ne_zero hth)
    rw [mul_inv_cancel₀ hth] at this
    omega
  have hpow : ∀ x : F, x ≠ 0 → ∀ j : ℕ,
      vE L S.ϖ (algebraMap F E (x ^ j)) = j * vE L S.ϖ (algebraMap F E x) := by
    intro x hx j
    induction j with
    | zero => rw [pow_zero, h1]; simp
    | succ j ih => rw [pow_succ, hadd _ _ (pow_ne_zero _ hx) hx, ih]; push_cast; ring
  rw [hadd _ _ (mul_ne_zero (pow_ne_zero _ (by simp)) hc) (pow_ne_zero _ (inv_ne_zero hth)),
    hadd _ _ (pow_ne_zero _ (by simp)) hc, hpow _ (by simp), hpow _ (inv_ne_zero hth), hn, hti]
  ring
end GlobalTheory.FrameGram
