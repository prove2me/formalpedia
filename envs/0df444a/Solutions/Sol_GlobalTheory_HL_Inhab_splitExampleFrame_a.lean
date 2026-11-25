-- Prove2me | solution 1 for GlobalTheory.HL.Inhab.splitExampleFrame_a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:37:08.90958+00:00
-- url     : https://prove2.me/submissions/547166b6-b0f5-44bf-9356-3aa9eec24165

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
import Theorems.Thm_GlobalTheory_HL_Inhab_splitExampleFrame_G
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_Model_vE_pow
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
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.Inhab
theorem _root_.solution (L : LocE F E) (hE : ¬ IsField E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (m : ℕ) :
    (toyG L hE ϖ hϖ m).a = 2 := by
  have h := vE_pow L ϖ hϖ 1 6
  simp only [zpow_ofNat, Units.val_one, OneMemClass.coe_one, mul_one] at h
  have hϖ' : (toyG L hE ϖ hϖ m).ϖ = ϖ := rfl
  have hgg : (toyG L hE ϖ hϖ m).gg = true := rfl
  simp only [Frames.a, splitExampleFrame_G, Frames.vth, hϖ', h, hgg]
  norm_num
end GlobalTheory.HL.Inhab
