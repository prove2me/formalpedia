-- Prove2me | solution 1 for GlobalTheory.HL.MoveTotal.triple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:32:43.57281+00:00
-- url     : https://prove2.me/submissions/3e198d49-9d1b-4e57-8cf8-14e7f331ff36

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NoLeak
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermExponentsNonnegAndDefectGroupBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FrameMoveCharacterNeOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralProdFubiniStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralLinearPositiveNormBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexIntegrableShareTopLevelVectorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerMoveScalarFibreMeasureOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermIntegralNearOneBoundStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsFineSubgroupMovesAtLatticeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMovesTotalMeasureEstimates
import Theorems.Thm_GlobalTheory_HL_MoveTotal_cint_zero
import Theorems.Thm_GlobalTheory_HL_MoveTotal_nice_of_ne
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_IdxInt_Lin_cint_zero
import Theorems.Thm_GlobalTheory_T_indexMeasureIntegral_linear_positive_norm_bound
import Theorems.Thm_GlobalTheory_T_indexMeasureIntegral_prod_fubini
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.MoveTotal
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
variable {W W₁ W₂ W₃ : Type} [AddCommGroup W] [AddCommGroup W₁] [AddCommGroup W₂] [AddCommGroup W₃]
namespace GlobalTheory.HL.MoveTotal
theorem _root_.solution (A₁ : AddSubgroup W₁) (A₂ : AddSubgroup W₂) (A₃ : AddSubgroup W₃) (P : W₁ → Prop)
    (Q Z : W₂ → Prop) (R : W₂ → W₃ → Prop) (M : W₁ × W₂ × W₃ → Prop)
    (hM : ∀ b u t, M (b, u, t) ↔ P b ∧ Q u ∧ R u t)
    (h1 : ∀ u, Z u → cint A₃ (ind (R u)) = 1) (h2 : ∀ u, (∃ t, R u t) → Z u) (g : W₁ → W₂ → ℂ)
    (hn : Nice (A₁.prod (A₂.prod A₃)) (fun w => ind M w * g w.1 w.2.1)) :
    Nice A₁ (fun b => ind P b * cint A₂ (fun u => ind (fun u => Q u ∧ Z u) u * g b u)) ∧
    cint (A₁.prod (A₂.prod A₃)) (fun w => ind M w * g w.1 w.2.1) =
      cint A₁ (fun b => ind P b * cint A₂ (fun u => ind (fun u => Q u ∧ Z u) u * g b u)) := by
  obtain ⟨k1, k2, k3⟩ := GlobalTheory.T.indexMeasureIntegral_prod_fubini _ _ _ hn
  have key : (fun b => cint (A₂.prod A₃) (fun w' => ind M (b, w') * g b w'.1)) =
      (fun b => ind P b * cint A₂ (fun u => ind (fun u => Q u ∧ Z u) u * g b u)) := by
    funext b
    rw [(GlobalTheory.T.indexMeasureIntegral_prod_fubini _ _ _ (k1 b)).2.2]
    by_cases hb : P b
    · rw [show ind P b = 1 by simp [ind, hb], one_mul]
      congr 1
      funext u
      by_cases hq : Q u
      · by_cases hz : Z u
        · have e : (fun t => ind M (b, u, t) * g b u) = fun t => g b u * ind (R u) t := by
            funext t; simp [ind, hM, hb, hq]
          have := ((GlobalTheory.T.indexMeasureIntegral_linear_positive_norm_bound A₃).2.1 (g b u) _ (nice_of_ne _ _ (by rw [h1 u hz]; simp))).2
          simp only
          rw [e, this, h1 u hz]
          simp [ind, hq, hz]
        · have e : (fun t => ind M (b, u, t) * g b u) = fun _ => 0 := by
            funext t
            have : ¬ R u t := fun h => hz (h2 u ⟨t, h⟩)
            simp [ind, hM, this]
          simp only
          rw [e, cint_zero]
          simp [ind, hz]
      · have e : (fun t => ind M (b, u, t) * g b u) = fun _ => 0 := by
          funext t
          simp [ind, hM, hq]
        simp only
        rw [e, cint_zero]
        simp [ind, hq]
    · have e : (fun u => cint A₃ (fun t => ind M (b, u, t) * g b u)) = fun _ => 0 := by
        funext u
        have e : (fun t => ind M (b, u, t) * g b u) = fun _ => 0 := by
          funext t
          simp [ind, hM, hb]
        rw [e, cint_zero]
      simp only
      rw [e, cint_zero]
      simp [ind, hb]
  simp only at k2 k3
  rw [key] at k2 k3
  exact ⟨k2, k3⟩
end GlobalTheory.HL.MoveTotal
