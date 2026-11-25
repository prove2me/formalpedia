-- Prove2me | solution 1 for GlobalTheory.Sloc.CloseConj.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:02:46.449312+00:00
-- url     : https://prove2.me/submissions/88dd3f2e-b19a-4702-983d-98fe623d2264

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsIntegralOfQuad
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PairingConjInverseAdjointCloseToOne
import Theorems.Thm_GlobalTheory_Sloc_CloseConj_cT_mul
import Theorems.Thm_GlobalTheory_Sloc_CloseConj_cT_one
import Theorems.Thm_GlobalTheory_Sloc_CloseConj_cT_sub
import Theorems.Thm_GlobalTheory_Sloc_CloseConj_cj_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.Sloc GlobalTheory.Sloc.CloseConj
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.Sloc.CloseConj
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (n : ℕ) (Z Zi M Mi M' : Matrix (Fin n) (Fin n) E) (t e : E), t ∈ L.O → L.cj t = t → Zi * Z = 1 → (∀ i j, e * Z i j ∈ L.O) → (∀ i j, e * Zi i j ∈ L.O) → Mi * M = 1 → M * Mi = 1 → (∀ i j, ∃ o ∈ L.O, (Mi - 1) i j = t * o) → cT L M * Z * M' = Z → ∀ i j, ∃ o ∈ L.O, e * e * (M' - 1) i j = t * o := by
  intro F _ _ _ E _ _ _ L n Z Zi M Mi M' t e ht htc hZiZ heZ heZi hMiM hMMi hclose hM'
  have hc : cT L Mi * cT L M = 1 := by rw [← cT_mul, hMMi, cT_one]
  have hM'eq : M' = Zi * cT L Mi * Z := by
    calc M' = Zi * (cT L Mi * cT L M) * Z * M' := by rw [hc, Matrix.mul_one, hZiZ, Matrix.one_mul]
      _ = Zi * cT L Mi * (cT L M * Z * M') := by simp only [Matrix.mul_assoc]
      _ = Zi * cT L Mi * Z := by rw [hM']
  have hsub : M' - 1 = Zi * cT L (Mi - 1) * Z := by
    rw [hM'eq, cT_sub, cT_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hZiZ]
  choose o ho hoe using hclose
  intro i j
  refine ⟨∑ l, ∑ k, (e * Zi i k) * L.cj (o l k) * (e * Z l j), ?_, ?_⟩
  · refine Subring.sum_mem _ fun l _ => Subring.sum_mem _ fun k _ => ?_
    exact Subring.mul_mem _ (Subring.mul_mem _ (heZi i k) (cj_mem L (ho l k))) (heZ l j)
  · rw [hsub]
    simp only [Matrix.mul_apply, cT, hoe, map_mul, htc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    ring
end GlobalTheory.Sloc.CloseConj
