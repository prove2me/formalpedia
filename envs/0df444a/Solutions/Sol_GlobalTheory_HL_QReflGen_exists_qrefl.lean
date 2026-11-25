-- Prove2me | solution 1 for GlobalTheory.HL.QReflGen.exists_qrefl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:40:59.328952+00:00
-- url     : https://prove2.me/submissions/99716dd6-6306-4896-bce8-b5e596b9adf2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometriesFixingSubspaceLeQuasiReflectionClosure
import Theorems.Thm_GlobalTheory_HL_QReflGen_hf_add_l
import Theorems.Thm_GlobalTheory_HL_QReflGen_hf_smul_l
import Theorems.Thm_GlobalTheory_HL_QReflGen_hf_add_r
import Theorems.Thm_GlobalTheory_HL_QReflGen_hf_smul_r
import Theorems.Thm_GlobalTheory_HL_QReflGen_hf_cj
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.QReflGen
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.QReflGen
theorem _root_.solution (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm)
    (a : Fin n → E) (ha : IsUnit (hf L Hm a a)) (c : E)
    (hc : c + L.cj c + c * L.cj c * hf L Hm a a = 0) :
    ∃ g, IsQRefl L Hm a g ∧ ∀ v, g v = v + (c * hf L Hm v a) • a := by
  let g : (Fin n → E) ≃ₗ[E] (Fin n → E) :=
    { toFun := fun v => v + (c * hf L Hm v a) • a
      invFun := fun v => v + (L.cj c * hf L Hm v a) • a
      map_add' := by
        intro v w
        rw [hf_add_l]; module
      map_smul' := by
        intro r v
        rw [hf_smul_l]; simp only [RingHom.id_apply]; module
      left_inv := by
        intro v
        simp only [hf_add_l, hf_smul_l]
        rw [add_assoc, ← add_smul]
        have : c * hf L Hm v a + L.cj c * (hf L Hm v a + c * hf L Hm v a * hf L Hm a a) = 0 := by
          linear_combination hf L Hm v a * hc
        rw [this]; simp
      right_inv := by
        intro v
        simp only [hf_add_l, hf_smul_l]
        rw [add_assoc, ← add_smul]
        have : L.cj c * hf L Hm v a + c * (hf L Hm v a + L.cj c * hf L Hm v a * hf L Hm a a) = 0 := by
          linear_combination hf L Hm v a * hc
        rw [this]; simp }
  refine ⟨g, ⟨ha, ?_, c, fun v => rfl⟩, fun v => rfl⟩
  intro v w
  change hf L Hm (v + (c * hf L Hm v a) • a) (w + (c * hf L Hm w a) • a) = _
  simp only [hf_add_l, hf_add_r, hf_smul_l, hf_smul_r, map_mul, hf_cj L h]
  linear_combination hf L Hm v a * hf L Hm a w * hc
end GlobalTheory.HL.QReflGen
