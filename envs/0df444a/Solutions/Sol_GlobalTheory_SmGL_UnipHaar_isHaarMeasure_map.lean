-- Prove2me | solution 1 for GlobalTheory.SmGL.UnipHaar.isHaarMeasure_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:05:30.949949+00:00
-- url     : https://prove2.me/submissions/9bff7d33-e164-4b09-ab27-64e931dc6d61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_unipEquiv_mul
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_det_lmat_unip
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_SplitWeil_t2Space
import Theorems.Thm_GlobalTheory_WeilM_smul_map_mulVec_pi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped Kronecker
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnipHaar
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
  [MeasurableSpace (unipRad k e)] [BorelSpace (unipRad k e)] [MeasurableSpace k] [BorelSpace k]
  (ν : Measure k) [ν.IsAddHaarMeasure]
namespace GlobalTheory.SmGL.UnipHaar
theorem _root_.solution :
    (Measure.map (unipHomeo e).symm (Measure.pi fun _ : Idx e => ν)).IsHaarMeasure := by
  haveI := secondCountable k
  haveI := t2Space k
  have hΦ : Measurable (unipHomeo (R := k) e).symm := (unipHomeo e).symm.measurable
  haveI : IsFiniteMeasureOnCompacts (Measure.map (unipHomeo (R := k) e).symm (Measure.pi fun _ : Idx e => ν)) :=
    Measure.IsFiniteMeasureOnCompacts.map _ _
  haveI : (Measure.map (unipHomeo (R := k) e).symm (Measure.pi fun _ : Idx e => ν)).IsOpenPosMeasure :=
    (unipHomeo e).symm.continuous.isOpenPosMeasure_map (unipHomeo e).symm.surjective
  haveI : (Measure.map (unipHomeo (R := k) e).symm (Measure.pi fun _ : Idx e => ν)).IsMulLeftInvariant := by
    refine ⟨fun u => ?_⟩
    have hm : Measurable (lmat e ((u : GL n k) : Matrix n n k)).mulVec :=
      (continuous_const.matrix_mulVec continuous_id).measurable
    have h1 := WeilM.smul_map_mulVec_pi ν _ 1 (det_lmat_unip e u).symm
    rw [map_one, ENNReal.coe_one, one_smul] at h1
    have h2 : (u * ·) ∘ (unipHomeo e).symm = (unipHomeo e).symm ∘ ((unipEquiv e u + ·) ∘
        (lmat e ((u : GL n k) : Matrix n n k)).mulVec) :=
      funext fun x => (unipEquiv e).eq_symm_apply.2 (unipEquiv_mul e u x)
    rw [Measure.map_map (measurable_const_mul u) hΦ, h2,
      ← Measure.map_map hΦ ((measurable_const_add _).comp hm),
      ← Measure.map_map (measurable_const_add _) hm, h1, map_add_left_eq_self]
  exact {}
end GlobalTheory.SmGL.UnipHaar
