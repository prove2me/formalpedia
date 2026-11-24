-- Prove2me | solution 1 for GlobalTheory.SmGL.UnitInd.isMulRightInvariant_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:05:19.733783+00:00
-- url     : https://prove2.me/submissions/a9e1eaa7-28ca-4140-9eb3-f79555b72e79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Theorems.Thm_GlobalTheory_SmGL_UnitInd_det_rmat_unip
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_ent_mat_mul
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field
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
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
open GlobalTheory.SplitFlip GlobalTheory.SmGL.UnipHaar
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
variable [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.SmGL.UnitInd
theorem _root_.solution (ν : Measure k) [ν.IsAddHaarMeasure] :
    (Measure.map (unipHomeo (R := k) e).symm (Measure.pi fun _ : Idx e => ν)).IsMulRightInvariant := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have hΦ : Measurable (unipHomeo (R := k) e).symm := (unipHomeo e).symm.measurable
  refine ⟨fun u => ?_⟩
  have hm : Measurable (rmat e ((u : GL n k) : Matrix n n k)).mulVec :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  have h1 := WeilM.smul_map_mulVec_pi ν _ 1 (det_rmat_unip e u).symm
  rw [map_one, ENNReal.coe_one, one_smul] at h1
  have h2 : (· * u) ∘ (unipHomeo e).symm = (unipHomeo e).symm ∘ ((unipEquiv e u + ·) ∘
      (rmat e ((u : GL n k) : Matrix n n k)).mulVec) :=
    funext fun x => (unipEquiv e).eq_symm_apply.2 (by
      show ent e ((1 + mat e x) * ((u : GL n k) : Matrix n n k)) = unipEquiv e u + (rmat e _).mulVec x
      rw [← ent_mat_mul, add_mul, one_mul]
      rfl)
  rw [Measure.map_map (measurable_mul_const u) hΦ, h2,
    ← Measure.map_map hΦ ((measurable_const_add _).comp hm),
    ← Measure.map_map (measurable_const_add _) hm, h1, map_add_left_eq_self]
end GlobalTheory.SmGL.UnitInd
