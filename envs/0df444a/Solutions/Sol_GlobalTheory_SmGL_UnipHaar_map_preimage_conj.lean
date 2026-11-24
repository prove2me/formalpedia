-- Prove2me | solution 1 for GlobalTheory.SmGL.UnipHaar.map_preimage_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:17:07.863119+00:00
-- url     : https://prove2.me/submissions/42bb115d-c296-4105-b08d-8c72e9f2cb34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_unipEquiv_conj
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_det_cmat
import Theorems.Thm_GlobalTheory_SmGL_UnipHaar_continuous_conj
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
theorem _root_.solution (g : Levi k m) {T : Set (unipRad k e)} (hT : MeasurableSet T) :
    Measure.map (unipHomeo e).symm (Measure.pi fun _ : Idx e => ν) T = ENNReal.ofReal (modulus k m g) *
      Measure.map (unipHomeo e).symm (Measure.pi fun _ : Idx e => ν) (conj e g ⁻¹' T) := by
  haveI := secondCountable k
  haveI := t2Space k
  have hΦ : Measurable (unipHomeo (R := k) e).symm := (unipHomeo e).symm.measurable
  have hm : Measurable (cmat e g).mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  have h1 := WeilM.smul_map_mulVec_pi ν _ _ (det_cmat e g)
  have h2 : conj e g ∘ (unipHomeo e).symm = (unipHomeo e).symm ∘ (cmat e g).mulVec :=
    funext fun x => (unipEquiv e).eq_symm_apply.2 (unipEquiv_conj e g x)
  have hc := (continuous_conj e g).measurable
  rw [← Measure.map_apply hc hT, Measure.map_map hc hΦ, h2, ← Measure.map_map hΦ hm]
  conv_lhs => rw [← h1, Measure.map_smul, Measure.smul_apply, smul_eq_mul]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal]
  simp [modulus, nabs]
end GlobalTheory.SmGL.UnipHaar
