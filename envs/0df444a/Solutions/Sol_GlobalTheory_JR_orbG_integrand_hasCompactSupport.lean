-- Prove2me | solution 1 for GlobalTheory.JR.orbG_integrand_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:17:44.781469+00:00
-- url     : https://prove2.me/submissions/138dbd40-657e-4392-97ac-1008cd2f8e07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HasCompactSupportJacquetRallisOrbitalIntegrand
import Theorems.Thm_GlobalTheory_JR_GLCompact_Bm_act
import Theorems.Thm_GlobalTheory_JR_GLCompact_continuous_Bm
import Theorems.Thm_GlobalTheory_JR_GLCompact_continuous_Cm
import Theorems.Thm_GlobalTheory_JR_TransferFactor_Cm_act
import Theorems.Thm_GlobalTheory_T_jacquetRallis_borderedMatrix_normalForm_invariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.JR.GLCompact
end GlobalTheory.JR.GLCompact
private theorem isCompact_unit_box (F : Type) [NontriviallyNormedField F] [ProperSpace F] (n : ℕ) :
    IsCompact {Z : Gl n F | (∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧
      ‖Z.2.2.2‖ ≤ 1} := by
  have hv : IsCompact (Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1) :=
    isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hm : IsCompact {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ 1} := by
    have h : {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ 1} =
        Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1 := by
      ext A
      exact ⟨fun h i _ j _ => by simpa using h i j,
        fun h i j => by simpa using h i (Set.mem_univ i) j (Set.mem_univ j)⟩
    rw [h]
    exact isCompact_univ_pi fun _ => hv
  have h : {Z : Gl n F | (∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧
      ‖Z.2.2.2‖ ≤ 1} = {A : Matrix (Fin n) (Fin n) F | ∀ i j, ‖A i j‖ ≤ 1} ×ˢ
        ((Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1) ×ˢ
          ((Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : F) 1) ×ˢ Metric.closedBall (0 : F) 1)) := by
    ext Z; simp
  rw [h]
  exact hm.prod (hv.prod (hv.prod (isCompact_closedBall 0 1)))
end

set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.JR
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F] (n : ℕ) (Y : Gl n F), Delta (inv Y) ≠ 0 → HasCompactSupport (fun g : GL (Fin n) F => unitG n F (act g Y) * omega (act g Y)) := by
  intro F _ _ n Y hY
  have : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨-, -, hCB, -, -⟩ := GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants F n
  have hdet : (Cm Y).det * (Bm Y).det ≠ 0 := by
    rw [← Matrix.det_mul, hCB Y]
    exact hY
  have hB : IsUnit (Bm Y).det := isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul hdet)
  have hC : IsUnit (Cm Y).det := isUnit_iff_ne_zero.mpr (left_ne_zero_of_mul hdet)

  have hψ : Continuous (fun Z : Gl n F =>
      (Bm Z * (Bm Y)⁻¹, MulOpposite.op ((Cm Y)⁻¹ * Cm Z))) :=
    (GlobalTheory.JR.GLCompact.continuous_Bm.matrix_mul continuous_const).prodMk
      (MulOpposite.continuous_op.comp (continuous_const.matrix_mul GlobalTheory.JR.GLCompact.continuous_Cm))
  have hK := Units.isClosedEmbedding_embedProduct.isCompact_preimage
    ((isCompact_unit_box F n).image hψ)
  refine HasCompactSupport.intro hK ?_
  intro g hg
  have hgY : act g Y ∉ {Z : Gl n F | (∀ i j, ‖Z.1 i j‖ ≤ 1) ∧ (∀ i, ‖Z.2.1 i‖ ≤ 1) ∧
      (∀ i, ‖Z.2.2.1 i‖ ≤ 1) ∧ ‖Z.2.2.2‖ ≤ 1} := by
    intro hmem
    refine hg ⟨act g Y, hmem, Prod.ext ?_ ?_⟩
    · show Bm (act g Y) * (Bm Y)⁻¹ = (g : Matrix (Fin n) (Fin n) F)
      rw [GlobalTheory.JR.GLCompact.Bm_act, Matrix.mul_nonsing_inv_cancel_right _ _ hB]
    · show MulOpposite.op ((Cm Y)⁻¹ * Cm (act g Y)) =
        MulOpposite.op ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      rw [GlobalTheory.JR.TransferFactor.Cm_act, Matrix.nonsing_inv_mul_cancel_left _ _ hC]
  have h0 : unitG n F (act g Y) = 0 := Set.indicator_of_notMem hgY _
  simp [h0]
end GlobalTheory.JR
