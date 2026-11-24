-- Prove2me | solution 1 for GlobalTheory.JR.Step.embHom_last_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:11:18.104901+00:00
-- url     : https://prove2.me/submissions/68924a11-695f-442a-9d32-bb834ad8c309

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralUnitaryGroupTransitiveNormOneVectorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActLiftHermitianBlockMemIntegralUnitaryMu
import Theorems.Thm_GlobalTheory_UnitaryTransitive_snocZeroLastCoordinate_castSucc
import Theorems.Thm_GlobalTheory_UnitaryTransitive_snocZeroLastCoordinate_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.UnitaryTransitive.snocZeroLastCoordinate_castSucc
attribute [local simp] GlobalTheory.UnitaryTransitive.snocZeroLastCoordinate_last



set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step
variable {r : ℕ} {E : Type} [Field E]
namespace GlobalTheory.JR.Step
theorem _root_.solution (M : Matrix (Fin r) (Fin r) E) (b : Fin r) :
    embHom r E M (Fin.last r) (Fin.castSucc b) = 0 := by
  have ha : finSumFinEquiv.symm (Fin.castSucc b) = (Sum.inl b : Fin r ⊕ Fin 1) :=
    finSumFinEquiv_symm_apply_castSucc b
  have hb : finSumFinEquiv.symm (Fin.last r) = (Sum.inr 0 : Fin r ⊕ Fin 1) := finSumFinEquiv_symm_last
  simp [embHom, Matrix.reindex_apply, Matrix.submatrix_apply, ha, hb]
end GlobalTheory.JR.Step
