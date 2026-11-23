-- Prove2me | solution 1 for GlobalTheory.JR.Step.embHom_castSucc_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:08.414746+00:00
-- url     : https://prove2.me/submissions/f57ac672-04b5-4889-b931-fdfd14ca7c65

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
theorem _root_.solution (M : Matrix (Fin r) (Fin r) E) (a b : Fin r) :
    embHom r E M (Fin.castSucc a) (Fin.castSucc b) = M a b := by
  have ha : finSumFinEquiv.symm (Fin.castSucc a) = (Sum.inl a : Fin r ⊕ Fin 1) :=
    finSumFinEquiv_symm_apply_castSucc a
  have hb : finSumFinEquiv.symm (Fin.castSucc b) = (Sum.inl b : Fin r ⊕ Fin 1) :=
    finSumFinEquiv_symm_apply_castSucc b
  simp [embHom, Matrix.reindex_apply, Matrix.submatrix_apply, ha, hb]
end GlobalTheory.JR.Step
