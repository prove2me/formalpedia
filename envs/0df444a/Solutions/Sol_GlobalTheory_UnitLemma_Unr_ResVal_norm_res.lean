-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Unr.ResVal.norm_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:05:14.357723+00:00
-- url     : https://prove2.me/submissions/d469f6d1-adaf-4d69-bc83-01c176ce3f37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SeparableCharpolyInvAlgBaseChangeUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerMapIsIntegralUnramifiedInvolutionExStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrFractionFieldAddValNormUnramifiedLocalExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueGeneratesUnramifiedExtResidueFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotIsRootResidueCofactorUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValResultantEqDegreeMulUnramifiedExt
import Theorems.Thm_GlobalTheory_TraceDetSplit_charpoly_leftMul_basis
import Theorems.Thm_GlobalTheory_TraceDetSplit_det_aeval


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.ResVal
namespace GlobalTheory.UnitLemma.Unr.ResVal
theorem _root_.solution {E A : Type} [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A) (p : E[X])
    (hp : p.Monic) : ∃ k : ℕ, Algebra.norm E (aeval g p) = (-1) ^ k * resultant p (LinearMap.mulLeft E g).charpoly := by
  let u := Module.finBasis E A
  have h := GlobalTheory.TraceDetSplit.det_aeval (Algebra.leftMulMatrix u g) p hp
  rw [GlobalTheory.TraceDetSplit.charpoly_leftMul_basis, aeval_algHom_apply, ← Algebra.norm_eq_matrix_det] at h
  exact ⟨_, h⟩
end GlobalTheory.UnitLemma.Unr.ResVal
