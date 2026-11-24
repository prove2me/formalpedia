-- Prove2me | solution 1 for GlobalTheory.T.latticeCount_and_gramDetSign_norm_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:50:03.815002+00:00
-- url     : https://prove2.me/submissions/696e3810-05a9-49c4-ba59-0f6a4c344997

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountAndGramDetSignNormClass
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LatticeCountAndGramDetSignNormClassStatement
import Theorems.Thm_GlobalTheory_UnitLemma_NormClass_N_norm_class


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : UQ) (B : InvAlg K) (x : B.A) (u : B.Aˣ), B.N (x * (u * B.σ (u : B.A))) = B.N x ∧ K.eta (B.gramDet (x * (u * B.σ (u : B.A)))) = K.eta (B.gramDet x) := by
  first | exact @GlobalTheory.UnitLemma.NormClass.N_norm_class | exact GlobalTheory.UnitLemma.NormClass.N_norm_class | (intros; apply GlobalTheory.UnitLemma.NormClass.N_norm_class <;> assumption)
end _root_.GlobalTheory.T
