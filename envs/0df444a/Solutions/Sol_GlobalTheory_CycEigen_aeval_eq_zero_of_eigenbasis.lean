-- Prove2me | solution 1 for GlobalTheory.CycEigen.aeval_eq_zero_of_eigenbasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:38:10.721469+00:00
-- url     : https://prove2.me/submissions/e9b9bec4-81f7-4d79-8b60-2e244e7b201a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeBis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AevalProdEqZeroHodgeTateCyclotomicFrame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycEigen
namespace GlobalTheory.CycEigen
theorem _root_.solution {C : Type} [Field C] {r : ℕ} (A : Matrix (Fin r) (Fin r) C)
    (e : Fin r → Fin r → C) (he : LinearIndependent C e) (c : Fin r → C)
    (hc : ∀ k, A.mulVec (e k) = c k • e k) (P : Polynomial C) (hP : ∀ k, P.eval (c k) = 0) :
    Polynomial.aeval A P = 0 := by
  have h1 : ∀ k, (Polynomial.aeval A P).mulVec (e k) = 0 := by
    intro k
    have h2 : Matrix.toLinAlgEquiv' (Polynomial.aeval A P) (e k) = P.eval (c k) • e k := by
      rw [← Polynomial.aeval_algHom_apply]
      exact Module.End.aeval_apply_of_mem_apply_eq_smul (by simpa using hc k)
    rw [hP, zero_smul] at h2
    simpa using h2
  have hsp : Submodule.span C (Set.range e) = ⊤ :=
    he.span_eq_top_of_card_eq_finrank' (by simp)
  have h3 : Matrix.toLin' (Polynomial.aeval A P) = 0 :=
    LinearMap.ext_on_range hsp fun k => by simpa using h1 k
  simpa using h3
end GlobalTheory.CycEigen
