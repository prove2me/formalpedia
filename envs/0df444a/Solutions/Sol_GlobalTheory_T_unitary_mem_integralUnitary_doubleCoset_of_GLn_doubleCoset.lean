-- Prove2me | solution 1 for GlobalTheory.T.unitary_mem_integralUnitary_doubleCoset_of_GLn_doubleCoset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:25:24.612581+00:00
-- url     : https://prove2.me/submissions/d6788cab-3169-4739-833d-12bd39bdd7aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleC
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitaryMemIntegralUnitaryDoubleCosetOfGLnDoubleCStatement
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_GlobalTheory_UnitaryDoubleCoset_doubleCoset_unitary_of_GL


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (σ : v.adicCompletion K →+* v.adicCompletion K) (n : ℕ), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → (∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) → ∀ g ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)), ∀ g' ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)), ∀ h ∈ GLint (Fin n) (Ov K v), ∀ k ∈ GLint (Fin n) (Ov K v), g' = h * g * k → ∃ k₁ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)) ⊓ GLint (Fin n) (Ov K v), ∃ k₂ ∈ UJ σ (1 : Matrix (Fin n) (Fin n) (v.adicCompletion K)) ⊓ GLint (Fin n) (Ov K v), g' = k₁ * g * k₂ := by
  first | exact @GlobalTheory.UnitaryDoubleCoset.doubleCoset_unitary_of_GL | exact GlobalTheory.UnitaryDoubleCoset.doubleCoset_unitary_of_GL | (intros; apply GlobalTheory.UnitaryDoubleCoset.doubleCoset_unitary_of_GL <;> assumption)
end _root_.GlobalTheory.T
