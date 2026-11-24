-- Prove2me | solution 1 for GlobalTheory.T.localField_topology_norm_balls
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:32:21.482375+00:00
-- url     : https://prove2.me/submissions/40fcc4da-3bf1-4fbd-8d14-8384494c50c7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBalls
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBallsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_QLTop_localField_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → IsOpen (O : Set F) ∧ IsCompact (O : Set F) ∧ SecondCountableTopology F ∧ Continuous (fun x : F => nrm x) ∧ (∀ e : ℤ, IsOpen {x : F | nrm x ≤ (q : ℝ) ^ e}) ∧ (∀ s ∈ nhds (0 : F), ∃ e : ℤ, {x : F | nrm x ≤ (q : ℝ) ^ e} ⊆ s) := by
  first | exact @GlobalTheory.CompanionTheory.QLTop.localField_top | exact GlobalTheory.CompanionTheory.QLTop.localField_top | (intros; apply GlobalTheory.CompanionTheory.QLTop.localField_top <;> assumption)
end _root_.GlobalTheory.T
