-- Prove2me | solution 1 for GlobalTheory.T.generalLinear_integral_compact_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:50:39.436879+00:00
-- url     : https://prove2.me/submissions/abf2fac6-30b6-42ab-8f44-2ac9dc3b9295

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpenStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_QLTop_gl_topology


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
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n : ℕ, IsOpen (GLint O n : Set (GL (Fin n) F)) ∧ IsCompact (GLint O n : Set (GL (Fin n) F)) ∧ LocallyCompactSpace (GL (Fin n) F) ∧ SecondCountableTopology (GL (Fin n) F) ∧ T2Space (GL (Fin n) F) ∧ IsOpen (Mint O n) ∧ IsClosed (Mint O n) := by
  first | exact @GlobalTheory.CompanionTheory.QLTop.gl_topology | exact GlobalTheory.CompanionTheory.QLTop.gl_topology | (intros; apply GlobalTheory.CompanionTheory.QLTop.gl_topology <;> assumption)
end _root_.GlobalTheory.T
