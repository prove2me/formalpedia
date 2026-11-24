-- Prove2me | solution 1 for GlobalTheory.T.mem_integralGL_iff_integral_unit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:27:10.966057+00:00
-- url     : https://prove2.me/submissions/6b6e9ccf-e723-48d0-b399-3f9959a6d7fe

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDet
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_QLDet_mem_GLint_iff


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
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (g : GL (Fin n) F), g ∈ GLint O n ↔ (IsInt O (g : Matrix (Fin n) (Fin n) F) ∧ nrm (g : Matrix (Fin n) (Fin n) F).det = 1) := by
  first | exact @GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff | exact GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff | (intros; apply GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff <;> assumption)
end _root_.GlobalTheory.T
