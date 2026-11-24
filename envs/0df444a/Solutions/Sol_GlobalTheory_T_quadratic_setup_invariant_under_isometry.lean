-- Prove2me | solution 1 for GlobalTheory.T.quadratic_setup_invariant_under_isometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:21:09.831562+00:00
-- url     : https://prove2.me/submissions/39eea2d8-2789-42e5-a4a4-c21fdb3cf5f3

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuadraticSetupInvariantUnderIsometry
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuadraticSetupInvariantUnderIsometryStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_qsetup_conj_majorant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ) (gi : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → (∀ w, (gi w)ᵀ * B.map (ρ w) * gi w = B.map (ρ w)) → QSetup M B ρ (fun w => (gi w)ᵀ * P w * gi w) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.qsetup_conj_majorant | exact GlobalTheory.CompanionTheory.SW.ThW.qsetup_conj_majorant | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.qsetup_conj_majorant <;> assumption)
end _root_.GlobalTheory.T
