-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FinGLChar.trace_infl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:08:40.837952+00:00
-- url     : https://prove2.me/submissions/4fcdd4c6-7a41-4fb7-bf17-148da930c52f

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TraceCompLeftFunLeft
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_FrobeniusSumFormula
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraCharacter
import Theorems.Thm_PI_SerBridgeGLW_trace_piTensorMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinGLChar
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {s : ℕ} (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
namespace GlobalTheory.CompanionTheory.FinGLChar
theorem _root_.solution (p : parab K b) :
    LinearMap.trace ℂ (PiTensorProduct ℂ fun c => (lam c : Type)) (infl K b lam p) =
      hcFun b (fun c => (lam c).character) p.1 := by
  unfold hcFun infl
  rw [PI.SerBridgeGLW.trace_piTensorMap]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [blkGL, dif_pos p.2]
  rfl
end GlobalTheory.CompanionTheory.FinGLChar
