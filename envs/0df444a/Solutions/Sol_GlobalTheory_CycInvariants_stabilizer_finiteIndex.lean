-- Prove2me | solution 1 for GlobalTheory.CycInvariants.stabilizer_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:08:51.465272+00:00
-- url     : https://prove2.me/submissions/18ecedec-b0b5-417f-bfe7-81633e3c3440

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerTraceAlmostSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SumMulLeftTransversal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycInvariants
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.CycInvariants
theorem _root_.solution (x : Om l) : (MulAction.stabilizer (GQ l) x).FiniteIndex := by
  refine ⟨?_⟩
  rw [MulAction.index_stabilizer]
  have hint : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hfin : (MulAction.orbit (GQ l) x).Finite := by
    refine ((minpoly ℚ_[l] x).rootSet_finite (Om l)).subset ?_
    rintro _ ⟨g, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    change Polynomial.aeval (g x) _ = 0
    rw [Polynomial.aeval_algEquiv]
    simp
  exact ((Set.ncard_pos hfin).2 ⟨x, MulAction.mem_orbit_self x⟩).ne'
end GlobalTheory.CycInvariants
