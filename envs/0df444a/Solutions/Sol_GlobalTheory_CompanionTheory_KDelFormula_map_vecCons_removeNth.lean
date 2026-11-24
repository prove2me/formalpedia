-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KDelFormula.map_vecCons_removeNth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:40:49.047363+00:00
-- url     : https://prove2.me/submissions/91db89a1-5a2e-4e1c-a702-80436f99e104

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RemoveNthSuccVecCons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Cz Fin Function
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KDelFormula
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]
namespace GlobalTheory.CompanionTheory.KDelFormula
theorem _root_.solution {n : ℕ} (η : P [⋀^Fin (n + 1)]→ₗ[ℝ] M) (x : P)
    (Y : Fin (n + 1) → P) (t : Fin (n + 1)) :
    η (Matrix.vecCons x (t.removeNth Y)) = (-1 : ℤ) ^ (t : ℕ) • η (Function.update Y t x) := by
  have hW : Matrix.vecCons x (t.removeNth Y) = Function.update Y t x ∘ t.cycleRange.symm := by
    rw [← Fin.cons_removeNth_eq_comp_cycleRange_symm]
    simp only [Function.update_self, Fin.removeNth_update]
    rfl
  rw [hW, η.map_perm, Equiv.Perm.sign_symm, Fin.sign_cycleRange, Units.smul_def]
  push_cast
  rfl
end GlobalTheory.CompanionTheory.KDelFormula
