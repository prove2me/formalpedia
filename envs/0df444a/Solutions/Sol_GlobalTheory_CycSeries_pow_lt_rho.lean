-- Prove2me | solution 1 for GlobalTheory.CycSeries.pow_lt_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:41:02.496379+00:00
-- url     : https://prove2.me/submissions/a349b9f1-41cd-4c77-928d-1b790708ac26

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegersStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTateOperatorLevelComplement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormZpowSubOneLeTer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.CycSeries
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.CycSeries
theorem _root_.solution {j : ℕ} (hj : Lev l j) : (l : ℝ) ^ (-(j : ℤ)) < rho1 l := by
  have h2 : 2 ≤ l := hl.1.two_le
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.1.one_lt
  rw [rho1, ← Real.rpow_intCast]
  apply Real.rpow_lt_rpow_of_exponent_lt h1
  rw [lt_div_iff₀ (by linarith)]
  push_cast
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj.1
  rcases h2.eq_or_lt with h | h
  · have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast hj.2 h.symm
    have : (l : ℝ) = 2 := by exact_mod_cast h.symm
    rw [this]; linarith
  · have : (3 : ℝ) ≤ l := by exact_mod_cast h
    nlinarith
end GlobalTheory.CycSeries
