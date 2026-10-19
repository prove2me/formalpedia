-- Prove2me | solution 2 for OAI.BalancedTransport.Effectivity.rhoCoeffs_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:31:48.717451+00:00
-- url     : https://prove2.me/submissions/43abec69-6bb3-4860-863c-03387a5b469e

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RhoAlgorithms.lean:L63-L76
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.rhoCoeffs_spec. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RhoAlgorithms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Polynomial
open scoped NNReal

lemma getD_zero_of_length_le {cs : List ℤ} {j : ℕ} (h : cs.length ≤ j) :
    cs.getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma rhoCoeffStep_getD (cs : List ℤ) (j : ℕ) :
    (rhoCoeffStep cs).getD (j + 2) 0 =
      cs.getD j 0 - (j + 1 : ℤ) * cs.getD (j + 1) 0 := by
  simp only [rhoCoeffStep, List.getD_cons_succ]
  by_cases hj : j < cs.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  · have hj' : cs.length ≤ j := le_of_not_gt hj
    rw [getD_zero_of_length_le (by simpa using hj'), getD_zero_of_length_le hj',
      getD_zero_of_length_le (by omega)]
    simp

lemma rhoCoeffs_spec (n j : ℕ) : (rhoCoeffs n).getD j 0 = (rhoPolynomial n).coeff j := by
  induction n generalizing j with
  | zero =>
    cases j <;> simp [rhoCoeffs, rhoPolynomial, List.getD_eq_getElem?_getD, coeff_one]
  | succ n ih =>
    cases j with
    | zero => simp [rhoCoeffs, rhoCoeffStep, rhoPolynomial]
    | succ j =>
      cases j with
      | zero => simp [rhoCoeffs, rhoCoeffStep, rhoPolynomial, coeff_X_pow_mul']
      | succ j =>
        rw [show j + 1 + 1 = j + 2 by omega, rhoCoeffs, rhoCoeffStep_getD,
          rhoPolynomial, coeff_X_pow_mul, coeff_sub, coeff_derivative, ← ih, ← ih]
        ring

end BalancedTransport.Effectivity
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open Polynomial
open scoped NNReal


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.rhoCoeffs_spec := @_root_.OAI.BalancedTransport.Effectivity.rhoCoeffs_spec
