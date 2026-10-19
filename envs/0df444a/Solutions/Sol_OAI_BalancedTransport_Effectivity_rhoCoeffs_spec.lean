-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.rhoCoeffs_spec
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:23:34.369692+00:00
-- url     : https://prove2.me/submissions/48b5daaa-1db0-4603-80da-3f603214ff0a

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

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity
open Polynomial
open scoped NNReal
theorem h44_rc (n : ℕ) : ∀ j, (rhoCoeffs n).getD j 0 = (rhoPolynomial n).coeff j := by
  induction n with
  | zero =>
    intro j
    rcases j with _ | j
    · simp [rhoCoeffs, rhoPolynomial]
    · simp [rhoCoeffs, rhoPolynomial, Polynomial.coeff_one]
  | succ n ih =>
    intro j
    simp only [rhoCoeffs, rhoPolynomial, rhoCoeffStep]
    rw [Polynomial.coeff_X_pow_mul']
    rcases j with _ | _ | m
    · simp
    · simp
    · rw [if_pos (by omega), show m + 1 + 1 - 2 = m by omega, Polynomial.coeff_sub,
        Polynomial.coeff_derivative, ← ih, ← ih]
      simp only [List.getD_cons_succ]
      by_cases hm : m < (rhoCoeffs n).length
      · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm]
        simp only [Option.map_some, Option.getD_some]
        push_cast; ring
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega),
          List.getD_eq_default _ _ (by omega)]
        simp

theorem solution (n j : ℕ) : (rhoCoeffs n).getD j 0 = (rhoPolynomial n).coeff j := by
  exact h44_rc n j

