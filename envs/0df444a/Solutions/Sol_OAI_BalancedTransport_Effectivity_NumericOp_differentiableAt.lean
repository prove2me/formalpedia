-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.NumericOp.differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:27:59.354049+00:00
-- url     : https://prove2.me/submissions/7df6ff8a-9f61-4586-b5a1-a52e146c2ae5

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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity OAI.BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]
theorem h44_rhoJet_eq (n : ℕ) : rhoJet n = fun x =>
    ((rhoPolynomial n).map (Int.castRingHom ℝ)).eval x⁻¹ * expNegInvGlue x := by
  funext x; simp only [rhoJet, Polynomial.eval₂_eq_eval_map]

theorem h44_rho_hasDeriv (n : ℕ) (x : ℝ) : HasDerivAt (rhoJet n) (rhoJet (n+1) x) x := by
  rw [h44_rhoJet_eq n]
  have := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
    ((rhoPolynomial n).map (Int.castRingHom ℝ)) x
  convert this using 1
  simp only [rhoJet, rhoPolynomial, Polynomial.eval₂_eq_eval_map, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub, Polynomial.derivative_map]

theorem solution (o : NumericOp) (x : Fin d → ℝ)
    (s : (Fin d → ℝ) → List ℝ)
    (hs : ∀ a, DifferentiableAt ℝ (fun y => (s y).getD a 0) x)
    (hv : o.Valid (s x)) : DifferentiableAt ℝ (fun y => o.real d y (s y)) x := by
  rcases o with ⟨tg, q, a, b⟩
  fin_cases tg <;> simp only [real, tag, left, right, rat, Valid] at hv ⊢
  · exact differentiableAt_const _
  · exact (differentiableAt_pi.1 differentiableAt_id) _
  · exact (hs a).add (hs b)
  · exact (hs a).mul (hs b)
  · exact (hs a).neg
  · have hp : (0:ℝ) < ((b + 1 : ℕ) : ℝ)⁻¹ := by positivity
    have hne : (s x).getD a 0 ≠ 0 := (lt_of_lt_of_le hp (hv rfl)).ne'
    exact (hs a).inv hne
  · exact (h44_rho_hasDeriv a _).differentiableAt.comp x (hs b)
  · exact (hs a).exp
  · exact differentiableAt_const _

