-- Prove2me | solution 1 for OAI.BalancedTransport.Effectivity.NumericOp.hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:28:56.590101+00:00
-- url     : https://prove2.me/submissions/316d2bb3-1ffb-4f05-a3b5-5f672c7ddf78

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

theorem solution (k : Fin d) (o : NumericOp) (x : ℝ → Fin d → ℝ)
    (s : ℝ → List ℝ) (v : ℕ → ℝ) (t : ℝ)
    (hx : ∀ i, HasDerivAt (fun t => x t i) (if i = k then 1 else 0) t)
    (hs : ∀ a, HasDerivAt (fun t => (s t).getD a 0) (v a) t)
    (hv : o.Valid (s t)) :
    HasDerivAt (fun t => o.real d (x t) (s t))
      (o.differential d k (fun a => (s t).getD a 0) v) t := by
  rcases o with ⟨tg, q, a, b⟩
  fin_cases tg <;> simp only [real, differential, tag, left, right, rat, Valid] at hv ⊢
  · exact hasDerivAt_const _ _
  · exact hx _
  · exact (hs a).add (hs b)
  · exact (hs a).mul (hs b)
  · exact (hs a).neg
  · have hp : (0:ℝ) < ((b + 1 : ℕ) : ℝ)⁻¹ := by positivity
    have hne : (s t).getD a 0 ≠ 0 := (lt_of_lt_of_le hp (hv rfl)).ne'
    refine ((hs a).inv hne).congr_deriv ?_
    rw [inv_pow, div_eq_mul_inv, neg_mul]
  · exact (h44_rho_hasDeriv a _).comp t (hs b)
  · exact (hs a).exp
  · exact hasDerivAt_const _ _

