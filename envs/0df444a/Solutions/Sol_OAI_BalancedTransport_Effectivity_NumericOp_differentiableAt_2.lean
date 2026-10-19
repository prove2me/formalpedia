-- Prove2me | solution 2 for OAI.BalancedTransport.Effectivity.NumericOp.differentiableAt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:46:23.291922+00:00
-- url     : https://prove2.me/submissions/b683c3c4-a1c5-44e5-8723-8b0013a96772

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/NumericDifferentiation.lean:L97-L112
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Effectivity.NumericOp.differentiableAt. The node keeps its source
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
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.FlatBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity
open Polynomial

lemma rhoJet_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (rhoJet n) (rhoJet (n + 1) x) x := by
  unfold rhoJet
  have h := expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul
    ((rhoPolynomial n).map (Int.castRingHom ℝ)) x
  simpa [rhoJet, rhoPolynomial, ← Polynomial.eval₂_eq_eval_map,
    Polynomial.derivative_map] using h

end BalancedTransport.Effectivity
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericDifferentiation ----
namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.NumericOp
variable (d : ℕ) [NeZero d]

lemma differentiableAt (o : NumericOp) (x : Fin d → ℝ)
    (s : (Fin d → ℝ) → List ℝ)
    (hs : ∀ a, DifferentiableAt ℝ (fun y => (s y).getD a 0) x)
    (hv : o.Valid (s x)) : DifferentiableAt ℝ (fun y => o.real d y (s y)) x := by
  rcases o with ⟨j,r,a,b⟩
  fin_cases j <;> dsimp only [real, tag, rat, left, right, Valid] at hv ⊢
  · exact differentiableAt_const _
  · exact (differentiable_apply _).differentiableAt
  · exact (hs a).add (hs b)
  · exact (hs a).mul (hs b)
  · exact (hs a).neg
  · have hh : (s x).getD a 0 ≠ 0 := ne_of_gt ((by positivity : (0 : ℝ) < ((b+1 : ℕ) : ℝ)⁻¹).trans_le (hv rfl))
    exact (hs a).inv hh
  · exact (rhoJet_hasDerivAt a _).differentiableAt.comp x (hs b)
  · exact (hs a).exp
  · exact differentiableAt_const _

end BalancedTransport.Effectivity.NumericOp
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity OAI.BalancedTransport.Effectivity.NumericOp


theorem solution : type_of% @_root_.OAI.BalancedTransport.Effectivity.NumericOp.differentiableAt := @_root_.OAI.BalancedTransport.Effectivity.NumericOp.differentiableAt
