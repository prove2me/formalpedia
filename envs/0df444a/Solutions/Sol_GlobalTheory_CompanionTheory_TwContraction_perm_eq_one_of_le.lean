-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TwContraction.perm_eq_one_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:42:47.582512+00:00
-- url     : https://prove2.me/submissions/cad037bc-60b0-480b-930d-7bf987962c82

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistedIwahoriContractionHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Tf.Loc Matrix ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwContraction
variable {F : Type*} [Field F] [ValuativeRel F] {n : ℕ}
namespace GlobalTheory.CompanionTheory.TwContraction
theorem _root_.solution (π : Equiv.Perm (Fin n)) (h : ∀ i, π i ≤ i) : π = 1 := by
  have key : ∀ m : ℕ, ∀ i : Fin n, (i : ℕ) = m → π i = i := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro i hi
      refine le_antisymm (h i) ?_
      by_contra hlt
      have hlt' : π i < i := not_le.mp hlt
      have h2 : π (π i) = π i := ih (π i) (by rw [← hi]; exact hlt') _ rfl
      exact hlt'.ne (π.injective h2)
  exact Equiv.ext fun i => key i i rfl
end GlobalTheory.CompanionTheory.TwContraction
