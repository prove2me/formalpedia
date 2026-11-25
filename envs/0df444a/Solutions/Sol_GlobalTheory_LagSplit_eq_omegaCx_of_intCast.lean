-- Prove2me | solution 1 for GlobalTheory.LagSplit.eq_omegaCx_of_intCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:06:50.342002+00:00
-- url     : https://prove2.me/submissions/f0bd71b2-29ca-4750-b15b-ea39f1783c07

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_BetaEqZeroOfCharacter
import Theorems.Thm_GlobalTheory_LagSplit_omegaCx_intCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Key.Chi
open GlobalTheory GlobalTheory.LagSplit
variable {g : ℕ}
namespace GlobalTheory.LagSplit
theorem _root_.solution (B : LinearMap.BilinForm ℂ (Fin g ⊕ Fin g → ℂ))
    (hB : ∀ a b : Fin g ⊕ Fin g → ℤ,
      B (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) = (omegaStd a b : ℂ)) : B = omegaCx g := by
  classical
  refine LinearMap.BilinForm.ext_basis (Pi.basisFun ℂ _) fun i j => ?_
  have e : ∀ i : Fin g ⊕ Fin g, Pi.basisFun ℂ (Fin g ⊕ Fin g) i =
      fun k => (((Pi.single i 1 : Fin g ⊕ Fin g → ℤ) k : ℤ) : ℂ) := by
    intro i; ext k; simp [Pi.single_apply]
  rw [e, e, hB, omegaCx_intCast]
end GlobalTheory.LagSplit
