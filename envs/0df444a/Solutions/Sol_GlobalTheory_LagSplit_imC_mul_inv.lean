-- Prove2me | solution 1 for GlobalTheory.LagSplit.imC_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:50:51.593711+00:00
-- url     : https://prove2.me/submissions/5296c1ef-cb8a-4c11-b760-10fe4bedb9ec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_BetaEqZeroOfCharacter

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
theorem _root_.solution {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det) :
    imC τ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) = 1 := by
  have h := congrArg (fun A : Matrix (Fin g) (Fin g) ℝ => A.map Complex.ofRealHom)
    (Matrix.mul_nonsing_inv _ hY)
  simp only [Matrix.map_mul] at h
  rw [Matrix.map_one _ (by simp) (by simp)] at h
  exact h
end GlobalTheory.LagSplit
