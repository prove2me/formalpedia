-- Prove2me | solution 1 for GlobalTheory.LagSplit.beta_secH_secL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:00:05.822549+00:00
-- url     : https://prove2.me/submissions/28c21132-2001-4864-9b34-ade7fd243c33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_BetaEqZeroOfCharacter
import Theorems.Thm_GlobalTheory_LagSplit_imC_inv
import Theorems.Thm_P2M_GlobalTheory_LagSplit_beta_secH_secL__253c2586de05

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
theorem _root_.solution {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm)
    (hY : IsUnit (τ.map Complex.im).det) (z w : Fin g → ℂ) :
    beta (omegaCx g) (secH τ) (secL g) z w =
      -(2 * I)⁻¹ * (z ⬝ᵥ ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) *ᵥ w) := by
  rw [beta_secH_secL' hτ hY, imC_inv hY]
end GlobalTheory.LagSplit
