-- Prove2me | solution 1 for GlobalTheory.Cartier.IsRegularFn.associated_of_dvd_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:09:28.146051+00:00
-- url     : https://prove2.me/submissions/a49f4e5a-93c9-45ea-9c52-ec91e0eb8f0a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mul_right_cancel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.Cartier
namespace IsRegularFn
theorem _root_.solution {U : X.Opens} {a b : Γ(X, U)} (ha : IsRegularFn a)
    (h₁ : a ∣ b) (h₂ : b ∣ a) : Associated a b := by
  obtain ⟨c, rfl⟩ := h₁
  obtain ⟨d, hd⟩ := h₂
  have : c * d = 1 := ha.mul_right_cancel (by rw [one_mul]; linear_combination -hd)
  exact ⟨Units.mkOfMulEqOne c d this, rfl⟩
end IsRegularFn
end GlobalTheory.Cartier
