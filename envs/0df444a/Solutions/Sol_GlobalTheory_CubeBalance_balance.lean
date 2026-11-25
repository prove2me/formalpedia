-- Prove2me | solution 1 for GlobalTheory.CubeBalance.balance
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:41:59.10801+00:00
-- url     : https://prove2.me/submissions/64c5fba2-8f64-43c1-a3cb-843886f611fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CubNSucc
import Theorems.Thm_GlobalTheory_CubeBalance_cubN_add
import Theorems.Thm_GlobalTheory_CubeBalance_cubN_mul
import Theorems.Thm_GlobalTheory_CubeBalance_cubN_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.CubeBalance
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}
namespace GlobalTheory.CubeBalance
theorem _root_.solution : ∀ (A U : Type) [CommGroup A] [CommGroup U] (θ : A → A → A → U), IsCub θ → ∀ (a b : ℕ) (x y : A), cubN θ (a * b) 1 x y = cubN θ a 1 (x ^ b) y * cubN θ b 1 x y ^ a ∧ cubN θ a 1 x (y ^ b) * cubN θ b 1 y x ^ a = cubN θ b 1 y (x ^ a) * cubN θ a 1 x y ^ b ∧ cubN θ (a + b) 1 x y = θ (x ^ a) (x ^ b) y * cubN θ a 1 x y * cubN θ b 1 x y :=
  fun _ _ _ _ _ h a b x y => ⟨cubN_mul h a b x y, cubN_swap h a b x y, cubN_add h a b x y⟩
end GlobalTheory.CubeBalance
