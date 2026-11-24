-- Prove2me | solution 1 for GlobalTheory.T.exists_standard_symplectic_basis_of_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:58:05.467798+00:00
-- url     : https://prove2.me/submissions/40f047fa-cb55-4fe5-9aea-cb58e478e207

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsStdSympZmod
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsStdSympZmodStatement
import Theorems.Thm_GlobalTheory_exists_stdSymp_of_alternating_pairing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (M g : ℕ) (G : Type) [CommGroup G] (R : Type) [CommRing R] [IsDomain R] (ζ : Rˣ), 0 < M → IsPrimitiveRoot ζ M → (∀ x : G, x ^ M = 1) → (∀ d : ℕ, d ∣ M → Nat.card {x : G // x ^ d = 1} = d ^ (2 * g)) → ∀ e : G →* G →* Rˣ, (∀ x, e x x = 1) → (∀ x, (∀ y, e x y = 1) → x = 1) → ∃ x : Fin (2 * g) → G, ∀ i j, e (x i) (x j) = ζ ^ stdSymp g i j := by
  first | exact @GlobalTheory.exists_stdSymp_of_alternating_pairing | exact GlobalTheory.exists_stdSymp_of_alternating_pairing | (intros; apply GlobalTheory.exists_stdSymp_of_alternating_pairing <;> assumption)
end _root_.GlobalTheory.T
