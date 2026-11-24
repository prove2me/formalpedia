-- Prove2me | solution 1 for GlobalTheory.PerfectPairingCount.right_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:20:55.123958+00:00
-- url     : https://prove2.me/submissions/7baa4488-6528-4325-9ea8-c6288de0cf73

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PerfectPairingOrthogonalOfCard
import Theorems.Thm_GlobalTheory_PerfectPairingCount_card_ker_mul_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PerfectPairingCount
variable {F : Type} [Field F]
variable {A : Type} [CommGroup A] [Finite A]
namespace GlobalTheory.PerfectPairingCount
theorem _root_.solution (E : A →* (A →* Fˣ)) (hE : ∀ a, (∀ b, E a b = 1) → a = 1)
    (b : A) (hb : ∀ a, E a b = 1) : b = 1 := by
  have h := card_ker_mul_le E hE E.flip.ker ⊤ (fun k _ h hh => by
    have := DFunLike.congr_fun (MonoidHom.mem_ker.mp hh) k
    simpa using this)
  rw [Subgroup.card_top] at h
  have hpos : 0 < Nat.card A := Nat.card_pos
  have h1 : Nat.card E.flip.ker ≤ 1 := by
    have : Nat.card A * Nat.card E.flip.ker ≤ Nat.card A * 1 := by simpa using h
    exact Nat.le_of_mul_le_mul_left this hpos
  have h2 : E.flip.ker = ⊥ := Subgroup.card_le_one_iff_eq_bot _ |>.mp h1
  have h3 : b ∈ E.flip.ker := by
    rw [MonoidHom.mem_ker]
    apply MonoidHom.ext
    intro a
    simpa using hb a
  rw [h2] at h3
  exact Subgroup.mem_bot.mp h3
end GlobalTheory.PerfectPairingCount
