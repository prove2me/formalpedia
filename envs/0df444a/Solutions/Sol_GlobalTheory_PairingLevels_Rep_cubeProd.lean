-- Prove2me | solution 1 for GlobalTheory.PairingLevels.Rep.cubeProd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:26:37.981495+00:00
-- url     : https://prove2.me/submissions/b2447a4d-5b49-4fc1-9801-df589dfa0fb3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsValueEq
import Theorems.Thm_GlobalTheory_PairingLevels_Rep_one
import Theorems.Thm_GlobalTheory_PairingLevels_Rep_mul
import Theorems.Thm_GlobalTheory_PairingLevels_Rep_congr
import Theorems.Thm_GlobalTheory_PairingLevels_Rep_cube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CommutatorPairing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PairingLevels
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] (L : LB A.left)
variable {L} {Y : Over S} {D D' : FreeAbelianGroup (Y.left ⟶ A.left)} {f f' : ValFam L Y}
namespace GlobalTheory.PairingLevels
namespace Rep
theorem _root_.solution [IsCommMonObj A] {t : LB.Gen (Theta A L)} (ht : t.IsGen) (x c : Y ⟶ A) (n : ℕ) :
    Rep L (pt (x ^ n * c) - pt c - pt (x ^ n) + pt (1 : Y ⟶ A) + n • (pt x + pt c - pt (x * c) - pt (1 : Y ⟶ A)))
      (fun Z r z J => ∏ i ∈ Finset.range n, cubeVal t z J ((r ≫ x) ^ i) (r ≫ x) (r ≫ c)) := by
  induction n with
  | zero => exact Rep.one.congr (by simp) (fun _ _ _ _ => by simp)
  | succ n ih =>
    refine (ih.mul (Rep.cube ht (x ^ n) x c)).congr ?_ (fun _ _ _ _ => ?_)
    · rw [pow_succ, succ_nsmul]; abel
    · rw [Finset.prod_range_succ, MonObj.comp_pow]
end Rep
end GlobalTheory.PairingLevels
