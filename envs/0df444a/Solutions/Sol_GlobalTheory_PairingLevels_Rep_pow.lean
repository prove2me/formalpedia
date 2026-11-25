-- Prove2me | solution 1 for GlobalTheory.PairingLevels.Rep.pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:33:53.733202+00:00
-- url     : https://prove2.me/submissions/d313d196-5cfb-4eae-972e-21b05c42216b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsValueEq
import Theorems.Thm_GlobalTheory_PairingLevels_Rep_one
import Theorems.Thm_GlobalTheory_PairingLevels_Rep_mul
import Theorems.Thm_GlobalTheory_PairingLevels_Rep_congr

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
omit [GrpObj A]
namespace GlobalTheory.PairingLevels
namespace Rep
theorem _root_.solution (h : Rep L D f) (n : ℕ) : Rep L (n • D) (fun Z r z J => f Z r z J ^ n) := by
  induction n with
  | zero => exact Rep.one.congr (zero_smul _ _).symm (fun _ _ _ _ => (pow_zero _).symm)
  | succ n ih => exact (ih.mul h).congr (succ_nsmul _ _).symm (fun _ _ _ _ => (pow_succ _ _).symm)
end Rep
end GlobalTheory.PairingLevels
