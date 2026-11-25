-- Prove2me | solution 1 for GlobalTheory.TorsionCompare.isOriginChart_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:25:53.615243+00:00
-- url     : https://prove2.me/submissions/cab8808c-08b9-4354-9b32-81aca3c6597a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_OriginChartMultiplication
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NotIsUnitNatCastOfIsLocalHom
import Theorems.Thm_GlobalTheory_TorsionCompare_isChartJ_iff

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
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionCompare
variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G]
variable {d : ℕ}
namespace GlobalTheory.TorsionCompare
theorem _root_.solution (F : FGLaw R d) (x : ∀ m : ℕ, algOver R (JetR R (Fin d) m) ⟶ G) :
    IsOriginChart G x F ↔ IsChartJ G F ((chartEquiv G d).symm x) := by
  rw [isChartJ_iff, Equiv.apply_symm_apply]
end GlobalTheory.TorsionCompare
