-- Prove2me | solution 1 for GlobalTheory.FamFree.exists_fam_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:28:53.604813+00:00
-- url     : https://prove2.me/submissions/7bb79df0-706a-454e-a7c5-a9a686c7c203

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Theorems.Thm_GlobalTheory_FamFree_add_nsmul_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_UUA_exists_fam_rep


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FamFree
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.FamFree
theorem _root_.solution (hG : GlobalFnsSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) (ρ : D.X)
    (σ : FamSec D F k ρ) :
    ∃ s : Fam D F k, s.s ρ = σ ∧ ∀ β : D.X, (∀ mu, ρ + k • mu ≠ β) → ∀ j, (s.s β).f j = 0 :=
  UUA.exists_fam_rep hG hB k ρ (add_nsmul_inj hk ρ) σ
end GlobalTheory.FamFree
