-- Prove2me | solution 1 for GlobalTheory.FamFree.exists_fam_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:35:39.038486+00:00
-- url     : https://prove2.me/submissions/b34b41f1-9b52-4645-9938-2bd6d2882022

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Theorems.Thm_GlobalTheory_FamFree_zero_add_nsmul_iff
import Theorems.Thm_GlobalTheory_FamFree_exists_fam_single
import Theorems.Thm_GlobalTheory_FamFree_exists_sec_ne_zero

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
theorem _root_.solution (hG : GlobalFnsSt) (hT : SecTwistSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k) (α : D.X) :
    ∃ s : Fam D F k, ∀ β : D.X, (¬ ∀ j, (s.s β).f j = 0) ↔ ∃ mu, α + k • mu = β := by
  obtain ⟨σ, hσ⟩ := exists_sec_ne_zero (D := D) (F := F) hT hk α
  obtain ⟨s, rfl, hs⟩ := exists_fam_single hG hB hk α σ
  refine ⟨s, fun β => ⟨fun h => by_contra fun hn => h (hs β fun mu e => hn ⟨mu, e⟩), ?_⟩⟩
  rintro ⟨mu, rfl⟩ h
  exact hσ ((zero_add_nsmul_iff hG s α mu).1 h)
end GlobalTheory.FamFree
