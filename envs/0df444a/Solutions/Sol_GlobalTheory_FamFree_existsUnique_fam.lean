-- Prove2me | solution 1 for GlobalTheory.FamFree.existsUnique_fam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:46:03.231249+00:00
-- url     : https://prove2.me/submissions/c339219b-fd7f-4f73-8aa5-eb3472f4b16e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFamOfReps
import Theorems.Thm_GlobalTheory_FamFree_existsUnique_fam_of_reps
import Theorems.Thm_GlobalTheory_FamFree_mk_eq_mk_iff

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
theorem _root_.solution (hG : GlobalFnsSt) (hB : D.TauBimult) {k : ℕ} (hk : 1 ≤ k)
    (rep : D.X ⧸ multiples D k → D.X) (hrep : ∀ c, QuotientAddGroup.mk (rep c) = c)
    (σ : ∀ c, FamSec D F k (rep c)) : ∃! s : Fam D F k, ∀ c, s.s (rep c) = σ c :=
  existsUnique_fam_of_reps hG hB hk rep (fun α => ⟨QuotientAddGroup.mk α, (mk_eq_mk_iff _ _).1 (hrep _),
    fun c hc => (hrep c).symm.trans ((mk_eq_mk_iff _ _).2 hc)⟩) σ
end GlobalTheory.FamFree
