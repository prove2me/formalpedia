-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.normVal_vp_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:52:58.051861+00:00
-- url     : https://prove2.me/submissions/7de99dd3-bf36-4330-807b-b5ebd0fb7f14

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_GeneratorValues
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GeneratorValues_IsCentred_log_norm_p_neg

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
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
variable {R : Type} [CommRing R] [IsDomain R]
variable [IsLocalRing R] {F : Type} [NormedField F]
variable {φ : FractionRing R →+* F}
namespace GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
theorem _root_.solution (hφ : IsCentred φ) {p : ℕ} (hp : IsOverPrime R p) :
    (normVal_vp hφ hp).toFun (toUnitK (p : R) hp.ne_zero) = 1 := by
  have e : φ (algebraMap R (FractionRing R) (p : R)) = (p : F) := by simp
  change Real.log ‖φ (algebraMap R (FractionRing R) (p : R))‖ / _ = 1
  rw [e]; exact div_self (hφ.log_norm_p_neg hp).2.ne
end GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
