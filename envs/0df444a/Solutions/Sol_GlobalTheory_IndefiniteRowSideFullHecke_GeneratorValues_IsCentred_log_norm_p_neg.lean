-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsCentred.log_norm_p_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:22.836427+00:00
-- url     : https://prove2.me/submissions/53d23c56-d341-4c35-88f1-21a4c70f1350

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_GeneratorValues

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
namespace IsCentred
theorem _root_.solution (hφ : IsCentred φ) {p : ℕ} (hp : IsOverPrime R p) :
    0 < ‖(p : F)‖ ∧ Real.log ‖(p : F)‖ < 0 := by
  have e : φ (algebraMap R (FractionRing R) (p : R)) = (p : F) := by simp
  have h0 : 0 < ‖(p : F)‖ := by
    rw [← e]; exact norm_pos_iff.2 ((map_ne_zero φ).2 (toUnitK (p : R) hp.ne_zero).ne_zero)
  exact ⟨h0, Real.log_neg h0 (e ▸ hφ.lt_one _ hp.mem)⟩
end IsCentred
end GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues
