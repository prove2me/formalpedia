-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSVerma.dd_yy
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:36.8423+00:00
-- url     : https://prove2.me/submissions/c4f37850-334e-4cf0-940d-9689f1b44a33

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_KummerLiftedCocycleImageEqPicardClass
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSVerma
open CompanionTheory.D.DSIC Formalism.REAL
variable {n : ℕ} {ε : Fin n → Bool}
open MvPolynomial
namespace GlobalTheory.CompanionTheory.DSVerma
theorem _root_.solution (a c : Fin n) (j : NC ε) :
    dd ε a c * yy j - yy j * dd ε a c = if a = j.1.1 ∧ c = j.1.2 then 1 else 0 := by
  classical
  unfold dd yy
  split_ifs with h1 h2 h2
  · refine LinearMap.ext fun f => ?_
    have : j = ⟨(a, c), h1⟩ := Subtype.ext (Prod.ext h2.1.symm h2.2.symm)
    subst this
    simp
  · refine LinearMap.ext fun f => ?_
    have : j ≠ ⟨(a, c), h1⟩ := by
      rintro rfl
      exact h2 ⟨rfl, rfl⟩
    simp [pderiv_X_of_ne this]
  · exact absurd (by rw [h2.1, h2.2]; exact j.2) h1
  · simp
end GlobalTheory.CompanionTheory.DSVerma
