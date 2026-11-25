-- Prove2me | solution 1 for GlobalTheory.ConstFam.sval_pullThrough
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:49:53.812335+00:00
-- url     : https://prove2.me/submissions/b1b009d2-7149-4b48-87ef-075268f4cbeb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Theorems.Thm_GlobalTheory_ConstFam_secThrough_pullThrough

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.ConstFam
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange
variable {X X' Y Y' Z : Scheme.{0}}
variable {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
variable {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
variable {R R' : Type} [CommRing R] [CommRing R'] {π : Y ⟶ Spec (CommRingCat.of R)}
  {π' : Y' ⟶ Spec (CommRingCat.of R')} {f : R →+* R'}
variable (hw : w.IsGen) (hL : L.IsLB) (hL' : L'.IsLB) (hψ : ∀ k, φ' k ≫ F = h ≫ φ k)
  (hp : h ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f))
namespace GlobalTheory.ConstFam
theorem _root_.solution (t : SecOver π (LB.LinComb L φ ε)) (r : Z ⟶ Y') {z : Z} {J J'} (hJ : Good L z J)
    (hJ' : Good L' z J') : sval t (r ≫ h) z J =
      (∏ k, wVal w z J J' (r ≫ φ' k) ^ ε k).val * sval (pullThrough hw hL hL' hψ ε hp t) r z J' :=
  (secThrough_pullThrough hw hL hL' hψ hp t).sval hψ r hJ hJ'
end GlobalTheory.ConstFam
