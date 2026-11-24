-- Prove2me | solution 1 for GlobalTheory.VeryAmplePow.exists_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:11:27.549975+00:00
-- url     : https://prove2.me/submissions/486e2ae3-9df7-4300-bc1e-b9256b7ab10c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_sval_pullSec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
namespace GlobalTheory.VeryAmplePow
theorem _root_.solution {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (e : ∀ k, φ' k = h ≫ φ k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε),
      (∀ j (l : LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j),
        s'.f j = (Y'.presheaf.map (homOfLE l).op).hom ((h.app _).hom (s.f j))) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J, Good L z J → sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext e
  exact ⟨H1.SectionArithmetic.pullSec s h, fun _ _ => rfl, fun Z r z J hJ => H1.SectionArithmetic.sval_pullSec s h r z hJ⟩
end GlobalTheory.VeryAmplePow
