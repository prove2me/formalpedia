-- Prove2me | solution 1 for GlobalTheory.TorsionFixedAut.isUnit_sval_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:56:07.168113+00:00
-- url     : https://prove2.me/submissions/226d54ef-7ff1-42fc-91ff-c27e63444e1e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqIdOfFixesTorsion
import Theorems.Thm_GlobalTheory_TorsionFixedAut_isUnit_gs_iff

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
open GlobalTheory GlobalTheory.TorsionFixedAut
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
variable {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
variable {σ : X ⟶ X} (c : LB.Gen (LB.LinComb L (K := Fin 2) ![σ, 𝟙 X] ![1, -1]))
namespace GlobalTheory.TorsionFixedAut
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) {Z : Scheme.{0}} (r : Z ⟶ Y)
    (z : Z) {J} (hJ : Good L z J) : IsUnit (sval s r z J) ↔ r z ∈ nonzeroLocus s := by
  have key : ∀ (j : K → L.ι) (hj : r z ∈ LB.wchart L φ j),
      IsUnit (gs r z (LB.wchart L φ j) (s.f j)) ↔ r z ∈ Y.basicOpen (s.f j) := fun j hj =>
    isUnit_gs_iff r z _ hj _
  constructor
  · intro h
    exact Opens.mem_iSup.2 ⟨_, (key _ (hJ.mem φ r)).1 h⟩
  · intro h
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 h
    have hj' : r z ∈ LB.wchart L φ j := Y.basicOpen_le _ hj
    have := (key j hj').2 hj
    rw [sec_trans s r z hj' (hJ.mem φ r)] at this
    exact isUnit_of_mul_isUnit_right this
end GlobalTheory.TorsionFixedAut
