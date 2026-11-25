-- Prove2me | solution 1 for GlobalTheory.SecLimit.exists_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:28:25.520869+00:00
-- url     : https://prove2.me/submissions/cca3c096-5d86-4fdf-97ab-77a5ca9512d5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueLimit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.SecLimit
variable {X Y Y' Y'' : Scheme.{0}} (L : LB X) {K K' K₃ : Type} [Fintype K] [Fintype K'] [Fintype K₃]
variable {L}
variable {φ : K → (Y ⟶ X)} {ε : K → ℤ}
namespace GlobalTheory.SecLimit
theorem _root_.solution {M : LB Y} {m : ℕ} (a : Fin m → Γ(Y, ⊤)) (b : Fin m → LB.Sec M) :
    ∃ s : LB.Sec M, ∀ j, s.f j = ∑ i, resTop _ (a i) * (b i).f j :=
  ⟨⟨fun j => ∑ i, resTop _ (a i) * (b i).f j, fun j j' => by
    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (DVR.SecOps.secScale (a i) (b i)).compat j j'⟩, fun _ => rfl⟩
end GlobalTheory.SecLimit
