-- Prove2me | solution 1 for GlobalTheory.SecLimit.isBas_of_comb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:10:39.732263+00:00
-- url     : https://prove2.me/submissions/7d3512d3-da16-4363-838e-79e17c612bc4

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
import Theorems.Thm_GlobalTheory_SecLimit_eq_of_val
import Theorems.Thm_GlobalTheory_SecLimit_ev_comb
import Theorems.Thm_GlobalTheory_SecLimit_exists_comb
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
theorem _root_.solution (hL : L.IsLB) {R : Type} [CommRing R] {m : ℕ} (g : R →+* Γ(Y, ⊤))
    (b : Fin m → LB.Sec (LB.LinComb L φ ε))
    (hb : ∀ s : LB.Sec (LB.LinComb L φ ε), ∃! a : Fin m → R, ∀ j, s.f j = ∑ i, resTop _ (g (a i)) * (b i).f j) :
    IsBas ((fn L Y).comp g) (secVals L φ ε) (fun i => ev (b i)) := by
  refine ⟨fun i => ⟨_, rfl⟩, ?_⟩
  rintro _ ⟨s, rfl⟩
  refine (existsUnique_congr fun a => ⟨ev_comb g a b, fun H => ?_⟩).1 (hb s)
  obtain ⟨t, ht⟩ := exists_comb (fun i => g (a i)) b
  rw [← ev_comb g a b ht] at H
  rw [eq_of_val hL fun y J => congrFun (congrFun (congrFun (congrFun H _) _) y) J]
  exact ht
end GlobalTheory.SecLimit
