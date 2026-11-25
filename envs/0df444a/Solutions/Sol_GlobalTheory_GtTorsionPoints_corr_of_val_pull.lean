-- Prove2me | solution 1 for GlobalTheory.GtTorsionPoints.corr_of_val_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:44:51.408944+00:00
-- url     : https://prove2.me/submissions/487a3545-4217-4fa9-8f98-90aadd2d797e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifPowOf3
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_GenCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIntegralOfTorsion
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.GtTorsionPoints
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.GtTorsionPoints
theorem _root_.solution (hL : L.IsLB) (ρ : Z ⟶ Y) (hinj : ∀ U, Function.Injective (ρ.app U).hom)
    (hρ : ∀ a b : Y ⟶ X, ρ ≫ a = ρ ≫ b → a = b)
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : ∀ z J, Good L z J → val t ρ z J = val t' ρ z J) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  refine Units.ext (hinj _ (fn_ext fun z hz => ?_))
  have hz' : ρ z ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' := hz
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (fun k => ρ ≫ Sum.elim φ φ' k) (Sum.elim j j') (by
    rintro (a | a) (b | b) e <;> replace e := hρ _ _ e
    exacts [c₁ a b e, c₃ a b e, (c₃ b a e.symm).symm, c₂ a b e]) (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hz'.1 a, Set.mem_iInter.1 hz'.2 a])
  have := h z J hJ
  rw [val_of t _ z J j (fun k => e (.inl k)), val_of t' _ z J j' (fun k => e (.inr k))] at this
  rw [gs_pull (𝟙 Z) ρ z _ hz', gs_pull (𝟙 Z) ρ z _ hz', Category.id_comp, gs_unit ρ z _ hz', gs_unit ρ z _ hz']
  exact congrArg Units.val ((gm_res ρ z _ hz' _).trans (this.trans (gm_res ρ z _ hz' _).symm))
end GlobalTheory.GtTorsionPoints
