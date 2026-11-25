-- Prove2me | solution 1 for GlobalTheory.UU.BoxSec.prod_famT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:02:23.654525+00:00
-- url     : https://prove2.me/submissions/afc0ea3f-4876-4629-9072-4cb53de45da0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RepSymInv
import Theorems.Thm_GlobalTheory_UU_BoxSec_comp_cT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BoxSec
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {Y : Over (Spec (CommRingCat.of R))}
namespace GlobalTheory.UU.BoxSec
theorem _root_.solution {T T₀ : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ T₀) (x : T ⟶ D.P.A) (α : D.X) (k : ℕ) {U : Type}
    [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h ((lift ρ x).left ≫ famφT D T₀ α i) ^ DegPre.famε k i =
      h x.left ^ ((k : ℤ) - 1) * h (x * cT D T α).left * (h (cT D T α).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have e₀ : (lift ρ x).left ≫ famφT D T₀ α 0 = x.left := congrArg (fun q => q.left) (lift_snd ρ x)
  have e₁ : (lift ρ x).left ≫ famφT D T₀ α 1 = (x * cT D T α).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul (lift ρ x) (snd T₀ D.P.A) (cT D _ α)).trans
      (by rw [comp_cT, lift_snd]))
  have e₂ : (lift ρ x).left ≫ famφT D T₀ α 2 = (cT D T α).left := congrArg (fun q => q.left) (comp_cT D (lift ρ x) α)
  have e₃ : (lift ρ x).left ≫ famφT D T₀ α 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (lift ρ x))
  rw [Fin.prod_univ_four, e₀, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]
end GlobalTheory.UU.BoxSec
