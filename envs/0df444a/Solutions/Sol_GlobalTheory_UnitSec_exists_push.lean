-- Prove2me | solution 1 for GlobalTheory.UnitSec.exists_push
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:28:56.996262+00:00
-- url     : https://prove2.me/submissions/4724a454-42ee-4940-975e-19b933b90d89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MatchingSectionsExist
import Theorems.Thm_GlobalTheory_UnitSec_exists_pull
import Theorems.Thm_GlobalTheory_UU_exists_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UnitSec
variable {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]
namespace GlobalTheory.UnitSec
theorem _root_.solution {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K → (Y' ⟶ X)} (h : Y' ⟶ Y) (g : Y ⟶ Y')
    (h₁ : g ≫ h = 𝟙 Y) (h₂ : h ≫ g = 𝟙 Y')
    (hφ : ∀ k, φ' k = h ≫ φ k) (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J := by
  obtain ⟨s, hs⟩ := exists_pull (φ' := φ) g
    (fun k => by rw [hφ k, ← Category.assoc, h₁, Category.id_comp]) s'
  refine ⟨s, fun Z r z J hJ => ?_⟩
  rw [hs Z _ z J hJ, Category.assoc, h₂, Category.comp_id]
end GlobalTheory.UnitSec
