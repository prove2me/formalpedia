-- Prove2me | solution 1 for GlobalTheory.UU.PackageDescent.exists_val_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:46:13.684898+00:00
-- url     : https://prove2.me/submissions/91a426fc-b6ec-435b-99ee-9422dea3734c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsDescendThrough
import Theorems.Thm_GlobalTheory_UU_PackageDescent_gm_comp
import Theorems.Thm_GlobalTheory_UU_PackageDescent_stalkMap_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.PackageDescent
variable {X X' Y Y' Z : Scheme.{0}} {K : Type} [Fintype K]
namespace GlobalTheory.UU.PackageDescent
theorem _root_.solution {M : LB X} (hM : M.IsLB) (ρ : Z ⟶ Y) [Flat ρ] [Surjective ρ] (y : Y) (I) (hI : Good M y I) :
    ∃ (z : Z) (I' : _) (e : (Y.presheaf.stalk y)ˣ →* (Z.presheaf.stalk z)ˣ), Good M z I' ∧ Function.Injective e ∧
      ∀ {W : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (W ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb M φ ε))
        (r : Y ⟶ W), val t (ρ ≫ r) z I' = e (val t r y I) := by
  obtain ⟨z, rfl⟩ := ρ.surjective y
  have : Epi ρ := Flat.epi_of_flat_of_surjective ρ
  obtain ⟨I', hI', e⟩ := exists_good M hM z (fun ψ : Y ⟶ X => ρ ≫ ψ) I
    (fun a b h => congrArg I ((cancel_epi ρ).1 h)) (fun ψ => hI ψ)
  refine ⟨z, I', Units.map (ρ.stalkMap z).hom.toMonoidHom, hI',
    Units.map_injective (stalkMap_injective ρ z), fun {W K} _ {φ ε} t r => ?_⟩
  rw [val_of t (ρ ≫ r) z I' (fun k => I (r ≫ φ k)) (fun k => by rw [Category.assoc]; exact e _)]
  exact gm_comp ρ r z _ (hI.mem φ r) _
end GlobalTheory.UU.PackageDescent
