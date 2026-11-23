-- Prove2me | solution 1 for GlobalTheory.corr_of_val_flat_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:36.704173+00:00
-- url     : https://prove2.me/submissions/35715bb3-ce02-4801-9339-bdc7eb84918d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValuesNatural
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CorrOfValFieldExtension
import Theorems.Thm_GlobalTheory_values_natural
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
private theorem stalkMap_injective_of_flat' {Y Z : Scheme.{0}} (ρ : Z ⟶ Y) [Flat ρ] (z : Z) :
    Function.Injective (ρ.stalkMap z).hom := by

  let _ := (ρ.stalkMap z).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z) := Flat.stalkMap ρ z
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z)) :=
    (by infer_instance : IsLocalHom (ρ.stalkMap z).hom)
  have : Module.FaithfullyFlat (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z)
end GlobalTheory
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y Z : Scheme.{0}} (ρ : Z ⟶ Y) [Flat ρ] [Surjective ρ] {L : LB X}
    (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)}
    {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : ∀ z J, Good L z J → val t ρ z J = val t' ρ z J) : LB.Gen.Corr L φ ε φ' ε' t t' := by

  have : Epi ρ := Flat.epi_of_flat_of_surjective ρ
  refine corr_of_val hL fun y J hJ => ?_
  obtain ⟨z, rfl⟩ := ρ.surjective y
  obtain ⟨J', hJ', hJJ'⟩ := exists_good L hL z (fun ψ : Y ⟶ X => ρ ≫ ψ) J
    (fun a b hab => congrArg J ((cancel_epi ρ).1 hab)) (fun ψ => by simpa using hJ ψ)
  have hpull : (fun ψ : Y ⟶ X => J' (ρ ≫ ψ)) = J := funext hJJ'
  have e₁ := (values_natural X Y Y Z L K φ ε (𝟙 Y) ρ z J' hJ').2.2.1 t
  have e₂ := (values_natural X Y Y Z L K' φ' ε' (𝟙 Y) ρ z J' hJ').2.2.1 t'
  rw [Category.comp_id, hpull] at e₁ e₂

  apply Units.ext
  apply stalkMap_injective_of_flat' ρ z
  rw [← e₁, ← e₂, h z J' hJ']
end GlobalTheory
