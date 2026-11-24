-- Prove2me | solution 1 for GlobalTheory.TorusUnit.IsMulLeft.value_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:05:12.816738+00:00
-- url     : https://prove2.me/submissions/d88e2060-42c6-460f-b879-5e791f696af0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Theorems.Thm_GlobalTheory_TorusUnit_torusPoint_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_ext_ZU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Rosenlicht_ringHom_uliftInt_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct AlgebraMonoidAlgebra
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TorusUnit
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (torusFst ringHom_ext_ZU ringHom_uliftInt_ext)
open AddMonoidAlgebra (single)
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]
variable {Y : Over S}
namespace GlobalTheory.TorusUnit
namespace IsMulLeft
theorem _root_.solution {ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)} (hρ : IsMulLeft ρ)
    {R : CommRingCat.{0}} (φ φ' ψ : torusRing ZU X ⟶ R) (y : Spec R ⟶ Y.left)
    (h : ∀ x : X, ψ.hom (single x 1) = φ.hom (single x 1) * φ'.hom (single x 1)) :
    (value ψ y).hom ρ = (value φ y).hom ρ * (value φ' y).hom ρ := by
  have := hρ (Over.mk (y ≫ Y.hom)) (torusPoint φ _) (torusPoint φ' _) (Over.homMk y rfl)
  rw [torusPoint_mul φ φ' ψ _ h] at this
  have h2 := congrArg (Scheme.ΓSpecIso R).hom.hom this
  rw [map_mul] at h2
  exact h2
end IsMulLeft
end GlobalTheory.TorusUnit
