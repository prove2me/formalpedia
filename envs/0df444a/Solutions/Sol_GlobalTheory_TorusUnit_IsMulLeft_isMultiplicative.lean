-- Prove2me | solution 1 for GlobalTheory.TorusUnit.IsMulLeft.isMultiplicative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:15:43.114325+00:00
-- url     : https://prove2.me/submissions/b01845bb-e47c-41eb-9fe1-f0e4c5a01694

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Theorems.Thm_GlobalTheory_TorusUnit_value_comp
import Theorems.Thm_GlobalTheory_TorusUnit_IsMulLeft_value_mul
import Theorems.Thm_GlobalTheory_TorusUnit_fromInt_single
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
attribute [local instance] TorusInj.zuAlg
namespace GlobalTheory.TorusUnit
namespace IsMulLeft
theorem _root_.solution {ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)} (hρ : IsMulLeft ρ)
    {R : CommRingCat.{0}} (y : Spec R ⟶ Y.left) : IsMultiplicative ((expand y).hom ρ) := by
  let m (f : X →+ X × X) : grpAlg X R ⟶ grpAlg (X × X) R :=
    CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom R f)
  have key (f : X →+ X × X) : AddMonoidAlgebra.mapDomainRingHom R f ((expand y).hom ρ) =
      (value (fromInt X R ≫ m f) (Spec.map (const (X × X) R) ≫ y)).hom ρ := by
    have h := value_comp (m f) (fromInt X R) (Spec.map (const X R) ≫ y)
    have h2 : const X R ≫ m f = const (X × X) R := by
      apply CommRingCat.hom_ext
      refine RingHom.ext fun r => ?_
      simp [const, m]
    rw [← Spec.map_comp_assoc, h2] at h
    exact congrArg (fun f => f.hom ρ) h
  rw [IsMultiplicative, key, key, key]
  apply hρ.value_mul
  intro x
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  rw [fromInt_single]
  simp [m, AddMonoidAlgebra.single_mul_single]
end IsMulLeft
end GlobalTheory.TorusUnit
