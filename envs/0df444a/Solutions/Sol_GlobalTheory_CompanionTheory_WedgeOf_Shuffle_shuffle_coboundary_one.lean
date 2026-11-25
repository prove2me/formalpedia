-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.Shuffle.shuffle_coboundary_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:53:02.077645+00:00
-- url     : https://prove2.me/submissions/17894193-6ade-4f5c-acc2-8ade48eeda10

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CrossProductKernelQuotientVanishing
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_Shuffle_mp_box
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_Shuffle_shuffle_mk
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf GlobalTheory.CompanionTheory.WedgeOf.Shuffle
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CompanionTheory.WedgeOf.Shuffle
theorem _root_.solution (w : C1 (box F)) {a a' b b' : C} (φ : a ⟶ a') (ψ : b ⟶ b') :
    shuffle F (d1 (box F) w) (⟨a, a', φ⟩, ⟨b, b', ψ⟩) =
      (TensorProduct.map LinearMap.id (mp F ψ).toLinearMap (w (a, b) (a', b) (φ, 𝟙 b)) - w (a, b') (a', b') (φ, 𝟙 b')) +
      (w (a', b) (a', b') (𝟙 a', ψ) -
        TensorProduct.map (mp F φ).toLinearMap LinearMap.id (w (a, b) (a, b') (𝟙 a, ψ))) := by
  have e : CategoryStruct.comp (X := ((a, b) : C × C)) (Y := (a', b)) (Z := (a', b')) (φ, 𝟙 b) (𝟙 a', ψ) =
      CategoryStruct.comp (X := ((a, b) : C × C)) (Y := (a, b')) (Z := (a', b')) (𝟙 a, ψ) (φ, 𝟙 b') := by
    simp
  have i1 : (mp F (𝟙 a')).toLinearMap = LinearMap.id := by ext u; exact mp_id F a' u
  have i2 : (mp F (𝟙 b')).toLinearMap = LinearMap.id := by ext u; exact mp_id F b' u
  rw [shuffle_mk, d1_apply, d1_apply, e, mp_box, mp_box, i1, i2]
  abel
end GlobalTheory.CompanionTheory.WedgeOf.Shuffle
