-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.Shuffle.shuffle_crossZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:26:46.912408+00:00
-- url     : https://prove2.me/submissions/a73b1c3e-2dcb-4122-bf7c-2432e19fdd0b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CrossProductKernelQuotientVanishing
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_Shuffle_shuffle_cup
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_Shuffle_crossZ_tmul
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
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
variable {F}
variable (F)
namespace GlobalTheory.CompanionTheory.WedgeOf.Shuffle
theorem _root_.solution (Φ : C1 F ⊗[R] C1 F ≃ₗ[R] E F)
    (hΦ : ∀ f g x, Φ (f ⊗ₜ g) x = f _ _ x.1.2.2 ⊗ₜ g _ _ x.2.2.2) (s : Z1 F ⊗[R] Z1 F) :
    shuffle F (crossZ F s).1 = Φ (TensorProduct.map (Z1 F).subtype (Z1 F).subtype s) := by
  induction s using TensorProduct.induction_on with
  | zero => simp
  | tmul f h =>
    funext x
    rw [crossZ_tmul, shuffle_cup, TensorProduct.map_tmul, hΦ]
    rfl
  | add u v hu hv =>
    simp only [map_add, Submodule.coe_add, hu, hv]
end GlobalTheory.CompanionTheory.WedgeOf.Shuffle
