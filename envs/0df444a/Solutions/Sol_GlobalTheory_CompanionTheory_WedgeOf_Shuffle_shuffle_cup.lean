-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.Shuffle.shuffle_cup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:03:23.652531+00:00
-- url     : https://prove2.me/submissions/3712432b-7d12-444c-8684-42f0d4380195

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CrossProductKernelQuotientVanishing
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_Shuffle_mp_box
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
namespace GlobalTheory.CompanionTheory.WedgeOf.Shuffle
theorem _root_.solution (f h : Z1 F) (x : Ar C × Ar C) :
    shuffle F (cupZ (box F) ((boxL F).pullbackOneCocycle f) ((boxR F).pullbackOneCocycle h)).1 x =
      f.1 _ _ x.1.2.2 ⊗ₜ h.1 _ _ x.2.2.2 := by
  obtain ⟨⟨a, a', φ⟩, ⟨b, b', ψ⟩⟩ := x
  change (mp (box F) (T := (a', b)) (T' := (a', b')) (𝟙 a', ψ)) (f.1 a a' φ ⊗ₜ 1) * (1 ⊗ₜ h.1 b b' ψ) -
    (mp (box F) (T := (a, b')) (T' := (a', b')) (φ, 𝟙 b')) (f.1 a a (𝟙 a) ⊗ₜ 1) * (1 ⊗ₜ h.1 b' b' (𝟙 b')) = _
  rw [Z1.id f a, mp_box]
  simp [mp_id]
end GlobalTheory.CompanionTheory.WedgeOf.Shuffle
