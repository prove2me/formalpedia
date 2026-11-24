-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.hopf_cross_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:55:37.4662+00:00
-- url     : https://prove2.me/submissions/4b1507ff-780c-494f-aee7-a1cf66408fd6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CupVanishingAntisymmetricCross
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_hopf_pull_lift_cup
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_cup
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf
namespace GlobalTheory.CompanionTheory.WedgeOf
theorem _root_.solution : LowSt → ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R), Hopf F False → ∀ t : H1 F ⊗[R] H1 F,
    TensorProduct.lift (cup F) t = 0 →
      TensorProduct.lift (crossB F) (t - TensorProduct.comm R _ _ t) = 0 := by
  intro hLow R _ C _ F hH t ht
  obtain ⟨D, _, G, π, m, hq, hm, -⟩ := hH
  have h2 := hopf_pull_lift_cup F G π m hm t
  simp only [ht, map_zero, zero_add] at h2
  obtain ⟨-, hinj, -⟩ := hLow R (C × C) D (box F) G π hq
  apply hinj.1
  rw [map_zero]
  exact h2.symm
end GlobalTheory.CompanionTheory.WedgeOf
