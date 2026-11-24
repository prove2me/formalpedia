-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.WedgeOf.cup_add_cup_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:34:56.599037+00:00
-- url     : https://prove2.me/submissions/0fefa7b1-578a-4b08-941c-239d1a1f6da4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CupVanishingAntisymmetricCross
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_cup_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_cup
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf
namespace GlobalTheory.CompanionTheory.WedgeOf
theorem _root_.solution {R : Type} [CommRing R] {C : Type} [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R) (a b : H1 F) : cup F a b + cup F b a = 0 := by
  obtain ⟨a', rfl⟩ := H1.mk_surjective F a
  obtain ⟨b', rfl⟩ := H1.mk_surjective F b
  rw [cup_mk, cup_mk, ← map_add, H2.mk_eq_zero]
  refine ⟨-(fun T T' φ => a'.1 T T' φ * b'.1 T T' φ), ?_⟩
  funext T T' T'' φ ψ
  simp only [map_neg, Pi.neg_apply, d1_apply, Submodule.coe_add, Pi.add_apply, cupZ_apply, Z1.comp, map_mul]
  ring
end GlobalTheory.CompanionTheory.WedgeOf
