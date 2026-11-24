-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.cupHyp_add_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:28:17.508489+00:00
-- url     : https://prove2.me/submissions/5fd711ba-3ea0-4d58-bbe2-12ffec2fb0d8

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_cupHyp_mk
import Theorems.Thm_GlobalTheory_CechDR_wedge_swap
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
namespace GlobalTheory.CompanionTheory.HodgeAlt
theorem _root_.solution (a b : Hyp1 F) : cupHyp F a b + cupHyp F b a = 0 := by
  obtain ⟨a, rfl⟩ := Hyp1.mk_surjective F a
  obtain ⟨b, rfl⟩ := Hyp1.mk_surjective F b
  rw [cupHyp_mk, cupHyp_mk, ← map_add]
  refine Hyp2.mk_eq_zero.2 ⟨(fun T T' φ ↦ -(a.1.1 T T' φ * b.1.1 T T' φ), 0), ?_⟩
  refine Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) fun T ↦ ?_
  · change _ = (cupTot F a.1 b.1).1 T T' T'' φ ψ + (cupTot F b.1 a.1).1 T T' T'' φ ψ
    simp only [cechDeRhamTotalDifferentialOne_functionPart, cupTot_apply, cechDeRhamTotalCocyclesOne.comp a, cechDeRhamTotalCocyclesOne.comp b, map_neg, map_mul]
    ring
  · change _ = (cupTot F a.1 b.1).2.1 T T' φ + (cupTot F b.1 a.1).2.1 T T' φ
    simp only [dTot1_a, cupTot_a]
    rw [cechDeRhamTotalCocyclesOne.conn a φ, cechDeRhamTotalCocyclesOne.conn b φ]
    simp only [Pi.zero_apply, map_zero, sub_zero, map_neg, Derivation.leibniz, smul_add]
    module
  · change _ = (cupTot F a.1 b.1).2.2 T + (cupTot F b.1 a.1).2.2 T
    simp only [dTot1_η, cupTot_η]
    rw [wedge_swap (a.1.2 T)]
    simp
end GlobalTheory.CompanionTheory.HodgeAlt
