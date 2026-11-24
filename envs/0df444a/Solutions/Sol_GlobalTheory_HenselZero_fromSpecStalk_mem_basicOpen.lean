-- Prove2me | solution 1 for GlobalTheory.HenselZero.fromSpecStalk_mem_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:56:44.405799+00:00
-- url     : https://prove2.me/submissions/edd9f9e6-1d4f-4cba-a4fa-7d54f1de40e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FormallySmoothQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsSectionOfTransversal
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.HenselZero
namespace GlobalTheory.HenselZero
theorem _root_.solution {X : Scheme.{0}} {y : X} {U : X.Opens} (hy : y ∈ U) (f : Γ(X, U))
    (q : Spec (X.presheaf.stalk y)) (hq : (X.presheaf.germ U y hy).hom f ∉ q.asIdeal) :
    X.fromSpecStalk y q ∈ X.basicOpen f := by
  have ht : ⊤ ≤ X.fromSpecStalk y ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem (X.fromSpecStalk y)
    (by rwa [Scheme.fromSpecStalk_closedPoint])).ge
  rw [← Scheme.Hom.mem_preimage, Scheme.preimage_basicOpen, Scheme.fromSpecStalk_app hy]
  simp only [CommRingCat.comp_apply]
  rw [Scheme.basicOpen_res, basicOpen_eq_of_affine]
  exact ⟨ht trivial, hq⟩
end GlobalTheory.HenselZero
