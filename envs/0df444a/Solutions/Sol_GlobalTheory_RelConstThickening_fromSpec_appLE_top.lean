-- Prove2me | solution 1 for GlobalTheory.RelConstThickening.fromSpec_appLE_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:55:00.577245+00:00
-- url     : https://prove2.me/submissions/80ff8434-bf04-4cd2-be59-1cc8ca493dc4

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualNumberSectionsUniqueDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.RelConstThickening
namespace GlobalTheory.RelConstThickening
theorem _root_.solution {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (e : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e = (Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
end GlobalTheory.RelConstThickening
