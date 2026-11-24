-- Prove2me | solution 1 for GlobalTheory.DisjointCoverLB.units_eq_of_gm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:23:42.444081+00:00
-- url     : https://prove2.me/submissions/5f96299b-ad45-4b8d-955e-1ba31dd7e0a5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LbIsoOfDisjointCover
import Theorems.Thm_GlobalTheory_ExtendLineBundle_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.DisjointCoverLB
namespace GlobalTheory.DisjointCoverLB
theorem _root_.solution {X : Scheme.{0}} {V : X.Opens} {a b : Γ(X, V)ˣ}
    (h : ∀ x ∈ V, ∃ (Z : Scheme.{0}) (ι : Z ⟶ X) (_ : IsOpenImmersion ι) (z : Z), ι z = x ∧ gm ι z V a = gm ι z V b) :
    a = b := by
  refine unit_ext fun x hx => ?_
  obtain ⟨Z, ι, hι, z, rfl, e⟩ := h x hx
  have e' := congrArg Units.val e
  rw [gm_val ι z V hx, gm_val ι z V hx, ← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply] at e'
  have key := (ConcreteCategory.bijective_of_isIso (ι.stalkMap z)).1 e'
  apply Units.ext
  rw [gm_val (𝟙 X) (ι z) V hx, gm_val (𝟙 X) (ι z) V hx]
  exact key
end GlobalTheory.DisjointCoverLB
