-- Prove2me | solution 1 for GlobalTheory.GlueLineBundle.unit_ext_imm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:37:14.933208+00:00
-- url     : https://prove2.me/submissions/42c1684f-1982-446b-8c3d-4e5678068348

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlueLineBundles
import Theorems.Thm_GlobalTheory_GlueLineBundle_gm_id_val
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
open GlobalTheory GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}}
namespace GlobalTheory.GlueLineBundle
theorem _root_.solution {O : X.Opens} {a b : Γ(X, O)ˣ}
    (h : ∀ x ∈ O, ∃ (W : Scheme.{0}) (j : W ⟶ X) (_ : IsOpenImmersion j) (w : W), j w = x ∧
      gm j w O a = gm j w O b) : a = b := by
  apply unit_ext
  intro x hx
  obtain ⟨W, j, hj, w, rfl, e⟩ := h x hx
  apply Units.ext
  rw [gm_id_val hx, gm_id_val hx]
  have e' := congrArg Units.val e
  rw [gm_val j w O hx, gm_val j w O hx, ← Scheme.Hom.germ_stalkMap_apply, ← Scheme.Hom.germ_stalkMap_apply] at e'
  exact (asIso (j.stalkMap w)).commRingCatIsoToRingEquiv.injective e'
end GlobalTheory.GlueLineBundle
