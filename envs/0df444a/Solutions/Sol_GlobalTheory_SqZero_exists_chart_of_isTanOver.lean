-- Prove2me | solution 1 for GlobalTheory.SqZero.exists_chart_of_isTanOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:27:42.834527+00:00
-- url     : https://prove2.me/submissions/29fa7bf8-d6ba-414b-a281-255d56bca090

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsChartOfMemRedKer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsResEqOfUnitInChart
import Theorems.Thm_GlobalTheory_SqZero_fstS_surjective
import Theorems.Thm_GlobalTheory_SqZero_nil_of_fstS
import Theorems.Thm_GlobalTheory_SqZero_exists_chart_pt_of_nil
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Chart_comp_one__39cc6a6ed057
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isLieComb_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isTan_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id comp_one' IsTan fstD scaleD prodPts
  isTan_iff isLieComb_iff)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
open TrivSqZeroExt (inl inr)
open GlobalTheory GlobalTheory.SqZero
attribute [local instance] Over.cartesianMonoidalCategory
variable {R : Type} [CommRing R]
variable {S S' S'' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
  [CommRing S''] [Algebra R S'']
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
namespace GlobalTheory.SqZero
theorem _root_.solution {B : Type} [CommRing B] [Algebra R B] (j : sp B ⟶ G)
    [IsOpenImmersion j.left] (u : B →ₐ[R] S) (hu : spMap u ≫ j = 1)
    {w : sp (R₀ := R) (DualNumber S) ⟶ G} (hw : IsTanOver w) :
    ∃ φ : B →ₐ[R] DualNumber S, w = spMap φ ≫ j ∧ ∀ b, (φ b).fst = u b := by
  obtain ⟨φ, h1, h2⟩ := exists_chart_pt_of_nil j (fstS R S) fstS_surjective nil_of_fstS w u
    (by rw [hu]; exact hw)
  exact ⟨φ, h1, fun b => by simpa using congrArg (fun f => f b) h2⟩
end GlobalTheory.SqZero
