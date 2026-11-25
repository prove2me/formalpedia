-- Prove2me | solution 1 for GlobalTheory.LieExt.lieMult_extend_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:03:18.13143+00:00
-- url     : https://prove2.me/submissions/65ed0aca-fe07-469f-a8ae-76ace3cefa7a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RankPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LieMultIffFinrank
import Theorems.Thm_GlobalTheory_LieExt_lieMult_iff_finrank
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_univChartLoc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.LieExt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.LieExt
theorem _root_.solution {k K : Type} [Field k] [Field K] (φ : k →+* K) (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] [Smooth G.hom] {O : Type} [CommRing O] (act : Geo.Tor.OAct O G) (χ : O →+* k) (N : ℕ) :
    Geo.Tor.LieMult act (Geo.Tor.spMap φ) (φ.comp χ) N ↔ Geo.Tor.LieMult act (𝟙 _) χ N := by
  let _ := φ.toAlgebra
  have := act.hom
  obtain ⟨n, x, hx⟩ := univChartLoc G
  have h := lieMult_iff_finrank (K := k) G hx act χ N
  have e : fB k k = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap k k)) = _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  rw [e, Algebra.algebraMap_self, RingHom.id_comp] at h
  exact (lieMult_iff_finrank (K := K) G hx act χ N).trans h.symm
end GlobalTheory.LieExt
