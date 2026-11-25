-- Prove2me | solution 1 for GlobalTheory.EigenDer.exists_trunc_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:00:56.671861+00:00
-- url     : https://prove2.me/submissions/9e8dc3c4-35f2-4a62-8e14-7ead03d6b5c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HasSubstAddSqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsNilpotentOfMemKerJetTruncR
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SubstMapAlgebraMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.EigenDer
variable {R : Type} [CommRing R]
namespace GlobalTheory.EigenDer
theorem _root_.solution {G : Over (Spec (CommRingCat.of R))} {κ : Type} (x : Fam G κ)
    (hx : ∀ m, spMap (jetTruncR R κ m) ≫ x (m + 1) = x m) (n : ℕ) :
    ∃ t : JetR R κ (n + 1) →ₐ[R] JetR R κ 1, (∀ j, t (zR (n + 1) j) = zR 1 j) ∧ spMap t ≫ x (n + 1) = x 1 := by
  induction n with
  | zero =>
    refine ⟨AlgHom.id R _, fun _ => rfl, ?_⟩
    have : spMap (R₀ := R) (AlgHom.id R (JetR R κ 1)) = 𝟙 _ := by
      apply Over.OverMorphism.ext
      rw [spMap_left]
      exact Spec.map_id _
    rw [this, Category.id_comp]
  | succ n ih =>
    obtain ⟨t, h1, h2⟩ := ih
    refine ⟨t.comp (jetTruncR R κ (n + 1)), fun j => h1 j, ?_⟩
    rw [← spMap_comp, Category.assoc, hx, h2]
end GlobalTheory.EigenDer
