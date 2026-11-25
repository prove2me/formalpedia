-- Prove2me | solution 1 for GlobalTheory.UT.SymFrame.GRep.out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:50:39.151521+00:00
-- url     : https://prove2.me/submissions/459dd860-eb78-41d3-83e8-d73973da9097

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UnivIdentity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.SymFrame
variable {S X : Scheme.{0}} (L : LB X) (Y : Over S)
variable {L Y}
namespace GlobalTheory.UT.SymFrame
namespace GRep
theorem _root_.solution (hL : L.IsLB) {P v} (h : GRep L Y P v) {K : Type} [Fintype K] (φ : K → (Y.left ⟶ X)) (ε : K → ℤ)
    (hP : ∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), P U h = ∏ k, h (φ k) ^ ε k) :
    ∃ s : LB.Gen (LB.LinComb L φ ε), s.IsGen ∧ ∀ (T : Over S) (r : T ⟶ Y) (z : T.left) (J), Good L z J →
      val s r.left z J = v T r z J := by
  obtain ⟨K', _, φ', ε', s', hs', hP', hv'⟩ := h
  obtain ⟨s, hs, vs⟩ := exists_gen hL (φ' := φ) (ε' := ε) (fun U _ h => (hP' U h).trans (hP U h)) s' hs'
  exact ⟨s, hs, fun T r z J hJ => (vs _ _ z J hJ).trans (hv' T r z J hJ)⟩
end GRep
end GlobalTheory.UT.SymFrame
