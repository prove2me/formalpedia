-- Prove2me | solution 1 for GlobalTheory.MulSplit.mem_Sg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:36:27.888805+00:00
-- url     : https://prove2.me/submissions/7ff2f41f-2760-4806-9b60-79af8fce913f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyEquivPiOfWeights
import Theorems.Thm_GlobalTheory_MulSplit_formEq_of_dv
import Theorems.Thm_GlobalTheory_MulSplit_dv_support
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec


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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.MulSplit
variable {X Y B : Scheme.{0}} (L : LB X) (p : Y ⟶ B)
variable {L p}
variable {K K' : Type} [Fintype K] [Fintype K']
namespace GlobalTheory.MulSplit
theorem _root_.solution (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {D : (Y ⟶ X) →₀ ℤ} (h : dv φ ε = D)
    (v : Vals L p) : v ∈ Sg L p D ↔ ∃ s : LB.Sec (LB.LinComb L φ ε), ev p s = v := by
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨s', hs⟩ := exists_sec hL (formEq_of_dv ((dv_support D).trans h.symm)) s
    exact ⟨s', funext fun i => hs _ _ _ _ i.2.1⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨s', hs⟩ := exists_sec hL (formEq_of_dv (h.trans (dv_support D).symm)) s
    exact ⟨s', funext fun i => hs _ _ _ _ i.2.1⟩
end GlobalTheory.MulSplit
