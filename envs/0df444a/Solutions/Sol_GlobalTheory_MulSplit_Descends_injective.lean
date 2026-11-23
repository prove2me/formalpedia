-- Prove2me | solution 1 for GlobalTheory.MulSplit.Descends.injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:34.798274+00:00
-- url     : https://prove2.me/submissions/3679682f-d889-47a2-b168-ba8f739420e1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_NonemptyEquivPiOfWeights
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart


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
variable {X Y B : Scheme.{0}} {L : LB X} {p : Y ⟶ B} {G : Type}
namespace GlobalTheory.MulSplit
namespace Descends
theorem _root_.solution (hL : L.IsLB) {q : Y ⟶ Y} {τ : G → (Y ⟶ Y)} (H : Descends q τ) (hq : q ≫ p = p)
    {D : (Y ⟶ X) →₀ ℤ} {v : Vals L p} (hv : v ∈ Sg L p D) (h : pl L q hq v = 0) : v = 0 := by
  obtain ⟨s, rfl⟩ := hv
  refine ev_zero fun j => H.1 _ (fn_ext fun y hy => ?_)
  choose I hI using fun χ : Y ⟶ X => exists_chart hL (χ y)
  have h0 : sval s (𝟙 Y ≫ q) y I = 0 := congrFun h ⟨(y, I, 𝟙 Y), hI, Category.id_comp _⟩
  refine (gs_pull (𝟙 Y) q y _ hy _).trans ((sec_trans s (𝟙 Y ≫ q) y hy (Good.mem hI _ _)).trans ?_)
  refine ((congrArg _ h0).trans (mul_zero _)).trans (Eq.symm ?_)
  exact (gs_pull (𝟙 Y) q y _ hy _).trans ((gs_eq _ _ _ hy _).trans
    ((congrArg _ (map_zero _)).trans (map_zero _)))
end Descends
end GlobalTheory.MulSplit
