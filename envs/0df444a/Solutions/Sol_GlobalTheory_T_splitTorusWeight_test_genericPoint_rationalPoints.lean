-- Prove2me | solution 1 for GlobalTheory.T.splitTorusWeight_test_genericPoint_rationalPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:04:43.192189+00:00
-- url     : https://prove2.me/submissions/a47b9608-6d76-4a1f-bbb1-dee6648734b0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusWeightTestGenericPointRationalPoints
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusWeightTestGenericPointRationalPointsStatement
import Theorems.Thm_GlobalTheory_SS_WtRat_wt_of_genericPoint


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], Smooth G.hom → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G) (F : Type) [Field F] (s : Sp F ⟶ Sp k) (g : Over.mk s ⟶ G), (∀ V : G.left.Opens, (V : Set G.left).Nonempty → ⊤ ≤ g.left ⁻¹ᵁ V) → ∀ (V : G.left.Opens) (u : Γ(G.left, V)) (χ : X), (∀ (t : 𝟙_ (Over (Sp k)) ⟶ splitTorus (Sp k) X) (h₁ : ⊤ ≤ (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V), WtRat.ev (R := F) (((toUnit (Over.mk s) ≫ t) ≫ i) * g).left V h₁ u = WtRat.ev (R := F) (toUnit (Over.mk s) ≫ t).left ⊤ le_top (charUnit (Sp k) X χ).val * WtRat.ev (R := F) g.left V h₂ u) → Wt i V u χ := by
  first | exact @GlobalTheory.SS.WtRat.wt_of_genericPoint | exact GlobalTheory.SS.WtRat.wt_of_genericPoint | (intros; apply GlobalTheory.SS.WtRat.wt_of_genericPoint <;> assumption)
end _root_.GlobalTheory.T
