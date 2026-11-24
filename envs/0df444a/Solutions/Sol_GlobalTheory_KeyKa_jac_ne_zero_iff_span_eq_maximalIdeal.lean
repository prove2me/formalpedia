-- Prove2me | solution 1 for GlobalTheory.KeyKa.jac_ne_zero_iff_span_eq_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:19.633499+00:00
-- url     : https://prove2.me/submissions/0889b24f-2f3d-4fc9-9fc7-566c289b4874

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Theorems.Thm_GlobalTheory_JacGen_det_ne_zero_iff_span_germ_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
namespace GlobalTheory.KeyKa
theorem _root_.solution : ∀ (K : Type) [Field K] (x : KeyIn K) (n : ℕ) (s : Fin x.P.g → RR x n) (z : Pt x) (c : x.P.L.ι) (p : Sp K), ⊤ ≤ z.left ⁻¹ᵁ x.P.L.U c → (∀ i, valT (T := K) z.left (x.P.L.U c) ((s i).f c) = 0) → (jac x s z c ≠ 0 ↔ Ideal.span (Set.range fun i => gs (𝟙 _) (z.left p) (x.P.L.U c) ((s i).f c)) = IsLocalRing.maximalIdeal (x.P.A.left.presheaf.stalk (z.left p))) := by
  intro K _ x n s z c p hc hs
  have := x.P.smoothDim
  have : Smooth x.P.A.hom := SmoothOfRelativeDimension.smooth x.P.g _
  have hU : z.left p ∈ x.P.L.U c := hc (x := p) trivial
  refine (GlobalTheory.JacGen.det_ne_zero_iff_span_germ_eq x.basis z p hU (fun i => (s i).f c) hs).trans ?_
  refine iff_of_eq (congrArg (fun F => Ideal.span (Set.range F) = _) (funext fun i => ?_))
  exact (gs_eq (𝟙 _) _ _ hU _).symm
end GlobalTheory.KeyKa
