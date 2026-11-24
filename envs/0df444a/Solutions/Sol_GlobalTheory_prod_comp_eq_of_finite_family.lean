-- Prove2me | solution 1 for GlobalTheory.prod_comp_eq_of_finite_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:52.158797+00:00
-- url     : https://prove2.me/submissions/ee8c7443-2b2f-4b57-bd81-a6622226855d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KaRuleK
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ProdCompEqOfFiniteFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S : Type} (A : Finset (S → ℂ)) (a : S → S)
    (h : ∀ f ∈ A, ∃ f' ∈ A, f = f' ∘ a) (w : ℂ) (x : S) :
    ∏ f ∈ A, (w - f (a x)) = ∏ f ∈ A, (w - f x) := by
  classical
  choose! φ hφA hφ using h
  have hinj : Set.InjOn φ A := fun f hf k hk hfk => by rw [hφ f hf, hφ k hk, hfk]
  have himg : A.image φ = A := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hy
      exact hφA f hf
    · rw [Finset.card_image_of_injOn hinj]
  calc ∏ f ∈ A, (w - f (a x)) = ∏ f ∈ A.image φ, (w - f (a x)) := by rw [himg]
    _ = ∏ f ∈ A, (w - φ f (a x)) := Finset.prod_image hinj
    _ = ∏ f ∈ A, (w - f x) :=
        Finset.prod_congr rfl (fun f hf => congrArg (w - ·) (congrFun (hφ f hf) x).symm)
end GlobalTheory
