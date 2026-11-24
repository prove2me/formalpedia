-- Prove2me | solution 1 for GlobalTheory.TransvFin.eq_of_specializes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:02:30.437022+00:00
-- url     : https://prove2.me/submissions/e2c41474-8b19-4dd7-82f6-7de8929fd64b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacNeZeroIffSpanEqMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_FiniteOfIsClosedSingleton

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
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.TransvFin
namespace GlobalTheory.TransvFin
theorem _root_.solution {X : Scheme.{0}} {J : Type} {U : X.Opens} (f : J → Γ(X, U)) {y y' : X} (h : y' ⤳ y)
    (hy : y ∈ U)
    (hf : Ideal.span (Set.range fun i => gs (𝟙 X) y U (f i)) = IsLocalRing.maximalIdeal (X.presheaf.stalk y))
    (h0 : ∀ i, y' ∉ X.basicOpen (f i)) : y' = y := by
  by_contra hne
  have hn : ¬ y ⤳ y' := fun h' => hne (h.antisymm h').eq
  rw [specializes_iff_forall_open] at hn
  push_neg at hn
  obtain ⟨V, hV, hV1, hV2⟩ := hn
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := y) (U := ⊤) trivial
  have hyW' : y' ∈ W := h.mem_open W.isOpen hyW
  obtain ⟨g, hg, hg'⟩ := hW.exists_basicOpen_le (V := ⟨V, hV⟩) ⟨y', hV1⟩ hyW'
  have hle : IsLocalRing.maximalIdeal (X.presheaf.stalk y) ≤
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y')).comap (X.presheaf.stalkSpecializes h).hom := by
    rw [← hf, Ideal.span_le]
    rintro _ ⟨i, rfl⟩ hu
    refine h0 i ((X.mem_basicOpen (f i) y' (h.mem_open U.isOpen hy)).2 ?_)
    have e : gs (𝟙 X) y U (f i) = (X.presheaf.germ U y hy).hom (f i) := gs_eq (𝟙 X) y U hy (f i)
    beta_reduce at hu
    rwa [e, TopCat.Presheaf.germ_stalkSpecializes_apply] at hu
  have hm : (X.presheaf.germ W y hyW).hom g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
    fun hu => hV2 (hg ((X.mem_basicOpen g y hyW).2 hu))
  refine hle hm ?_
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  exact (X.mem_basicOpen g y' hyW').1 hg'
end GlobalTheory.TransvFin
