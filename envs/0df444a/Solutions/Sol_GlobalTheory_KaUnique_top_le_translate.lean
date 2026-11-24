-- Prove2me | solution 1 for GlobalTheory.KaUnique.top_le_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:29:52.26083+00:00
-- url     : https://prove2.me/submissions/b02212db-c28b-4172-9b4d-746930a4cca5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SignSwap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_TopLeTranslate
import Theorems.Thm_GlobalTheory_KaUnique_fst_translate

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
noncomputable section
open GlobalTheory GlobalTheory.KaUnique
variable {T T' : Type} [CommRing T] [CommRing T'] {X : Scheme.{0}}
variable {R : Type} [CommRing R]
namespace GlobalTheory.KaUnique
theorem _root_.solution (x : KeyIn R) (z : Pt x) (k : Fin x.P.g) {U : x.P.A.left.Opens} (h : ⊤ ≤ z.left ⁻¹ᵁ U) :
    ⊤ ≤ (show Sp (DualNumber R) ⟶ x.P.A.left from ((toUnit (epsR R) ≫ z) * x.v k).left) ⁻¹ᵁ U := by
  intro p _
  have hp : (p : PrimeSpectrum (DualNumber R)) ∈
      Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
    rw [range_comap_of_surjective _ _ (fun a => ⟨TrivSqZeroExt.inl a, rfl⟩)]
    intro a ha
    have ha' : a.fst = 0 := ha
    refine p.isPrime.mem_of_pow_mem 2 ?_
    have : a ^ 2 = 0 := by ext <;> simp [ha', pow_two]
    rw [this]; exact zero_mem _
  obtain ⟨q, rfl⟩ := hp
  have := h (Set.mem_univ q)
  rw [← fst_translate x z k] at this
  exact this
end GlobalTheory.KaUnique
