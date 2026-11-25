-- Prove2me | solution 1 for GlobalTheory.TraceDescent.exactAt_of_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:19:32.87573+00:00
-- url     : https://prove2.me/submissions/a9107964-5084-4a4c-a872-31e257917544

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExactAtSectionCubeOfMulPullback
import Theorems.Thm_GlobalTheory_TraceDescent_exactAt_of_trace
import Theorems.Thm_GlobalTheory_TraceDescent_act_restrict
import Theorems.Thm_GlobalTheory_TraceDescent_act_act
import Theorems.Thm_GlobalTheory_TraceDescent_act_pullLE
import Theorems.Thm_GlobalTheory_TraceDescent_pullLE_injective
import Theorems.Thm_GlobalTheory_TraceDescent_exists_pullLE
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_pullLE_restrict
import Theorems.Thm_GlobalTheory_AbLaw_SecOn_restrict_pullLE


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
open GlobalTheory
noncomputable section
open GlobalTheory GlobalTheory.TraceDescent
open GlobalTheory.AbLaw.PowVanish
variable {X Y : Scheme.{0}} (f : Y ⟶ X) (M : LB X)
variable {G : Type} (τ : G → (Y ⟶ Y)) (hτ : ∀ y, τ y ≫ f = f)
    (hgal : ∀ (U : X.Opens) (s : Γ(Y, f ⁻¹ᵁ U)),
      (∀ y (e : f ⁻¹ᵁ U ≤ τ y ⁻¹ᵁ (f ⁻¹ᵁ U)), pb (τ y) e s = s) → ∃! g : Γ(X, U), (f.app U).hom g = s)
include hτ hgal
namespace GlobalTheory.TraceDescent
theorem _root_.solution [Group G] [Fintype G] (hmul : ∀ y z, τ y ≫ τ z = τ (y * z))
    {R : Type} [CommRing R] (a : X ⟶ Spec (CommRingCat.of R)) (b : Y ⟶ Spec (CommRingCat.of R))
    (hu : IsUnit ((Fintype.card G : ℕ) : R)) {I : Type} [LinearOrder I] (D : I → X.Opens) (p : ℕ)
    (H : (cubeComplex (secCube b (M.pull f) (fun i => f ⁻¹ᵁ D i))).ExactAt p) :
    (cubeComplex (secCube a M D)).ExactAt p := by
  have inv : ∀ y (s : Finset I), (⨅ i ∈ s, f ⁻¹ᵁ D i) ≤ τ y ⁻¹ᵁ (⨅ i ∈ s, f ⁻¹ᵁ D i) := fun y s => by
    rw [← preimage_biInf, ← Scheme.Hom.comp_preimage, hτ]
  let φ : ∀ s : Finset I, SecOn M (⨅ i ∈ s, D i) →+ SecOn (M.pull f) (⨅ i ∈ s, f ⁻¹ᵁ D i) :=
    fun s => (SecOn.pullLE M f _ _ (preimage_biInf D f s).ge).toAddMonoidHom
  let T : ∀ s : Finset I, SecOn (M.pull f) (⨅ i ∈ s, f ⁻¹ᵁ D i) →+ SecOn (M.pull f) (⨅ i ∈ s, f ⁻¹ᵁ D i) :=
    fun s => ∑ y, act f M (hτ y) (inv y s)
  have hT : ∀ s x, T s x = ∑ y, act f M (hτ y) (inv y s) x := fun s x => AddMonoidHom.finset_sum_apply _ _ _
  refine exactAt_of_trace _ _ φ T (fun {s t} h x => ?_) (fun {s t} h x => ?_)
    (fun s => pullLE_injective f M τ hτ hgal _ _ (preimage_biInf D f s).ge (preimage_biInf D f s).le) _ hu (fun s y => ?_)
    (fun s x => ?_) p H
  · exact (SecOn.pullLE_restrict f (iInf_le_iInf_of_subset D h) (preimage_biInf D f t).ge _).trans
      (SecOn.restrict_pullLE f (preimage_biInf D f s).ge (iInf_le_iInf_of_subset (fun i => f ⁻¹ᵁ D i) h) _).symm
  · change T t (SecOn.restrict _ (iInf_le_iInf_of_subset (fun i => f ⁻¹ᵁ D i) h) x) =
      SecOn.restrict _ (iInf_le_iInf_of_subset (fun i => f ⁻¹ᵁ D i) h) (T s x)
    rw [hT t, hT s x, map_sum]
    exact Finset.sum_congr rfl fun y _ => act_restrict f M (hτ y) (inv y s) (inv y t) _ x
  · refine exists_pullLE f M τ hτ hgal _ _ (preimage_biInf D f s).ge (preimage_biInf D f s).le (T s y)
      fun z e => ?_
    rw [hT s y, map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft z) _ _ fun w =>
      act_act f M (hτ z) (hτ w) (hτ (z * w)) (hmul z w) e (inv w s) (inv (z * w) s) y
  · refine (hT s _).trans ((Finset.sum_congr rfl fun y _ =>
      act_pullLE f M (hτ y) (inv y s) (preimage_biInf D f s).ge x).trans ?_)
    rw [Finset.sum_const, Finset.card_univ]
    rfl
end GlobalTheory.TraceDescent
