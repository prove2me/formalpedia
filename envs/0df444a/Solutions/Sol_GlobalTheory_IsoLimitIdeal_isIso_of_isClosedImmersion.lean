-- Prove2me | solution 1 for GlobalTheory.IsoLimitIdeal.isIso_of_isClosedImmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:05:57.705838+00:00
-- url     : https://prove2.me/submissions/af22e24d-7ada-42b0-bea4-8b54bded5109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsIsoOfIsClosedImmersion
import Theorems.Thm_GlobalTheory_ThickeningClosed_exists_mul_eq_zero_of_mem
import Theorems.Thm_GlobalTheory_ThickeningClosed_isOpen_zeroLocusOpen
import Theorems.Thm_GlobalTheory_ThickeningClosed_mem_of_thickenings


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IsoLimitIdeal
open ThickeningClosed
namespace GlobalTheory.IsoLimitIdeal
theorem _root_.solution {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (I : Ideal V) (hI : I ≠ ⊤) {X Z : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [IsProper f] (j : Z ⟶ X)
    [IsClosedImmersion j]
    (h : ∀ n : ℕ, ∃ l : pullback f (thick V I n) ⟶ Z,
      l ≫ j = pullback.fst f (thick V I n)) : IsIso j := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have key : ∀ x, x ∈ zeroLocusOpen j.ker := by
    intro x
    by_contra hx
    have hc : IsClosed (f '' (zeroLocusOpen j.ker)ᶜ) :=
      f.isClosedMap _ (isOpen_zeroLocusOpen _).isClosed_compl
    obtain ⟨y, hy, hy'⟩ :=
      (IsLocalRing.specializes_closedPoint (R := V) (f x)).mem_closed hc ⟨x, hx, rfl⟩
    refine hy (mem_of_thickenings _ f j h y ?_)
    rw [hy']
    exact IsLocalRing.le_maximalIdeal hI
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
  refine le_bot_iff.1 fun U a ha ↦ ?_
  change a = 0
  refine eq_zero_of_localization a fun J hJ ↦ ?_
  obtain ⟨s, hs, hsa⟩ := exists_mul_eq_zero_of_mem j.ker U ⟨J, hJ.isPrime⟩ (key _) ha
  exact (IsLocalization.map_eq_zero_iff J.primeCompl _ a).2 ⟨⟨s, hs⟩, hsa⟩
end GlobalTheory.IsoLimitIdeal
