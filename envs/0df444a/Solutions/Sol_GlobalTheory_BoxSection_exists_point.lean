-- Prove2me | solution 1 for GlobalTheory.BoxSection.exists_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:18:37.425149+00:00
-- url     : https://prove2.me/submissions/6f5ee4d0-1731-4507-8b81-4a0d28885424

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusProdSec
import Theorems.Thm_GlobalTheory_BoxSection_exists_point_powObj

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
open GlobalTheory GlobalTheory.BoxSection
namespace GlobalTheory.BoxSection
theorem _root_.solution {S : Scheme.{0}} {G' G : Over S} {n : ℕ} (pr : Fin n → (G' ⟶ G))
    (lim : IsLimit (Fan.mk G' pr)) (s : S) (x : Fin n → G.left) (hx : ∀ i, G.hom (x i) = s) :
    ∃ y : G'.left, G'.hom y = s ∧ ∀ i, (pr i).left y = x i := by
  obtain ⟨z, hz, hz'⟩ := exists_point_powObj G s n x hx
  let m : Out.powObj G n ⟶ G' := lim.lift (Fan.mk (Out.powObj G n) (Out.powPr G (n := n)))
  have hm : ∀ i, m ≫ pr i = Out.powPr G i := fun i => lim.fac _ ⟨i⟩
  refine ⟨m.left z, ?_, fun i => ?_⟩
  · rw [← Scheme.Hom.comp_apply, Over.w m, hz]
  · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hm, hz']
end GlobalTheory.BoxSection
