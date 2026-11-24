-- Prove2me | solution 1 for GlobalTheory.BoxSection.exists_point_powObj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:02:50.639834+00:00
-- url     : https://prove2.me/submissions/6e89494c-87de-4635-90fc-f48b735da8b2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusProdSec

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
theorem _root_.solution {S : Scheme.{0}} (G : Over S) (s : S) :
    ∀ (n : ℕ) (x : Fin n → G.left), (∀ i, G.hom (x i) = s) →
      ∃ y : (Out.powObj G n).left, (Out.powObj G n).hom y = s ∧
        ∀ i, (Out.powPr G i).left y = x i
  | 0, _, _ => ⟨s, rfl, fun i => i.elim0⟩
  | n + 1, x, hx => by
    obtain ⟨z, hz, hz'⟩ := solution G s n (fun i => x i.succ) (fun i => hx _)
    obtain ⟨y, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom)
      (g := (Out.powObj G n).hom) (x 0) z ((hx 0).trans hz.symm)
    refine ⟨y, ?_, fun i => Fin.cases ?_ (fun i => ?_) i⟩
    · change G.hom (pullback.fst G.hom (Out.powObj G n).hom y) = s
      rw [h1, hx]
    · exact h1
    · change (Out.powPr G i).left (pullback.snd G.hom (Out.powObj G n).hom y) = _
      rw [h2, hz']
end GlobalTheory.BoxSection
