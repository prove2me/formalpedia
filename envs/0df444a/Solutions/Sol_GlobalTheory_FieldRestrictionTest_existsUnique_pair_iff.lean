-- Prove2me | solution 1 for GlobalTheory.FieldRestrictionTest.existsUnique_pair_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:42:13.389798+00:00
-- url     : https://prove2.me/submissions/ced10852-cb15-4aea-abab-9b042323550c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsUniquePairIff
import Theorems.Thm_GlobalTheory_FieldRestrictionTest_over_of_isPullF
import Theorems.Thm_GlobalTheory_FieldRestrictionTest_isPullF_unique
import Theorems.Thm_GlobalTheory_FieldRestrictionTest_exists_isPullF
import Theorems.Thm_GlobalTheory_FieldRestrictionTest_isNsmul_restrict
import Theorems.Thm_GlobalTheory_FieldRestrictionTest_isIota_restrict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FieldRestrictionTest
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))}
variable {W : (Spec (CommRingCat.of R)).Opens} {ψW : PsiOn D W} {S : Over W.toScheme}
namespace GlobalTheory.FieldRestrictionTest
theorem _root_.solution {k : ℕ} (x : Spec (CommRingCat.of F) ⟶ S.left) (p : QkPtW D W ψW k S) :
    (∃! q : QkPt D F k, QkPtW.IsPullF F x p q) ↔ x ≫ S.hom ≫ W.ι = jFK (R := R) F ≫ jK R := by
  refine ⟨fun ⟨_, h, _⟩ => over_of_isPullF h.2, fun hx => ?_⟩
  let σ : TF (R := R) F ⟶ overW W S := Over.homMk x hx
  obtain ⟨g, hg⟩ := exists_isPullF σ p.g
  obtain ⟨h, h1, h2⟩ := p.eq
  obtain ⟨h', hh⟩ := exists_isPullF σ h
  refine ⟨⟨p.y, g, h', isNsmul_restrict hg hh h1, isIota_restrict hh h2⟩, ⟨rfl, hg⟩, ?_⟩
  rintro ⟨y, g', _⟩ ⟨rfl, e⟩
  obtain rfl : g' = g := isPullF_unique e hg
  rfl
end GlobalTheory.FieldRestrictionTest
