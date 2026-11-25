-- Prove2me | solution 1 for GlobalTheory.FieldRestrictionTest.isNsmul_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:50:07.717021+00:00
-- url     : https://prove2.me/submissions/5b7fe6b0-c6f2-4be7-b281-cba0335764d8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsUniquePairIff
import Theorems.Thm_GlobalTheory_FieldRestrictionTest_isPullF_unique
import Theorems.Thm_GlobalTheory_FieldRestrictionTest_exists_isPullF
import Theorems.Thm_GlobalTheory_FieldRestrictionTest_isZero_restrict
import Theorems.Thm_GlobalTheory_FieldRestrictionTest_isAdd_restrict

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
namespace GlobalTheory.FieldRestrictionTest
theorem _root_.solution {σ : TF (R := R) F ⟶ T} {k : ℕ} {a c : GtPt D T} {a' c' : GtPtF D F}
    (Ha : GtPt.IsPullF F σ.left a a') (Hc : GtPt.IsPullF F σ.left c c') (h : GtPt.IsNsmul k a c) :
    GtPtF.IsNsmul k a' c' := by
  obtain ⟨u, u0, us, rfl⟩ := h
  choose v hv using fun i => exists_isPullF σ (u i)
  exact ⟨v, isZero_restrict (hv _) u0, fun i => isAdd_restrict (hv _) Ha (hv _) (us i), isPullF_unique (hv _) Hc⟩
end GlobalTheory.FieldRestrictionTest
