-- Prove2me | solution 1 for GlobalTheory.KeyPow.exists_sec_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:03:44.614521+00:00
-- url     : https://prove2.me/submissions/10d4d6d2-a819-4233-b0f7-18909198e386

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SubsingletonPrimeSpectrum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ValueAtNormalForm
import Theorems.Thm_GlobalTheory_KeyPow_res_constFn
import Theorems.Thm_GlobalTheory_KeyPow_constFn_mul
import Theorems.Thm_GlobalTheory_KeyPow_constFn_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.KeyPow
variable {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) {L : LB X}
namespace GlobalTheory.KeyPow
theorem _root_.solution {a b : R} (h : a * b = 1) (s : L.Sec) :
    ∃ t : L.Sec, (∀ i, t.f i = constFn p _ b * s.f i) ∧ (∀ i, s.f i = constFn p _ a * t.f i) ∧
      Out.nonzeroLocus s ≤ Out.nonzeroLocus t := by
  have e : ∀ i, s.f i = constFn p _ a * (constFn p _ b * s.f i) := fun i => by
    rw [← _root_.mul_assoc, ← constFn_mul, h, constFn_one, _root_.one_mul]
  refine ⟨⟨fun i => constFn p _ b * s.f i, fun i j => ?_⟩, fun _ => rfl, e, iSup_mono fun i => ?_⟩
  · rw [map_mul, map_mul, res_constFn, res_constFn, s.compat i j, mul_left_comm]
  · conv_lhs => rw [e i, Scheme.basicOpen_mul]
    exact inf_le_right
end GlobalTheory.KeyPow
