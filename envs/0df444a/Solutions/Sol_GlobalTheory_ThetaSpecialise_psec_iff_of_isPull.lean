-- Prove2me | solution 1 for GlobalTheory.ThetaSpecialise.psec_iff_of_isPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:58:58.10236+00:00
-- url     : https://prove2.me/submissions/312426ea-9821-4d93-b762-fb34d3bf8a1a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsFOfIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange
variable {X X' X'' Y Y' Y'' Y₁ Y₁' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {Φ : X' ⟶ X} {Φ' : X'' ⟶ X'}
  {K : Type} [Fintype K] {ε : K → ℤ}
variable {φ : K → (Y ⟶ X)} {φ₁ : K → (Y₁ ⟶ X)} {φ₂ : K → (Y₁' ⟶ X)} {a : Y₁ ⟶ Y} {b : Y₁' ⟶ Y₁}
  {s : LB.Sec (LB.LinComb L φ ε)} {t : LB.Sec (LB.LinComb L φ₁ ε)} {v : LB.Sec (LB.LinComb L φ₂ ε)}
variable {w : LB.Iso L' (L.pull Φ)} {φ' : K → (Y' ⟶ X')} {s' : LB.Sec (LB.LinComb L' φ' ε)}
namespace GlobalTheory.ThetaSpecialise
theorem _root_.solution {h₁ : Y' ⟶ Y₁} (hc : ∀ κ, φ' κ ≫ Φ = h₁ ≫ φ₁ κ) (H : IsPull a t s) {h : Y' ⟶ Y}
    (e : h₁ ≫ a = h) : PSec w φ' φ₁ ε h₁ s' t ↔ PSec w φ' φ ε h s' s := by
  unfold IsPull at H
  subst e
  unfold PSec
  refine forall_congr' fun Z => forall_congr' fun r => forall_congr' fun z => forall_congr' fun p =>
    forall_congr' fun q => imp_congr_right fun hp => imp_congr_right fun _ => ?_
  have hmem : ∀ κ, φ₁ κ ((r ≫ h₁) z) ∈ L.U (p κ) := fun κ => by
    have hκ := congrArg (fun g : Y' ⟶ X => g (r z)) (hc κ)
    simp only [Scheme.Hom.comp_apply] at hκ
    rw [Scheme.Hom.comp_apply, ← hκ]
    exact hp κ
  rw [H.2 Z (r ≫ h₁) z p hmem, Category.assoc]
end GlobalTheory.ThetaSpecialise
