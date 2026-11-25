-- Prove2me | solution 1 for GlobalTheory.ThetaSpecialise.PSec.pull_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:49:12.83438+00:00
-- url     : https://prove2.me/submissions/d8e05e7a-60f4-4906-9843-136d7b5ee001

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
namespace PSec
theorem _root_.solution {h : Y' ⟶ Y} (H : PSec w φ' φ ε h s' s) {φ₁' : K → (Y₁' ⟶ X')} {a' : Y₁' ⟶ Y'}
    {t' : LB.Sec (LB.LinComb L' φ₁' ε)} (H' : IsPull a' t' s') : PSec w φ₁' φ ε (a' ≫ h) t' s := by
  unfold IsPull at H'
  unfold PSec at H ⊢
  intro Z r z p q hp hq
  have hp' : ∀ κ, Φ (φ' κ ((r ≫ a') z)) ∈ L.U (p κ) := fun κ => by
    have hκ := hp κ
    rw [H'.1 κ, Scheme.Hom.comp_apply] at hκ
    rwa [Scheme.Hom.comp_apply]
  have hq' : ∀ κ, φ' κ ((r ≫ a') z) ∈ L'.U (q κ) := fun κ => by
    have hκ := hq κ
    rw [H'.1 κ, Scheme.Hom.comp_apply] at hκ
    rwa [Scheme.Hom.comp_apply]
  have e : ∀ κ, r ≫ φ₁' κ = (r ≫ a') ≫ φ' κ := fun κ => by rw [H'.1 κ, Category.assoc]
  have key := H Z (r ≫ a') z p q hp' hq'
  rw [Category.assoc] at key
  rw [H'.2 Z r z q hq, key]
  simp only [e]
end PSec
end GlobalTheory.ThetaSpecialise
