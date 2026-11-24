-- Prove2me | solution 1 for GlobalTheory.ThetaCoord.exists_unit_of_isGenSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:23:07.002045+00:00
-- url     : https://prove2.me/submissions/1d5146c4-c111-48d2-a653-6470733d8900

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfLocalOnBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SymmetricLiftOddOrderExistsUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Statements_TorsionEndomorphisms_ExistsGeneratorOfIsField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverOfSubsingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaCoord
open CommPairing GlobalLift VVRank
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T T' : Over S} {k : ℤ}
namespace GlobalTheory.ThetaCoord
theorem _root_.solution [Subsingleton T.left] {th th' : LB.Sec (LPow A L k T)}
    (H : IsGenSec A L k th) (H' : IsGenSec A L k th') :
    ∃ u : Γ(T.left, ⊤)ˣ, SecM.ofSec A th = (u : Γ(T.left, ⊤)) • SecM.ofSec A th' := by
  obtain ⟨r, hr⟩ := H' th
  obtain ⟨r', hr'⟩ := H th'
  have e : SecM.ofSec A th = r • SecM.ofSec A th' := Subtype.ext (funext hr)
  have e' : SecM.ofSec A th' = r' • SecM.ofSec A th := Subtype.ext (funext hr')
  by_cases hu : IsUnit r
  · exact ⟨hu.unit, e⟩
  have h₁ : IsUnit (1 - r * r') := T.left.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun p _ => by
    rw [map_sub, map_one, map_mul]
    refine (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_left fun h => hu ?_
    refine T.left.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun p' _ => ?_
    obtain rfl : p = p' := Subsingleton.elim (α := T.left) _ _
    exact isUnit_of_mul_isUnit_left h
  have h₂ : SecM.ofSec A th = 0 := h₁.smul_eq_zero.1 (by rw [sub_smul, one_smul, mul_smul, ← e', ← e, sub_self])
  exact ⟨1, by rw [e', h₂, smul_zero, smul_zero]⟩
end GlobalTheory.ThetaCoord
