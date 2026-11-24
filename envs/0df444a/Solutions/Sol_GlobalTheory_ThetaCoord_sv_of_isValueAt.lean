-- Prove2me | solution 1 for GlobalTheory.ThetaCoord.sv_of_isValueAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:24:36.273681+00:00
-- url     : https://prove2.me/submissions/6db9b66f-8f01-4e36-96e1-891938a0e7a5

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of


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
theorem _root_.solution {s : LB.Sec (LPow A L k T)} {w : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => w.left) (fun _ => k))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L k s w τ v) (π : T' ⟶ T) {z : T'.left} {J} (hJ : Good L z J) :
    sv A s (lift π (π ≫ w)).left z J = gs π.left z ⊤ v * (val τ π.left z J).val := by
  have e₀ : (lift π (π ≫ w)).left = π.left ≫ (ptSecT A w).left := by
    rw [← Over.comp_left, ptSecT, comp_lift, Category.comp_id]
  have e : (ptSecT A w).left ≫ (snd T A).left = w.left := by rw [← Over.comp_left, ptSecT, lift_snd]
  have hz := hJ.mem (fun _ : Fin 1 => w.left) π.left
  rw [e₀]
  refine (sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s _ z J
    (fun _ => J (π.left ≫ w.left)) (fun _ => by rw [Category.assoc, e])).trans ?_
  have key : ∀ j : Fin 1 → L.ι, π.left z ∈ LB.wchart L (fun _ : Fin 1 => w.left) j →
      gs (π.left ≫ (ptSecT A w).left) z (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j) (s.f j) =
        gs π.left z ⊤ v * (gm π.left z (LB.wchart L (fun _ : Fin 1 => w.left) j) (τ.s j)).val := fun j hz =>
    ((gs_res π.left z (val_le A L w j) hz _).trans (gs_pull π.left (ptSecT A w).left z
      (LB.wchart L (fun _ : Fin 1 => (snd T A).left) j) (val_le A L w j hz) (s.f j))).symm.trans
    ((congrArg (gs π.left z _) (H j)).trans ((gs_mul π.left z _ hz _ _).trans
      (congrArg₂ (· * ·) (gs_res π.left z le_top hz _) (gs_unit π.left z _ hz _))))
  exact key _ hz
end GlobalTheory.ThetaCoord
