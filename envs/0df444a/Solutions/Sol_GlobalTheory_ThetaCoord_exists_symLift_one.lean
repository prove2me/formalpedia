-- Prove2me | solution 1 for GlobalTheory.ThetaCoord.exists_symLift_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:41:17.083474+00:00
-- url     : https://prove2.me/submissions/9743e44d-c1c7-4a93-a28c-b612757cda32

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
import Theorems.Thm_GlobalTheory_ThetaCoord_symLift_of_tval
import Theorems.Thm_GlobalTheory_ThetaAct_translPt_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


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
theorem _root_.solution (hL : L.IsLB) {ν : LB.Gen (negLB A L k T)} (hν : ν.IsGen) (q : ℕ) :
    ∃ θ : ThetaGrp A L k T, SymLift A L k q 1 θ ∧
      ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J → tval θ ρ z J = 1 := by
  obtain ⟨o, ho, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (translPt A (1 : T ⟶ A)).left]) (ε' := ![k, -k])
    (fun U _ f => (Fintype.prod_empty _).trans (by
      rw [Fin.prod_univ_two, ThetaAct.translPt_one]; simp))
    (LB.oneGen L) (fun i j => (map_one _).trans
      ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  have hv' : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      tval (⟨1, o, ho⟩ : ThetaGrp A L k T) ρ z J = 1 := fun Z ρ z J hJ => (hv _ _ z J hJ).trans (val_one _)
  refine ⟨⟨1, o, ho⟩, symLift_of_tval hL rfl hν (fun T' π z J hJ p => Finset.prod_eq_one fun j _ => hv' _ _ z J hJ)
    (fun T' π z J hJ p => ?_), hv'⟩
  rw [hv' _ _ z J hJ, hv' _ _ z J hJ, MonObj.comp_one, inv_one, _root_.one_mul, _root_.one_mul, _root_.one_mul,
    mul_inv_cancel]
end GlobalTheory.ThetaCoord
