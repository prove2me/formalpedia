-- Prove2me | solution 1 for GlobalTheory.ThetaCoord.sym_tval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:09:05.637049+00:00
-- url     : https://prove2.me/submissions/f19dbdb8-7825-43d7-b676-675a8df0843f

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
import Theorems.Thm_GlobalTheory_ThetaCoord_lift_translT
import Theorems.Thm_GlobalTheory_ThetaCoord_lift_negT
import Theorems.Thm_GlobalTheory_ThetaCoord_lift_fst_left
import Theorems.Thm_GlobalTheory_CommPairing_surj_fst
import Theorems.Thm_GlobalTheory_CommPairing_val_div_eq
import Theorems.Thm_GlobalTheory_CommutatorPairing_lift_translT
import Theorems.Thm_GlobalTheory_CommutatorPairing_surj_fst
import Theorems.Thm_GlobalTheory_GlobalLift_val_symGen
import Theorems.Thm_GlobalTheory_SymLiftOdd_lift_negT
import Theorems.Thm_GlobalTheory_SymLiftOdd_lift_translT
import Theorems.Thm_GlobalTheory_SymLiftOdd_surj_fst
import Theorems.Thm_GlobalTheory_SymLiftOdd_val_symGen
import Theorems.Thm_GlobalTheory_WeilMul_lift_translT
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pt_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
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
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB) {n : ℕ} {x : T ⟶ A}
    {θ : ThetaGrp A L k T} (H : SymLift A L k n x θ) {ν : LB.Gen (negLB A L k T)} (hν : ν.IsGen) (π : T' ⟶ T)
    {z : T'.left} {J} (hJ : Good L z J) (p : T' ⟶ A) :
    tval θ (lift π ((π ≫ x)⁻¹ * p)).left z J * nval ν (lift π p).left z J *
      (tval θ (lift π p⁻¹).left z J * (nval ν (lift π ((π ≫ x)⁻¹ * p)).left z J)⁻¹) = 1 := by
  obtain ⟨ν', hν', hs⟩ := H.sym
  have q := val_corr hJ hs (lift π p).left
  rw [GlobalLift.val_symGen _ _ _ hJ, val_one, lift_translT, lift_negT, H.pt_eq, GrpObj.comp_inv] at q
  have w : nval ν (lift π p).left z J * (nval ν' (lift π p).left z J)⁻¹ =
      nval ν (lift π ((π ≫ x)⁻¹ * p)).left z J * (nval ν' (lift π ((π ≫ x)⁻¹ * p)).left z J)⁻¹ :=
    val_div_eq hL (fst T A).left (surj_fst hG hA T) hν hν' _ _ (by rw [lift_fst_left, lift_fst_left]) z J hJ
  apply Additive.ofMul.injective
  replace q := congrArg Additive.ofMul q
  replace w := congrArg Additive.ofMul w
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at q w ⊢
  linear_combination (norm := abel) q + w
end GlobalTheory.ThetaCoord
