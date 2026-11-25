-- Prove2me | solution 1 for GlobalTheory.ThetaCoord.exists_symLift_mulPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:16:09.784936+00:00
-- url     : https://prove2.me/submissions/f946349b-0211-42eb-b6b7-944e87aca150

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
import Theorems.Thm_GlobalTheory_ThetaCoord_lift_mulT
import Theorems.Thm_GlobalTheory_ThetaCoord_prod_tval
import Theorems.Thm_GlobalTheory_ThetaCoord_symLift_of_tval
import Theorems.Thm_GlobalTheory_ThetaCoord_exists_conj
import Theorems.Thm_GlobalTheory_CommutatorPairing_lift_translPt
import Theorems.Thm_GlobalTheory_CommutatorPairing_lift_translT
import Theorems.Thm_GlobalTheory_GlobalLift_val_symGen
import Theorems.Thm_GlobalTheory_SymLiftOdd_lift_negT
import Theorems.Thm_GlobalTheory_SymLiftOdd_lift_translPt
import Theorems.Thm_GlobalTheory_SymLiftOdd_lift_translT
import Theorems.Thm_GlobalTheory_SymLiftOdd_val_symGen
import Theorems.Thm_GlobalTheory_WeilMul_lift_translPt
import Theorems.Thm_GlobalTheory_WeilMul_lift_translT
import Theorems.Thm_P2M_GlobalTheory_SymLiftOdd_comp_pow__fae19791c0f2
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
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
theorem _root_.solution (hA : IsAbelianScheme A) (hL : L.IsLB) {a b : ℤ} {r q q' : ℕ} (hq : q ∣ q')
    {β : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (snd T A ^ r).left] ![a, -b])} (hβ : β.IsGen)
    {y : T ⟶ A} (hy : y ^ q' = 1) {θ : ThetaGrp A L b T} (H : SymLift A L b q (y ^ r) θ) :
    ∃ θ' : ThetaGrp A L a T, SymLift A L a q' y θ' ∧
      ∀ (T' : Over S) (π : T' ⟶ T) (z : T'.left) (J), Good L z J → ∀ p : T' ⟶ A,
        tval θ' (lift π p).left z J = bval β (lift π p).left z J * tval θ (lift π (p ^ r)).left z J *
          (bval β (lift π ((π ≫ y) * p)).left z J)⁻¹ := by
  have := hA.comm
  obtain ⟨ν, hν, hs⟩ := H.sym
  obtain ⟨u, hu, hv⟩ := exists_conj hL hβ (translT A y) (m := translPt A θ.pt) (m' := translPt A y) (lift_snd _ _)
    (by
      rw [mulT, SymLiftOdd.lift_translPt, H.pt_eq, MonObj.comp_pow, ← mul_pow]; rfl) θ.isGen
  obtain ⟨ν', hν', hw⟩ := exists_conj hL hβ (negT A T) (m := snd T A ≫ (GrpObj.inv : A ⟶ A))
    (m' := snd T A ≫ (GrpObj.inv : A ⟶ A)) (lift_snd _ _)
    (by
      rw [mulT, lift_snd_assoc]
      exact (inv_pow (snd T A) r).symm) hν
  have hv' : ∀ (T' : Over S) (π : T' ⟶ T) (z : T'.left) (J), Good L z J → ∀ p : T' ⟶ A,
      tval (⟨y, u, hu⟩ : ThetaGrp A L a T) (lift π p).left z J =
        bval β (lift π p).left z J * tval θ (lift π (p ^ r)).left z J *
          (bval β (lift π ((π ≫ y) * p)).left z J)⁻¹ := fun T' π z J hJ p => by
    rw [← lift_mulT, ← lift_translT]; exact hv _ _ z J hJ
  have hw' : ∀ (T' : Over S) (π : T' ⟶ T) (z : T'.left) (J), Good L z J → ∀ p : T' ⟶ A,
      nval ν' (lift π p).left z J = bval β (lift π p).left z J * nval ν (lift π (p ^ r)).left z J *
          (bval β (lift π p⁻¹).left z J)⁻¹ := fun T' π z J hJ p => by
    rw [← lift_mulT, ← lift_negT]; exact hw _ _ z J hJ
  refine ⟨⟨y, u, hu⟩, symLift_of_tval hL rfl hν' (fun T' π z J hJ p => ?_) (fun T' π z J hJ p => ?_), hv'⟩
  · let B : ℕ → (T'.left.presheaf.stalk z)ˣ := fun j => (bval β (lift π ((π ≫ y) ^ j * p)).left z J)⁻¹
    have e : ∀ j ∈ Finset.range q', tval (⟨y, u, hu⟩ : ThetaGrp A L a T) (lift π ((π ≫ y) ^ j * p)).left z J =
        tval θ (lift π ((π ≫ y ^ r) ^ j * p ^ r)).left z J * (B (j + 1) / B j) := fun j _ => by
      rw [hv' _ _ z J hJ, mul_pow, ← pow_mul, Nat.mul_comm, pow_mul, SymLiftOdd.comp_pow' π y r, ← _root_.mul_assoc (π ≫ y),
        ← pow_succ', div_inv_eq_mul]
      exact (fun x t w : (T'.left.presheaf.stalk z)ˣ => (by ac_rfl : x * t * w = t * (w * x))) _ _ _
    rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib, Finset.prod_range_div]
    have e₂ : B q' = B 0 := by
      simp only [B]
      rw [← MonObj.comp_pow, hy, MonObj.comp_one, pow_zero]
    rw [e₂, div_self', _root_.mul_one]
    obtain ⟨n, rfl⟩ := hq
    clear e e₂ hy
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.mul_succ, Finset.prod_range_add, ih, _root_.one_mul]
      refine Eq.trans (Finset.prod_congr rfl fun j _ => ?_) (prod_tval H π hJ ((π ≫ y ^ r) ^ (q * n) * p ^ r))
      rw [pow_add, mul_comm (_ ^ (q * n)), _root_.mul_assoc]
  · have s := val_corr hJ hs (lift π (p ^ r)).left
    rw [GlobalLift.val_symGen _ _ _ hJ, val_one, lift_translT, lift_negT, H.pt_eq, GrpObj.comp_inv] at s
    rw [hv' _ _ z J hJ, hv' _ _ z J hJ, hw' _ _ z J hJ, hw' _ _ z J hJ, mul_inv_cancel_left, mul_pow, inv_pow, inv_pow,
      ← MonObj.comp_pow, mul_inv (π ≫ y)⁻¹, inv_inv]
    apply Additive.ofMul.injective
    replace s := congrArg Additive.ofMul s
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at s ⊢
    linear_combination (norm := abel) s
end GlobalTheory.ThetaCoord
