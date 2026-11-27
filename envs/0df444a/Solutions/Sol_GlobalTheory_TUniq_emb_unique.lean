-- Prove2me | solution 1 for GlobalTheory.TUniq.emb_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:37:48.438476+00:00
-- url     : https://prove2.me/submissions/2a216b29-f710-4bf9-b323-4de31e164ae8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCompatOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordOfRatio
import Theorems.Thm_GlobalTheory_TUniq_secCoord_of_sv
import Theorems.Thm_GlobalTheory_CommPairing_surj_fst
import Theorems.Thm_GlobalTheory_CommPairing_val_div_eq
import Theorems.Thm_GlobalTheory_CommutatorPairing_surj_fst
import Theorems.Thm_GlobalTheory_SymLiftOdd_surj_fst
import Theorems.Thm_GlobalTheory_SymLiftOdd_symLift_unique
import Theorems.Thm_GlobalTheory_TUniq_GeoGood_symm
import Theorems.Thm_GlobalTheory_ThetaAct_sv_smul
import Theorems.Thm_GlobalTheory_ThetaCoord_exists_unit_of_isGenSec
import Theorems.Thm_GlobalTheory_VVRank_sv_of_isTwistPull
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pt_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_corr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.TUniq
open GlobalTheory.SegreCoord ReciprocityTheory.ChartRestriction.G.Out
variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {S S' : Scheme.{0}} {s : S ⟶ Sp o}
  {s' : S' ⟶ Sp o}
namespace GlobalTheory.TUniq
theorem _root_.solution (hG : GlobalFnsSt) (t : TObj g (N' ^ 2) J b s) {m : ℕ} (hm : Odd m) {T : Over S}
    [Subsingleton T.left] {σ σ'} (H : t.Emb m T σ) (H' : t.Emb m T σ') {B : Type} [Field B]
    (y : Sp B ⟶ (T ⊗ t.A).left) {w} (h : SecCoord _ σ y w) : SecCoord _ σ' y w := by
  obtain ⟨th, s₁, α, U, h₁, h₂, h₄, h₅, h₆⟩ := H
  obtain ⟨th', s₁', α', U', h₁', h₂', h₄', h₅', h₆'⟩ := H'
  have hL := t.isLB
  obtain ⟨c, hc⟩ := ThetaCoord.exists_unit_of_isGenSec h₁' h₁
  let p : Sp B := (default : PrimeSpectrum B)
  obtain ⟨I, hI⟩ := ConstFam.exists_good' hL p
  refine secCoord_of_sv hL p hI hI
    (val α' y p I * (val α y p I)⁻¹ * gm (y ≫ (fst T t.A).left) p ⊤ c) (fun a => ?_) h
  have e₀ : (U' a).pt = (U a).pt := (h₅' a).pt_eq.trans (h₅ a).pt_eq.symm
  have e₁ := val_corr hI (SymLiftOdd.symLift_unique hG t.ab hL hm.pow _ _ (h₅' a) (h₅ a)) y
  have f₁ : (y ≫ (translT t.A (U a).pt).left) ≫ (fst T t.A).left = y ≫ (fst T t.A).left := by
    rw [Category.assoc, ← Over.comp_left, translT, lift_fst]
  have f₂ : ((y ≫ (translT t.A (U a).pt).left) ≫ (mulT t.A T m).left) ≫ (fst T t.A).left = y ≫ (fst T t.A).left := by
    rw [Category.assoc, ← Over.comp_left, mulT, lift_fst, f₁]
  have e₂ := CommPairing.val_div_eq hL (fst T t.A).left (CommPairing.surj_fst hG t.ab T) h₂' h₂ _ _ f₁ p I hI
  have e₃ := ThetaAct.sv_smul (c : Γ(T.left, ⊤)) (SecM.ofSec t.A th)
    ((y ≫ (translT t.A (U a).pt).left) ≫ (mulT t.A T m).left) p hI
  rw [← hc, f₂, gs_unit _ _ ⊤ trivial] at e₃
  rw [VVRank.sv_of_isTwistPull t.A (h₆ a) y p hI, VVRank.sv_of_isTwistPull t.A (h₆' a) y p hI,
    VVRank.sv_of_isTwistPull t.A h₄ _ p hI, VVRank.sv_of_isTwistPull t.A h₄' _ p hI, ← e₂]
  erw [e₁]
  rw [e₀]
  rw [show VVRank.sv t.A th' _ p I = _ * VVRank.sv t.A th _ p I from e₃]
  simp only [Units.val_mul]
  have key : ∀ {Q : Type} [CommRing Q] (a a' : Qˣ) (x y z : Q), x * (a' * (y * z)) = a' * ↑a⁻¹ * y * (x * (a * z)) :=
    fun a a' x y z => by linear_combination (-(x * a' * y * z)) * a.inv_mul
  exact key _ _ _ _ _
end GlobalTheory.TUniq
