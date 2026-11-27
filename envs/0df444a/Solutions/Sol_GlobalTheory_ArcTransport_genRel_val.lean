-- Prove2me | solution 1 for GlobalTheory.ArcTransport.genRel_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:01:43.129611+00:00
-- url     : https://prove2.me/submissions/ab1eeeb7-bf8f-429c-acec-6a227f4f430e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsCommonField
import Theorems.Thm_P2M_GlobalTheory_ArcTransport_exists_good__b067f9275064
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_genRel_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pw_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ArcTransport
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
variable {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]
variable {F : Type} [Field F]
namespace GlobalTheory.ArcTransport
theorem _root_.solution {w : LB.Iso L' (L.pull Φ)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {pt : K → (Sp F ⟶ X')}
    {pt₀ : K → (Sp F ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L' pt ε)} {t₀ : LB.Gen (LB.LinComb L pt₀ ε)}
    (ht : t.IsGen) (ht₀ : t₀.IsGen) (x : Fˣ) :
    GenRel w t t₀ (x : F) ↔ (∀ k, pt k ≫ Φ = pt₀ k) ∧ ∀ (y : Sp F) J J', Good L y J → Good L' y J' →
      (∏ k, Geo.Tor.gw w (pt k) y (J (pt k ≫ Φ)) (J' (pt k)) ^ ε k) * vS t y J' = unitStk y x * vS t₀ y J := by
  have z : Sp F := (default : PrimeSpectrum F)
  constructor
  · intro H
    refine ⟨H.1, fun y J J' hJ hJ' => ?_⟩
    obtain ⟨hp, H⟩ := (genRel_iff w t t₀ x y).1 H
    obtain rfl : (fun k => pt k ≫ Φ) = pt₀ := funext hp
    have := H (fun k => J' (pt k)) (fun k => J (pt k ≫ Φ)) (fun k => hJ (pt k ≫ Φ)) (fun k => hJ' (pt k))
    rw [vS, vS, val_of t _ y J' (fun k => J' (pt k)) (fun k => by rw [Category.id_comp]),
      val_of t₀ _ y J (fun k => J (pt k ≫ Φ)) (fun k => by rw [Category.id_comp])]
    exact Units.ext this
  · rintro ⟨hp, H⟩
    obtain rfl : (fun k => pt k ≫ Φ) = pt₀ := funext hp
    refine (genRel_iff w t t₀ x z).2 ⟨hp, fun j j₀ h₀ h₁ => ?_⟩
    obtain ⟨J, hJ⟩ := exists_good' hL z
    obtain ⟨J', hJ'⟩ := exists_good' hL' z
    have H' := H z J J' hJ hJ'
    rw [vS, vS, val_of t _ z J' (fun k => J' (pt k)) (fun k => by rw [Category.id_comp]),
      val_of t₀ _ z J (fun k => J (pt k ≫ Φ)) (fun k => by rw [Category.id_comp])] at H'
    have m₀ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart L (fun k => pt k ≫ Φ) j₀ := Set.mem_iInter.2 h₀
    have m₁ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart L' pt j := Set.mem_iInter.2 h₁
    have n₀ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart L (fun k => pt k ≫ Φ) (fun k => J (pt k ≫ Φ)) :=
      Set.mem_iInter.2 fun k => hJ (pt k ≫ Φ)
    have n₁ : (𝟙 (Sp F) : Sp F ⟶ Sp F) z ∈ LB.wchart L' pt (fun k => J' (pt k)) :=
      Set.mem_iInter.2 fun k => hJ' (pt k)
    have a := pw_trans hw pt ε (𝟙 _) z m₀ n₀ m₁ n₁
    simp only [pw, Category.id_comp] at a
    have key : (∏ k, Geo.Tor.gw w (pt k) z (j₀ k) (j k) ^ ε k) * gm (𝟙 _) z (LB.wchart L' pt j) (t.s j) =
        unitStk z x * gm (𝟙 _) z (LB.wchart L (fun k => pt k ≫ Φ) j₀) (t₀.s j₀) := by
      rw [a, gen_trans ht (𝟙 _) z m₁ n₁, gen_trans ht₀ (𝟙 _) z m₀ n₀]
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul H'
      simp only [ofMul_mul, ofMul_inv] at e' ⊢
      linear_combination (norm := abel) e'
    exact congrArg Units.val key
end GlobalTheory.ArcTransport
