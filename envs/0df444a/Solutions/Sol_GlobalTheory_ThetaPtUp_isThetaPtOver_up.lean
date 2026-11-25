-- Prove2me | solution 1 for GlobalTheory.ThetaPtUp.isThetaPtOver_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:21:39.495038+00:00
-- url     : https://prove2.me/submissions/e3e66e7a-1513-433c-adc8-33b388db49fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HasThetaConstantsIffOfThetaLevelPullback
import Theorems.Thm_GlobalTheory_ThetaPtUp_exists_gen_up_iso
import Theorems.Thm_GlobalTheory_ThetaPtUp_exists_genThrough_up
import Theorems.Thm_GlobalTheory_ThetaPtUp_isTwistPull_up
import Theorems.Thm_GlobalTheory_ThetaPtUp_isValueAt_up
import Theorems.Thm_GlobalTheory_ThetaPtUp_isGenSec_up
import Theorems.Thm_GlobalTheory_ThetaPtUp_symLift_up
import Theorems.Thm_GlobalTheory_ThetaPtMove_exists_secRel_up
import Theorems.Thm_GlobalTheory_ThetaPtMove_over_one
import Theorems.Thm_GlobalTheory_ThetaPtMove_psi_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ThetaPtUp
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift GlobalTheory.ThetaPtMove
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) [IsIso τ] (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}
namespace GlobalTheory.ThetaPtUp
theorem _root_.solution {P₀ : PolAV S} {P : PolAV S'} {φ : P.A.left ⟶ P₀.A.left}
    (hp : IsGrpPullback P.A P₀.A f φ) (hw : LBIso P.L (P₀.L.pull φ)) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
    {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {x₀ : I → (T₀ ⟶ P₀.A)} (hx : ∀ i, τ ≫ (x₀ i).left = (x i).left ≫ φ)
    (hk : ∀ i, x i ^ (k ^ 2) = 1) {v : I → Γ(T.left, ⊤)} (H : IsThetaPtOver P k x v) :
    IsThetaPtOver P₀ k x₀ (fun i => (inv τ).appTop.hom (v i)) := by
  obtain ⟨w, hw⟩ := hw
  have hL₀ := P₀.isLB
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨th₀, s₀, α₀, ρ₀, U₀, t₀, c₀, u₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩ := H
  obtain ⟨th, hth⟩ := exists_secRel_up hp τ hτ hw hL₀ hL₁ th₀
  obtain ⟨s, hs⟩ := exists_secRel_up hp τ hτ hw hL₀ hL₁ s₀
  choose t ht using fun i => exists_secRel_up hp τ hτ hw hL₀ hL₁ (t₀ i)
  obtain ⟨α, hα, vα⟩ := exists_genThrough_up hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ k) α₀ h₂
  obtain ⟨ρ, hρ, vρ⟩ := exists_gen_up_iso (φ := fun _ : Fin 1 => (1 : T₀ ⟶ P₀.A).left) (h := τ) hw hL₀ hL₁
    (IsIso.hom_inv_id τ) (IsIso.inv_hom_id τ) (fun _ => (over_one hp τ hτ).symm) ρ₀ h₃
  choose U hU hU' using fun i => symLift_up hp τ hτ hw hL₀ hL₁ (hx i) (hk i) (h₅ i)
  refine ⟨th, s, α, ρ, U, t, fun i => (inv τ).appTop.hom (c₀ i), Units.map (inv τ).appTop.hom.toMonoidHom u₀,
    isGenSec_up hp τ hτ hw hL₀ hL₁ hth h₁, hα, hρ,
    isTwistPull_up hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ k) hα vα hth hs h₄, hU,
    fun i => hU' i _ _ _ _ hs (ht i) (h₆ i),
    fun i => isValueAt_up hp τ hτ hL₀ hL₁ (over_one hp τ hτ) vρ (ht i) (h₇ i), fun i => ?_⟩
  exact (congrArg (inv τ).appTop.hom (h₈ i)).trans (map_mul _ _ _)
end GlobalTheory.ThetaPtUp
