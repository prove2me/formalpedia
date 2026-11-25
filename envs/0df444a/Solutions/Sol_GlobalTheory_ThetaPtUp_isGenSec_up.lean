-- Prove2me | solution 1 for GlobalTheory.ThetaPtUp.isGenSec_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:35:28.493435+00:00
-- url     : https://prove2.me/submissions/84d4e8d1-66a5-4ff7-9154-52f5bbc6ea8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HasThetaConstantsIffOfThetaLevelPullback
import Theorems.Thm_P2M_GlobalTheory_ThetaPtUp_exists_psi_inv__3417de49043e
import Theorems.Thm_GlobalTheory_ThetaAct_sv_ext
import Theorems.Thm_GlobalTheory_ThetaAct_sv_smul
import Theorems.Thm_GlobalTheory_ThetaPtMove_exists_secRel
import Theorems.Thm_GlobalTheory_ThetaPtMove_sv_of_eq_mul
import Theorems.Thm_P2M_GlobalTheory_ThetaPtMove_psi_fst__593f73f6caa4
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
theorem _root_.solution (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ}
    {th : LB.Sec (LPow A L₁ a T)} {th₀ : LB.Sec (LPow G L₀ a T₀)}
    (h : SecRel hp τ hτ w th th₀) (hg : IsGenSec A L₁ a th) : IsGenSec G L₀ a th₀ := by
  intro s₀
  obtain ⟨χ, -, h₂⟩ := exists_psi_inv' hp τ hτ
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ s₀
  obtain ⟨c, hc⟩ := hg s
  have e : χ ≫ (fst T A).left = (𝟙 _ ≫ (fst T₀ G).left) ≫ inv τ := by
    rw [← h₂, Category.assoc χ, psi_fst', Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have key : SecM.ofSec G s₀ = (inv τ).appTop.hom c • SecM.ofSec G th₀ := ThetaAct.sv_ext hL₀ fun y J hJ => by
    obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    have q := sv_of_eq_mul hc χ y hJ'
    have q₁ := hs _ χ y J J' hJ hJ'
    have q₂ := h _ χ y J J' hJ hJ'
    rw [h₂] at q₁ q₂
    refine Eq.trans ?_ (ThetaAct.sv_smul _ _ _ _ hJ).symm
    refine q₁.trans (Eq.trans ?_ (congrArg₂ (· * ·) (gs_pull _ (inv τ) y ⊤ trivial c) q₂).symm)
    rw [q, e, mul_left_comm]
  exact ⟨(inv τ).appTop.hom c, fun j => congrArg (fun q => q.1 j) key⟩
end GlobalTheory.ThetaPtUp
