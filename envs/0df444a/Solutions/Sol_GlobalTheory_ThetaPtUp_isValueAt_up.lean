-- Prove2me | solution 1 for GlobalTheory.ThetaPtUp.isValueAt_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:32:54.386423+00:00
-- url     : https://prove2.me/submissions/8aa817f5-95cc-4591-8f46-5555d2609bf7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HasThetaConstantsIffOfThetaLevelPullback
import Theorems.Thm_GlobalTheory_ThetaPtMove_isValueAt_of_sv
import Theorems.Thm_GlobalTheory_ThetaPtMove_psi_ptSec
import Theorems.Thm_GlobalTheory_ThetaPtMove_ptSecT_snd
import Theorems.Thm_GlobalTheory_ThetaPtMove_sv_of_isValueAt
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
theorem _root_.solution (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ} {x : T ⟶ A} {x₀ : T₀ ⟶ G}
    (hx : τ ≫ x₀.left = x.left ≫ φ)
    {ρ₀ : LB.Gen (LB.LinComb L₀ (Y := T₀.left) (K := Fin 1) (fun _ => x₀.left) (fun _ => a))}
    {ρ : LB.Gen (LB.LinComb L₁ (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))}
    (H : GenThrough w _ _ _ ρ ρ₀ τ) {s₀ s} (hs : SecRel hp τ hτ w s s₀) {c : Γ(T.left, ⊤)}
    (H₁ : IsValueAt A L₁ a s x ρ c) : IsValueAt G L₀ a s₀ x₀ ρ₀ ((inv τ).appTop.hom c) := by
  refine isValueAt_of_sv hL₀ fun y J hJ => ?_
  obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
  have q := sv_of_isValueAt H₁ (inv τ) y hJ'
  have g : gs (𝟙 _) y ⊤ ((inv τ).appTop.hom c) = gs (inv τ) y ⊤ c :=
    (gs_pull (𝟙 _) (inv τ) y ⊤ trivial c).trans (by rw [Category.id_comp])
  rw [g, ← IsIso.inv_hom_id τ, H _ _ _ _ _ hJ hJ', Category.assoc, ← psi_ptSec hp τ hτ hx, ← Category.assoc,
    hs _ _ _ _ _ hJ hJ', q, Category.assoc, ptSecT_snd, Fin.prod_univ_one, Units.val_mul, mul_left_comm]
end GlobalTheory.ThetaPtUp
