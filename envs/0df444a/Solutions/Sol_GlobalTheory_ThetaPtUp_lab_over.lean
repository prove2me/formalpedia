-- Prove2me | solution 1 for GlobalTheory.ThetaPtUp.lab_over
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:18:54.777844+00:00
-- url     : https://prove2.me/submissions/59990319-9d74-41f4-a108-1760c687150f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HasThetaConstantsIffOfThetaLevelPullback
import Theorems.Thm_GlobalTheory_ThetaPtUp_map_linComb
import Theorems.Thm_GlobalTheory_ThetaPtMove_over_iff
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
theorem _root_.solution {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}
    {t : TObj g k J b s} {t' : TObj g k J b s'} {φ : t'.A.left ⟶ t.A.left} (hp : IsGrpPullback t'.A t.A f φ)
    (h : ∀ i, (t'.pt i).left ≫ φ = f ≫ (t.pt i).left) (a : Ix g k) :
    f ≫ (t.lab a).left = (t'.lab a).left ≫ φ := by
  have hf : f ≫ (baseOver S).hom = (baseOver S').hom ≫ f := (Category.comp_id _).trans (Category.id_comp _).symm
  refine (over_iff (T := baseOver _) (T₀ := baseOver _) hp f hf _ _).2 ?_
  rw [TObj.lab, TObj.lab, map_linComb, map_linComb]
  exact congrArg (linComb · _) (funext fun i => (over_iff (T := baseOver _) (T₀ := baseOver _) hp f hf _ _).1 (h i).symm)
end GlobalTheory.ThetaPtUp
