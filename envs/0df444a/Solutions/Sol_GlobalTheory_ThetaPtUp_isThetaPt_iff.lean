-- Prove2me | solution 1 for GlobalTheory.ThetaPtUp.isThetaPt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:18:37.427859+00:00
-- url     : https://prove2.me/submissions/e6f45b9f-4f9f-4a57-85c2-b70b50688ed7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HasThetaConstantsIffOfThetaLevelPullback
import Theorems.Thm_GlobalTheory_ThetaPtUp_isThetaPtOver_up
import Theorems.Thm_GlobalTheory_ThetaPtUp_isThetaPtOver_down
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
omit τ
namespace GlobalTheory.ThetaPtUp
theorem _root_.solution {P₀ : PolAV S} {P : PolAV S'} {φ : P.A.left ⟶ P₀.A.left}
    (hp : IsGrpPullback P.A P₀.A f φ) (hw : LBIso P.L (P₀.L.pull φ))
    {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {x₀ : I → (Over.mk (T.hom ≫ f) ⟶ P₀.A)}
    (hx : ∀ i, (x₀ i).left = (x i).left ≫ φ) (hk : ∀ i, x i ^ (k ^ 2) = 1) (v : I → Γ(T.left, ⊤)) :
    IsThetaPt P k x v ↔ IsThetaPt P₀ k x₀ v := by
  refine and_congr_right fun _ => and_congr_right fun _ =>
    forall_congr' fun p => exists_congr fun V => and_congr_right fun _ => ?_
  let V₀ : (Over.mk (T.hom ≫ f)).left.Opens := V
  let τ : (overRes V).left ⟶ (overRes V₀).left := 𝟙 V.toScheme
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 V.toScheme))
  have hτ : τ ≫ (overRes V₀).hom = (overRes V).hom ≫ f := (Category.id_comp _).trans (Category.assoc _ _ _).symm
  have mv : ∀ i, τ ≫ (overResι V₀ ≫ x₀ i).left = (overResι V ≫ x i).left ≫ φ := fun i =>
    (Category.id_comp _).trans ((congrArg (V.ι ≫ ·) (hx i)).trans (Category.assoc _ _ _).symm)
  have hk' : ∀ i, (overResι V ≫ x i) ^ (k ^ 2) = 1 := fun i => by
    rw [← MonObj.comp_pow, hk, MonObj.comp_one]
  have hi : inv τ = 𝟙 V.toScheme := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
  refine ⟨fun H => ?_, fun H => isThetaPtOver_down τ hp hw hτ mv hk' H⟩
  have Q := isThetaPtOver_up τ hp hw hτ mv hk' H
  rw [hi] at Q
  exact Q
end GlobalTheory.ThetaPtUp
