-- Prove2me | solution 1 for GlobalTheory.ThetaSpecialise.exists_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:24:13.429843+00:00
-- url     : https://prove2.me/submissions/7b140d1e-2b41-48c0-97d1-2fd85af19a31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMoveMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsFOfIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_psi_fst
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_psi_snd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange
variable {S₀ S₁ : Scheme.{0}} {G : Over S₀} [GrpObj G] {A : Over S₁} [GrpObj A]
  {f : S₁ ⟶ S₀} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S₁} {T₀ : Over S₀} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left}
include hp hτ
namespace GlobalTheory.ThetaSpecialise
theorem _root_.solution : ∃ ψ : (T ⊗ A).left ⟶ (T₀ ⊗ G).left, IsPullback ψ (fst T A).left (fst T₀ G).left τ ∧
    ψ ≫ (snd T₀ G).left = (snd T A).left ≫ φ ∧ ψ = (psiO hp τ hτ).left := by
  refine ⟨(psiO hp τ hτ).left, ?_, psi_snd hp τ hτ, rfl⟩
  have h₀ : IsPullback (snd T₀ G).left (fst T₀ G).left G.hom T₀.hom := (IsPullback.of_hasPullback _ _).flip
  have h₁ : IsPullback (snd T A).left (fst T A).left A.hom T.hom := (IsPullback.of_hasPullback _ _).flip
  refine IsPullback.of_right ?_ (psi_fst hp τ hτ) h₀
  rw [psi_snd, hτ]
  exact h₁.paste_horiz hp.1
end GlobalTheory.ThetaSpecialise
