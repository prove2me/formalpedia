-- Prove2me | solution 1 for GlobalTheory.ThetaPtUp.exists_genThrough_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:12:03.891171+00:00
-- url     : https://prove2.me/submissions/75f596c1-5fb6-409c-b7c5-965d2afc427b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_HasThetaConstantsIffOfThetaLevelPullback
import Theorems.Thm_GlobalTheory_ThetaPtUp_exists_gen_up_iso
import Theorems.Thm_P2M_GlobalTheory_ThetaPtUp_exists_psi_inv__3417de49043e
import Theorems.Thm_P2M_GlobalTheory_ThetaPtMove_psi_snd__014c8d7c58c3
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
theorem _root_.solution (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a b : ℤ} {m : T ⊗ A ⟶ A}
    {m₀ : T₀ ⊗ G ⟶ G} (h : psi hp τ hτ ≫ m₀.left = m.left ≫ φ)
    (α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, m.left] ![a, b])) (hα : α.IsGen) :
    ∃ α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![(snd T₀ G).left, m₀.left] ![a, b]), α₀.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
        val α₀ (r ≫ psi hp τ hτ) z J =
          (wVal w z J J' (r ≫ (snd T A).left) ^ a * wVal w z J J' (r ≫ m.left) ^ b) * val α r z J' := by
  obtain ⟨χ, h₁, h₂⟩ := exists_psi_inv' hp τ hτ
  obtain ⟨α₀, hα₀, H⟩ := exists_gen_up_iso (φ := ![(snd T₀ G).left, m₀.left]) hw hL₀ hL₁ h₁ h₂
    (fun i => by
      fin_cases i
      · exact (psi_snd' hp τ hτ).symm
      · exact h.symm) α hα
  refine ⟨α₀, hα₀, fun Z r z J J' hJ hJ' => (H Z r z J J' hJ hJ').trans ?_⟩
  rw [Fin.prod_univ_two]
  rfl
end GlobalTheory.ThetaPtUp
