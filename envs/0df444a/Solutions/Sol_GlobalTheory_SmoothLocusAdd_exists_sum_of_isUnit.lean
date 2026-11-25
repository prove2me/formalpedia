-- Prove2me | solution 1 for GlobalTheory.SmoothLocusAdd.exists_sum_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:21:03.891409+00:00
-- url     : https://prove2.me/submissions/cddf8587-f717-4714-b289-b3a7b88bfc62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfLocallyRel
import Theorems.Thm_GlobalTheory_SmoothLocusAdd_isSumAt_ptHom
import Theorems.Thm_GlobalTheory_AddLaw_Represents_ne_zero
import Theorems.Thm_GlobalTheory_WeierstrassCurve_equation_of_forall_field
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
  AlgebraicGeometry
noncomputable section
open GlobalTheory GlobalTheory.SmoothLocusAdd
open GlobalTheory.WeierstrassCurve
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
open WeierstrassCurve.Projective
namespace GlobalTheory.SmoothLocusAdd
theorem _root_.solution {C : Type} [CommRing C] [_root_.IsReduced C] (ρ : R →+* C)
    {P Q S : Fin 3 → C} (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
    (nP : ∀ (k : Type) [Field k] (φ : C →+* k),
      (W.map (φ.comp ρ)).toProjective.Nonsingular (φ ∘ P))
    (nQ : ∀ (k : Type) [Field k] (φ : C →+* k),
      (W.map (φ.comp ρ)).toProjective.Nonsingular (φ ∘ Q))
    (hS : ∀ (k : Type) [Field k] (φ : C →+* k), φ ∘ S ≠ 0 →
      φ ∘ S ≈ (W.map (φ.comp ρ)).toProjective.add (φ ∘ P) (φ ∘ Q))
    (i : Fin 3) (hi : IsUnit (S i)) :
    ∃ h : IsUnimodularSol (W.map ρ) S, ∀ (k : Type) [Field k] (x : Spec (.of k) ⟶ Spec (.of C)),
      IsSumAt W (x ≫ ptHom W ρ P hP) (x ≫ ptHom W ρ Q hQ) (x ≫ ptHom W ρ S h) := by
  have hS' : ∀ (k : Type) [Field k] (φ : C →+* k),
      φ ∘ S ≈ (W.map (φ.comp ρ)).toProjective.add (φ ∘ P) (φ ∘ Q) := fun k _ φ =>
    hS k φ fun h0 => (hi.map φ).ne_zero (congrFun h0 i)
  have h : IsUnimodularSol (W.map ρ) S := .of_isUnit (equation_of_forall_field fun k _ φ =>
    ((nonsingular_of_equiv (hS' k φ)).mpr (nonsingular_add (nP k φ) (nQ k φ))).left) i hi
  refine ⟨h, fun k _ x => ?_⟩
  obtain ⟨φ, rfl⟩ := Spec.map_surjective x
  obtain ⟨φ, rfl⟩ : ∃ ψ : C →+* k, CommRingCat.ofHom ψ = φ := ⟨φ.hom, rfl⟩
  rw [SpecMap_ptHom, SpecMap_ptHom, SpecMap_ptHom]
  exact isSumAt_ptHom W _ _ _ _ (nP k φ) (nQ k φ) (hS' k φ)
end GlobalTheory.SmoothLocusAdd
