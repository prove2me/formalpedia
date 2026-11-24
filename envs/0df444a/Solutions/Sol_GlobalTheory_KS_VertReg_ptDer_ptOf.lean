-- Prove2me | solution 1 for GlobalTheory.KS.VertReg.ptDer_ptOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:51:55.126954+00:00
-- url     : https://prove2.me/submissions/af61b5d7-8aa5-4c0b-b274-67b34b143f3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFibreCoordsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldAbelianVarietyAlgebraicStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueSectionOfLocallyRegularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LocDerRegularCoeff
import Theorems.Thm_GlobalTheory_KS_VertReg_resG_resG
import Theorems.Thm_GlobalTheory_KS_VertReg_val_res
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
namespace GlobalTheory.KS.VertReg
private theorem exists_ringHom_eq_valAt'' {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ∃ φ : Γ(Y, U) →+* ℂ, ∀ f, valAt' x U f = φ f := by
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (x.appLE U ⊤ h).hom, fun f => ?_⟩
  unfold valAt'
  rw [dif_pos h]
  rfl
private theorem valAt'_resG_of_le {Y : Scheme.{0}} (x : Sp ℂ ⟶ Y) {U V : Y.Opens} (hVU : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V)
    (f : Γ(Y, U)) : valAt' x V (resG Y hVU f) = valAt' x U f := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun _ ha => hVU (h ha)
  unfold valAt'
  rw [dif_pos h, dif_pos h']
  unfold valAt
  exact congrArg (fun s => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom s)
    (congrArg (fun φ => CommRingCat.Hom.hom φ f) (Scheme.Hom.map_appLE x h (homOfLE hVU).op))
private theorem valAt'_app_eq_valAt'_comp_moduli {Y Z : Scheme.{0}} (x : Sp ℂ ⟶ Y) (φ : Y ⟶ Z) (U : Z.Opens) (f : Γ(Z, U)) :
    valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f := by
  unfold valAt'
  by_cases hh : ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U
  · have hh' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := hh
    rw [dif_pos hh, dif_pos hh']
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · have hh' : ¬ ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := hh
    rw [dif_neg hh, dif_neg hh']
private theorem top_le_preimage_preimage_inf {Y X : Scheme.{0}} (y : Sp ℂ ⟶ Y) (m : Y ⟶ X) {U V : X.Opens}
    (h1 : ⊤ ≤ y ⁻¹ᵁ m ⁻¹ᵁ U) (h2 : ⊤ ≤ y ⁻¹ᵁ m ⁻¹ᵁ V) : ⊤ ≤ y ⁻¹ᵁ m ⁻¹ᵁ (U ⊓ V) :=
  fun _ ha => ⟨h1 ha, h2 ha⟩
variable {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp ℂ} {p : X ⟶ Sp R} {m : Y ⟶ X}
  {W₀ : X.Opens} {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
end GlobalTheory.KS.VertReg
namespace GlobalTheory.KS
open VertReg
end GlobalTheory.KS
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.VertReg
variable {R : Type} [CommRing R] {Y X : Scheme.{0}} {q : Y ⟶ Sp ℂ} {p : X ⟶ Sp R} {m : Y ⟶ X}
  {W₀ : X.Opens} {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
namespace GlobalTheory.KS.VertReg
theorem _root_.solution {D : R → ℂ} (h : LocDer q p m D W₀ d) (y : Sp ℂ ⟶ Y) (hy : ⊤ ≤ (y ≫ m) ⁻¹ᵁ W₀) :
    PtDer (y ≫ m) (ptOf W₀ d y) where
  add W _ f f' := by
    rename_i hW
    obtain ⟨φ, hφ⟩ := exists_ringHom_eq_valAt'' y (m ⁻¹ᵁ (W ⊓ W₀)) (top_le_preimage_preimage_inf y m hW hy)
    unfold ptOf
    rw [map_add, h.add _ inf_le_right]
    simp only [hφ, map_add]
  mul W hW f f' := by
    have hh : ⊤ ≤ y ⁻¹ᵁ m ⁻¹ᵁ (W ⊓ W₀) := top_le_preimage_preimage_inf y m hW hy
    obtain ⟨φ, hφ⟩ := exists_ringHom_eq_valAt'' y (m ⁻¹ᵁ (W ⊓ W₀)) hh
    have e1 : ∀ g : Γ(X, W), valAt' (y ≫ m) W g = φ ((m.app (W ⊓ W₀)).hom (resG X inf_le_left g)) := fun g => by
      rw [← hφ, valAt'_app_eq_valAt'_comp_moduli, valAt'_resG_of_le (y ≫ m) inf_le_left hh]
    unfold ptOf
    rw [e1 f, e1 f', map_mul, h.mul _ inf_le_right]
    simp only [hφ, map_add, map_mul]
  res W W' hle hW' f := by
    unfold ptOf
    rw [resG_resG, ← val_res h y (inf_le_inf_right W₀ hle) inf_le_right (top_le_preimage_preimage_inf y m hW' hy)
      (resG X inf_le_left f), resG_resG]
end GlobalTheory.KS.VertReg
