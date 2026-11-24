-- Prove2me | solution 1 for GlobalTheory.KS.Endo.ptDer_push
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:26:11.364647+00:00
-- url     : https://prove2.me/submissions/352257ef-79c1-47f8-bbe7-fd4e21beea2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EntireAntilinearLatticePeriodsConstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDifferentiableOnVerticalVectorFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerCommutesWithEndomorphism
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
namespace GlobalTheory.KS.Endo
private theorem valAt'_comp_lemma {Y Z : Scheme.{0}} (x : Sp ℂ ⟶ Y) (φ : Y ⟶ Z) (U : Z.Opens) (a : Γ(Z, U)) :
    valAt' (x ≫ φ) U a = valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom a) := by
  unfold valAt'
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U := h
    rw [dif_pos h, dif_pos h']
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ φ ⁻¹ᵁ U := h
    rw [dif_neg h, dif_neg h']
variable {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g) {X : Scheme.{0}}
end GlobalTheory.KS.Endo
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Endo
namespace GlobalTheory.KS.Endo
theorem _root_.solution {X Y : Scheme.{0}} (y : Sp ℂ ⟶ X) (f : X ⟶ Y) (δ : ∀ W : X.Opens, Γ(X, W) → ℂ) (h : PtDer y δ) :
    PtDer (y ≫ f) (fun W a => δ (f ⁻¹ᵁ W) ((f.app W).hom a)) where
  add W hW a b := by
    rw [map_add]
    exact h.add (f ⁻¹ᵁ W) hW _ _
  mul W hW a b := by
    rw [map_mul, valAt'_comp_lemma y f W a, valAt'_comp_lemma y f W b]
    exact h.mul (f ⁻¹ᵁ W) hW _ _
  res W W' hle hW a := by
    have hle' : f ⁻¹ᵁ W' ≤ f ⁻¹ᵁ W := fun x hx => hle hx
    have nat : (f.app W').hom (resG Y hle a) = resG X hle' ((f.app W).hom a) :=
      congrArg (fun φ : Γ(Y, W) ⟶ Γ(X, f ⁻¹ᵁ W') => φ.hom a) (f.naturality (homOfLE hle).op)
    rw [nat]
    exact h.res (f ⁻¹ᵁ W) (f ⁻¹ᵁ W') hle' hW _
end GlobalTheory.KS.Endo
