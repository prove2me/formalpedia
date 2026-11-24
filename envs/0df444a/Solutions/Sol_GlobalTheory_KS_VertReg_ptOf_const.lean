-- Prove2me | solution 1 for GlobalTheory.KS.VertReg.ptOf_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:02:19.60753+00:00
-- url     : https://prove2.me/submissions/f374614b-5173-4438-8c37-6f889fec8ec4

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
import Theorems.Thm_GlobalTheory_KS_VertReg_resG_constFn
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
private theorem valAt'_constFn' {Y : Scheme.{0}} (y : Sp ℂ ⟶ Y) (q : Y ⟶ Sp ℂ) (hq : y ≫ q = 𝟙 _) (U : Y.Opens)
    (h : ⊤ ≤ y ⁻¹ᵁ U) (c : ℂ) : valAt' y U (constFn q U c) = c := by
  unfold valAt' constFn
  rw [dif_pos h]
  unfold valAt
  have e2 := congrArg (fun φ => CommRingCat.Hom.hom φ ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c))
    (Scheme.Hom.appLE_comp_appLE y q ⊤ U ⊤ (fun x _ => trivial) h)
  have key : ∀ (φ : Sp ℂ ⟶ Sp ℂ) (_ : φ = 𝟙 _) (e : ⊤ ≤ φ ⁻¹ᵁ ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((φ.appLE ⊤ ⊤ e).hom
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)) = c := by
    rintro φ rfl e
    simp [Scheme.Hom.appLE]
    change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (((Sp ℂ).presheaf.map (𝟙 (Opposite.op ⊤))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c)) = c
    rw [CategoryTheory.Functor.map_id]
    simp
  exact (congrArg (fun s => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom s) e2).trans (key _ hq _)
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
theorem _root_.solution {D : R → ℂ} (h : LocDer q p m D W₀ d) (y : Sp ℂ ⟶ Y) (hq : y ≫ q = 𝟙 _)
    (hy : ⊤ ≤ (y ≫ m) ⁻¹ᵁ W₀) (r : R) : ptOf W₀ d y ⊤ (constFn p ⊤ r) = D r := by
  unfold ptOf
  rw [resG_constFn, h.base _ inf_le_right r]
  exact valAt'_constFn' y q hq (m ⁻¹ᵁ (⊤ ⊓ W₀)) (fun a ha => ⟨trivial, hy ha⟩) (D r)
end GlobalTheory.KS.VertReg
