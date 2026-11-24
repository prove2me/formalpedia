-- Prove2me | solution 1 for GlobalTheory.KS.VertReg.exists_cramer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:32:56.842402+00:00
-- url     : https://prove2.me/submissions/1276fd93-f9b4-47c1-bd88-c9c8ef20694c

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
private theorem rmul_rmul' {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (f : Γ(X, U)) :
    resG X h' (resG X h f) = resG X (h'.trans h) f := by
  show (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE h').op).hom f = _
  rw [← Functor.map_comp]
  rfl
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
namespace GlobalTheory.KS.VertReg
theorem _root_.solution {Y : Scheme.{0}} {n : ℕ} (O₁ O₂ : Y.Opens) (J : Matrix (Fin n) (Fin n) Γ(Y, O₁))
    (e : Fin n → Γ(Y, O₂)) (a : Fin n) :
    ∃ c : Γ(Y, Y.basicOpen J.det ⊓ O₂), ∀ y : Sp ℂ ⟶ Y, ⊤ ≤ y ⁻¹ᵁ (Y.basicOpen J.det ⊓ O₂) → ∀ w : Fin n → ℂ,
      (∀ b, valAt' y O₂ (e b) = ∑ i, w i * valAt' y O₁ (J i b)) → valAt' y _ c = w a := by
  classical
  have hb : Y.basicOpen J.det ⊓ O₂ ≤ O₁ := inf_le_left.trans (Y.basicOpen_le _)
  have hu : IsUnit (resG Y hb J.det) := by
    have h0 : IsUnit (resG Y (Y.basicOpen_le J.det) J.det) := Y.toRingedSpace.isUnit_res_basicOpen J.det
    have h1 := h0.map
      (resG Y (inf_le_left : Y.basicOpen J.det ⊓ O₂ ≤ Y.basicOpen J.det))
    rwa [rmul_rmul'] at h1
  let A : Matrix (Fin n) (Fin n) Γ(Y, Y.basicOpen J.det ⊓ O₂) := Matrix.transpose (J.map (resG Y hb))
  let v : Fin n → Γ(Y, Y.basicOpen J.det ⊓ O₂) := fun b => resG Y inf_le_right (e b)
  have hA : A.det = resG Y hb J.det := by
    rw [Matrix.det_transpose, RingHom.map_det]
    rfl
  refine ⟨↑hu.unit⁻¹ * (Matrix.mulVec A.adjugate v) a, ?_⟩
  intro y hy w hw
  obtain ⟨φ, hφ⟩ := exists_ringHom_eq_valAt'' y _ hy
  have hJ : ∀ i b, valAt' y O₁ (J i b) = φ (A b i) := fun i b => by
    rw [← hφ]
    exact (valAt'_resG_of_le y hb hy (J i b)).symm
  have he : ∀ b, valAt' y O₂ (e b) = φ (v b) := fun b => by
    rw [← hφ]
    exact (valAt'_resG_of_le y inf_le_right hy (e b)).symm
  let M := A.map φ
  have hM : Matrix.mulVec M w = fun b => φ (v b) := by
    funext b
    rw [← he, hw b]
    simp only [M, Matrix.mulVec, dotProduct, Matrix.map_apply, hJ]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hdet : φ ↑hu.unit = M.det := by
    rw [IsUnit.unit_spec, ← hA, RingHom.map_det]
    rfl
  have hne : M.det ≠ 0 := by
    rw [← hdet]
    exact (hu.unit.isUnit.map φ).ne_zero
  have hadj : φ ((Matrix.mulVec A.adjugate v) a) = (Matrix.mulVec M.adjugate (Matrix.mulVec M w)) a := by
    rw [RingHom.map_mulVec]
    have hm : A.adjugate.map φ = M.adjugate := RingHom.map_adjugate φ A
    rw [hm, hM]
    rfl
  rw [hφ, map_mul, map_units_inv, hadj, hdet, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul,
    inv_mul_cancel_left₀ hne]
end GlobalTheory.KS.VertReg
