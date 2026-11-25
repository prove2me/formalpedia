-- Prove2me | solution 1 for GlobalTheory.HL.GoodClass.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:51:56.071551+00:00
-- url     : https://prove2.me/submissions/423b56e6-48b5-4987-a4bd-071aa2713e17

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetFrameClassProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitEntries
import Theorems.Thm_GlobalTheory_HL_GoodClass_UpU_mul
import Theorems.Thm_GlobalTheory_HL_GoodClass_UpU_det
import Theorems.Thm_GlobalTheory_HL_GoodClass_UpU_inv
import Theorems.Thm_GlobalTheory_HL_GoodClass_int_of_mul
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.GoodClass
variable {E : Type} [CommRing E] {n : ℕ}
namespace GlobalTheory.HL.GoodClass
theorem _root_.solution (O : Subring E) (W : Matrix (Fin n) (Fin n) E) (σ : Fin n → Fin n)
    (hσ : ∀ a, σ (σ a) = a) (hmono : ∀ a b : Fin n, a ≤ b → (a : ℕ) + σ a ≤ b + σ b)
    (h0 : ∀ a b, b ≠ σ a → W a b = 0) (hu : ∀ a, UnitIn O (W a (σ a)))
    (L U : Matrix (Fin n) (Fin n) E) (hL : UpU L.transpose) (hU : UpU U)
    (hZ : ∀ i j, (L * W * U) i j ∈ O) :
    ∃ D L₁ V U₁ : Matrix (Fin n) (Fin n) E, UpU D.transpose ∧ UpU L₁.transpose ∧ UpU V ∧ UpU U₁ ∧
      (∀ i j, L₁ i j ∈ O) ∧ (∀ i j, U₁ i j ∈ O) ∧ L = L₁ * D ∧ U = V * U₁ ∧ D * W * V = W := by
  choose e he using fun a => (hu a).2
  let β : Fin n → ℕ := fun a => (a : ℕ) + σ a
  have hβ : ∀ a, β (σ a) = β a := fun a => by simp only [β, hσ]; omega
  have hWl : ∀ (X : Matrix (Fin n) (Fin n) E) a b, (W * X) a b = W a (σ a) * X (σ a) b := by
    intro X a b
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ a)]
    · intro c _ hc; rw [h0 a c hc, zero_mul]
    · simp
  have hWr : ∀ (X : Matrix (Fin n) (Fin n) E) a b, (X * W) a b = X a (σ b) * W (σ b) b := by
    intro X a b
    rw [Matrix.mul_apply, Finset.sum_eq_single (σ b)]
    · intro c _ hc; rw [h0 c b (fun h => hc (by rw [h, hσ])), mul_zero]
    · simp
  let D : Matrix (Fin n) (Fin n) E := fun a b => if β a = β b then L a b else 0
  have hD : UpU D.transpose := by
    refine ⟨fun i j h => ?_, fun i => ?_⟩
    · have := hL.1 i j h
      simp only [Matrix.transpose_apply] at this ⊢
      simp [D, this]
    · have := hL.2 i
      simp only [Matrix.transpose_apply] at this ⊢
      simp [D, this]
  have hd : IsUnit D.det := by rw [← Matrix.det_transpose, hD.det]; exact isUnit_one
  letI := Matrix.invertibleOfIsUnitDet D hd
  have hb : D.BlockTriangular (OrderDual.toDual ∘ β) := by
    intro i j h
    have h' : β i < β j := h
    simp [D, h'.ne]
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hb
  have hL1 : ∀ a b, β a ≤ β b → (L * D⁻¹) a b = (1 : Matrix (Fin n) (Fin n) E) a b := by
    intro a b hab
    rw [← Matrix.mul_nonsing_inv D hd, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rcases lt_trichotomy (β a) (β c) with h | h | h
    · have h3 : a < c := by
        by_contra h4
        exact absurd (hmono c a (not_lt.1 h4)) (not_le.2 h)
      have := hL.1 c a h3
      simp only [Matrix.transpose_apply] at this
      simp [D, this]
    · simp [D, h]
    · have h' : β c < β b := lt_of_lt_of_le h hab
      rw [hi (show (OrderDual.toDual ∘ β) b < (OrderDual.toDual ∘ β) c from h'), mul_zero, mul_zero]
  let V : Matrix (Fin n) (Fin n) E := fun a b => e (σ a) * D (σ a) (σ b) * W (σ b) b
  have hV : UpU V := by
    refine ⟨fun i j h => ?_, fun i => ?_⟩
    · by_cases h1 : β (σ i) = β (σ j)
      · have h2 : σ i < σ j := by
          simp only [β, hσ] at h1
          rw [Fin.lt_def] at h ⊢
          omega
        have := hD.1 _ _ h2
        simp only [Matrix.transpose_apply] at this
        simp only [V, this, mul_zero, zero_mul]
      · simp [V, D, h1]
    · have h1 := hD.2 (σ i)
      have h2 := (he (σ i)).2
      simp only [Matrix.transpose_apply] at h1
      rw [hσ] at h2
      simp only [V, h1, mul_one]
      rw [mul_comm, h2]
  have hDW : D * W = W * V := by
    ext a b
    rw [hWl, hWr]
    simp only [V, hσ]
    linear_combination (-(D a (σ b) * W (σ b) b)) * (he a).2
  obtain ⟨V', hV', hVV⟩ := hV.inv
  have hLD : L = L * D⁻¹ * D := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul D hd, Matrix.mul_one]
  have hint := int_of_mul O (L * D⁻¹ * W) (V * U) (hV.mul hU) (fun m => ⟨σ m, by
      rw [hWr, hL1 _ _ le_rfl, Matrix.one_apply_eq, one_mul]
      have := hu (σ m)
      rwa [hσ] at this, fun m' hm => by
      rw [hWr, hL1 _ _ (by rw [hβ, hβ]; exact hmono _ _ hm.le), Matrix.one_apply_ne, zero_mul]
      intro h
      exact hm.ne (by rw [← hσ m, h, hσ])⟩) (by
      have : L * D⁻¹ * W * (V * U) = L * W * U := by
        conv_rhs => rw [hLD]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc W, ← hDW, Matrix.mul_assoc]
      rwa [this])
  refine ⟨D, L * D⁻¹, V', V * U, hD, ⟨fun i j h => ?_, fun i => ?_⟩, hV', hV.mul hU, fun i j => ?_,
    fun i j => (hint i).2 j, hLD, ?_, ?_⟩
  · rw [Matrix.transpose_apply, hL1 _ _ (hmono _ _ h.le), Matrix.one_apply_ne h.ne]
  · rw [Matrix.transpose_apply, hL1 _ _ le_rfl, Matrix.one_apply_eq]
  · have := O.mul_mem ((hint (σ j)).1 i) (he j).1
    rwa [hWr, hσ, mul_assoc, (he j).2, mul_one] at this
  · rw [← Matrix.mul_assoc, hVV, Matrix.one_mul]
  · rw [hDW, Matrix.mul_assoc, mul_eq_one_comm.1 hVV, Matrix.mul_one]
end GlobalTheory.HL.GoodClass
