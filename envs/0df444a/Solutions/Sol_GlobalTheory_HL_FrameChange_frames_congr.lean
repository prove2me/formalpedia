-- Prove2me | solution 1 for GlobalTheory.HL.FrameChange.frames_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:32:11.402608+00:00
-- url     : https://prove2.me/submissions/47af62f1-a880-45dd-a25d-6c76d45c78af

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermFramesCongrModThetaUnitriangular
import Theorems.Thm_GlobalTheory_HL_FrameChange_diag_mul
import Theorems.Thm_GlobalTheory_HL_FrameChange_tri_coeffs
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_HL_TermBasic_term_basic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.FrameChange
namespace GlobalTheory.HL.FrameChange
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : Formalism.MainNotions.S.Loc.LocE F E) (r k : ℕ) (S : GlobalTheory.HL.Frames L r k) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (y x : Fin (r + 1) → S.V) (B B' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∀ a b, b < a → B a b = 0) → (∀ a, B a a = 1) → (∀ a b, b < a → B' a b = 0) → (∀ a, B' a a = 1) → (∀ b, y b = ∑ a, B a b • S.f a) → (∀ b, x b = ∑ a, B' a b • S.f' a) → (∀ a, y a ∈ Λ) → (∀ b, x b ∈ Λ) → ∃ ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ a b, ξ a b ∈ L.O) ∧ (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ ∀ b, S.InTh Λ (x b - ∑ a, ξ a b • y a) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT y x B B' hB0 hB1 hB'0 hB'1 hy hx hyΛ hxΛ
  obtain ⟨-, hW, -, t, t', hli, -, -⟩ := TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, hn, hn', -, -, hth, -⟩ := hW
  have hg : ∀ a (j : Fin r), hf L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
    simp [S.gram, Fin.castSucc_ne_last]
  have hg' : ∀ a (j : Fin r), hf L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
    simp [S.gram', Fin.castSucc_ne_last]
  have hl1 : LinearIndependent E (S.fr d Λ) := hli.comp Sum.inl Sum.inl_injective
  have hl2 : LinearIndependent E (S.fr' d Λ) := hli.comp Sum.inr Sum.inr_injective
  have hlf : LinearIndependent E S.f := by
    have := hl1.map' (S.wit d Λ).1.symm.toLinearMap (LinearEquiv.ker _)
    have e : S.f = ⇑((S.wit d Λ).1.symm.toLinearMap) ∘ S.fr d Λ := by
      funext a; simp [Frames.fr]
    rw [e]; exact this
  have hlf' : LinearIndependent E S.f' := by
    have := hl2.map' (S.wit d Λ).2.symm.toLinearMap (LinearEquiv.ker _)
    have e : S.f' = ⇑((S.wit d Λ).2.symm.toLinearMap) ∘ S.fr' d Λ := by
      funext a; simp [Frames.fr']
    rw [e]; exact this
  obtain ⟨C, hC0, hC1, hCy⟩ := tri_coeffs S hg hlf hn t y B hB0 hB1 hy hyΛ
  obtain ⟨C', hC'0, hC'1, hC'x⟩ := tri_coeffs S hg' hlf' hn' t' x B' hB'0 hB'1 hx hxΛ
  have hCt : C.BlockTriangular id := fun a b h => hC0 a b h
  have hC't : C'.BlockTriangular id := fun a b h => hC'0 a b h
  have hdet : C.det = 1 := by
    rw [Matrix.det_of_upperTriangular hCt]; simp [hC1]
  letI : Invertible C := Matrix.invertibleOfIsUnitDet C (by rw [hdet]; exact isUnit_one)
  have hCit : C⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hCt
  have hCi1 : ∀ a, C⁻¹ a a = 1 := fun a => by
    have h1 := diag_mul hCit hCt a
    rw [Matrix.inv_mul_of_invertible, hC1, mul_one] at h1
    simpa using h1.symm
  set D := C⁻¹ * C' with hD
  have hDt : D.BlockTriangular id := hCit.mul hC't
  have hCD : C * D = C' := by rw [hD, ← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul]
  choose w hwΛ hw using hth
  refine ⟨Matrix.of fun a b => ((D a b : L.O) : E), fun a b => (D a b).2, fun a b h => ?_, fun a => ?_,
    fun b => ?_⟩
  · simp [hDt h]
  · simp [hD, diag_mul hCit hC't, hCi1, hC'1]
  · have e1 : ∑ a, (Matrix.of fun a b => ((D a b : L.O) : E)) a b • y a =
        ∑ c, ((C' c b : L.O) : E) • (S.wit d Λ).1 (S.f c) := by
      simp only [Matrix.of_apply, hCy, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_smul, ← hCD, Matrix.mul_apply]
      push_cast
      simp only [mul_comm]
    refine ⟨∑ c, ((C' c b : L.O) : E) • w c, Λ.sum_mem fun c _ => Λ.smul_mem (C' c b) (hwΛ c), ?_⟩
    rw [e1, hC'x b, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← smul_sub, hw c, smul_comm]
end GlobalTheory.HL.FrameChange
