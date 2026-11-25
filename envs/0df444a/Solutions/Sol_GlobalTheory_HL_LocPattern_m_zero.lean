-- Prove2me | solution 1 for GlobalTheory.HL.LocPattern.m_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:30:43.94203+00:00
-- url     : https://prove2.me/submissions/0949a9a8-1256-4ae4-be85-3a205d917445

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RationalExtend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LocalCommonStabiliserBlockUnitriangularOnFrame
import Theorems.Thm_GlobalTheory_HL_LocPattern_zh_split
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_FrameBasic_main
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LocPattern
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
namespace GlobalTheory.HL.LocPattern
theorem _root_.solution [IsNonarchimedeanLocalField F] [CharZero F]
    (m m' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hm' : (∀ i j, j < i → m' i j = 0) ∧ (∀ i, m' i i = 1))
    (heq : cT L m * S.Zh * m' = S.Zh) (l : Fin (r + 2)) (hl : S.D l ≠ 0) (a b : Fin (r + 1))
    (ha : (a : ℕ) < l) (hb : (l : ℕ) ≤ b) : m a b = 0 := by
  obtain ⟨-, -, -, hU, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hU' : IsUnit S.Zh.det := hU
  have hbt : m'.BlockTriangular id := by
    intro i j hij; exact hm'.1 i j hij
  have hdet : IsUnit m'.det := by
    rw [Matrix.det_of_upperTriangular hbt]; simp [hm'.2]
  letI := Matrix.invertibleOfIsUnitDet m' hdet
  have hN : (m'⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  have h1 : cT L m * S.Zh = S.Zh * m'⁻¹ := by
    calc cT L m * S.Zh = cT L m * S.Zh * m' * m'⁻¹ := by
          rw [Matrix.mul_assoc (cT L m * S.Zh) m', Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = S.Zh * m'⁻¹ := by rw [heq]
  let v : Fin (r + 1) → E := fun x => if (x : ℕ) < l then L.cj (m x b) else 0
  have hv : Matrix.vecMul v S.Zh = 0 := by
    funext y
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    by_cases hy : (y : ℕ) < l
    · have h2 := congrFun (congrFun h1 b) y
      rw [Matrix.mul_apply, Matrix.mul_apply] at h2
      have h3 : ∑ z, S.Zh b z * m'⁻¹ z y = 0 := Finset.sum_eq_zero fun z _ => by
        by_cases hz : (z : ℕ) ≤ y
        · rw [zh_split S l hl b z (Or.inr ⟨by omega, hb⟩), zero_mul]
        · rw [hN (show y < z from Fin.lt_def.2 (by omega)), mul_zero]
      rw [h3] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [v, cT]
      split_ifs with hx
      · rfl
      · simp [zh_split S l hl x y (Or.inr ⟨hy, by omega⟩)]
    · refine Finset.sum_eq_zero fun x _ => ?_
      simp only [v]
      split_ifs with hx
      · rw [zh_split S l hl x y (Or.inl ⟨hx, by omega⟩), mul_zero]
      · rw [zero_mul]
  have hv0 : v = 0 := Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hU')
    (hv.trans (Matrix.zero_vecMul _).symm)
  have := congrFun hv0 a
  simp only [v, if_pos ha, Pi.zero_apply] at this
  exact (map_eq_zero_iff L.cj L.cj.injective).1 this
end GlobalTheory.HL.LocPattern
