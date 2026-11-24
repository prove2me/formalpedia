-- Prove2me | solution 1 for GlobalTheory.RankFibreKer.sec_inv_mul_mem_slice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:11:32.929622+00:00
-- url     : https://prove2.me/submissions/a32ed6e5-a21b-40e2-83d4-04b7619744f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionInverseIntoSlice
import Theorems.Thm_GlobalTheory_RankFibreKer_eq_of_isFirstMax_of_isFirstMax
import Theorems.Thm_GlobalTheory_RankFibreKer_minor_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer
open GlobalTheory GlobalTheory.RankFibreKer
namespace GlobalTheory.RankFibreKer
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Y : Matrix (Fin a) (Fin d) k) (J : Fin a ↪ Fin d), IsFirstMax Y J →
    ((sec Y)⁻¹).val * Y ∈ slice k a d := by
  intro k _ _ _ _ a d Y J hJ
  have hex : ∃ J, IsFirstMax Y J := ⟨J, hJ⟩
  have hc : hex.choose = J := eq_of_isFirstMax_of_isFirstMax hex.choose_spec hJ
  have hs : (sec Y).val = Y.submatrix id J := by
    unfold sec
    rw [dif_pos hex]
    show Y.submatrix id hex.choose = _
    rw [hc]
  have hsub : (((sec Y)⁻¹).val * Y).submatrix id J = ((sec Y)⁻¹).val * Y.submatrix id J := by
    ext i j; simp [Matrix.mul_apply]
  have hdet : (((sec Y)⁻¹).val).det = (minor Y J)⁻¹ := by
    have e := congrArg Matrix.det (sec Y).inv_mul
    rw [Matrix.det_mul, Matrix.det_one, hs] at e
    exact eq_inv_of_mul_eq_one_left e
  refine ⟨J, ?_, fun J' => ?_⟩
  · rw [hsub, ← hs]; exact (sec Y).inv_mul
  · rw [minor_mul, hdet, map_mul, map_inv₀]
    have h0 : valuation k (minor Y J) ≠ 0 := by simpa using hJ.1
    constructor
    · rw [inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one]; exact (hJ.2 J').1
    · intro hl
      rw [inv_mul_lt_iff₀ (zero_lt_iff.2 h0), mul_one]; exact (hJ.2 J').2 hl
end GlobalTheory.RankFibreKer
