-- Prove2me | solution 1 for GlobalTheory.NormLe.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:29:29.960958+00:00
-- url     : https://prove2.me/submissions/f84a5ea2-dbf0-489c-9c41-dfa3d2afa610

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormLeAbsNormMulDivAbsNormOfEisensteinIndexPa
import Theorems.Thm_GlobalTheory_NormLe_absNorm_le_abs_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open GlobalTheory GlobalTheory.NormLe
namespace GlobalTheory.NormLe
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (p : QPair 𝔞 𝔟),
    |(Algebra.norm ℚ p.1.1 : ℝ)| ≤ |(Algebra.norm ℚ (p.1.1 * p.1.2) : ℝ)| / nrm 𝔟 := by
  intro F _ _ _ 𝔞 𝔟 p
  obtain ⟨⟨ν, b⟩, h𝔞, h𝔟, hpos⟩ := p
  dsimp only at h𝔞 h𝔟 hpos ⊢
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have τ : Emb F := w.embedding_of_isReal (IsTotallyReal.isReal w)
  have hνb : ν * b ≠ 0 := fun h => by have := hpos τ; rw [h, map_zero] at this; exact lt_irrefl _ this
  have hb0 : b ≠ 0 := right_ne_zero_of_mul hνb
  have hle := absNorm_le_abs_norm 𝔟 h𝔟 hb0
  have hB0 : (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := 𝔟.ne_zero
  have hnpos : 0 < nrm 𝔟 := by
    unfold nrm
    have h1 := FractionalIdeal.absNorm_nonneg (𝔟 : FractionalIdeal (𝓞 F)⁰ F)
    have h2 : FractionalIdeal.absNorm (𝔟 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 :=
      fun h => hB0 (FractionalIdeal.absNorm_eq_zero_iff.1 h)
    exact_mod_cast lt_of_le_of_ne h1 (Ne.symm h2)
  have hle' : nrm 𝔟 ≤ |(Algebra.norm ℚ b : ℝ)| := by
    unfold nrm; rw [← Rat.cast_abs]; exact_mod_cast hle
  rw [le_div_iff₀ hnpos, map_mul, Rat.cast_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left hle' (abs_nonneg _)
end GlobalTheory.NormLe
