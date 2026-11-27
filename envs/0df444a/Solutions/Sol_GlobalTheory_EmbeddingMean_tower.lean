-- Prove2me | solution 1 for GlobalTheory.EmbeddingMean.tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:26:24.03479+00:00
-- url     : https://prove2.me/submissions/e4b2fd0d-1624-493d-b8a6-8c342421050e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendAndMean
import Theorems.Thm_GlobalTheory_EmbeddingMean_card_fibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EmbeddingMean
namespace GlobalTheory.EmbeddingMean
theorem _root_.solution {K A B C : Type} [Field K] [Field A] [Field B] [Field C] [CharZero K]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra A B] [IsScalarTower K A B]
    [FiniteDimensional K A] [FiniteDimensional K B] [IsAlgClosed C] :
    (∀ f : A →ₐ[K] C, ∃ g : B →ₐ[K] C, g.comp (IsScalarTower.toAlgHom K A B) = f) ∧
    ∀ F : (A →ₐ[K] C) → ℝ,
      (∑ g : B →ₐ[K] C, F (g.comp (IsScalarTower.toAlgHom K A B))) / (Module.finrank K B : ℝ)
        = (∑ f : A →ₐ[K] C, F f) / (Module.finrank K A : ℝ) := by
  classical
  haveI : FiniteDimensional A B := Module.Finite.of_restrictScalars_finite K A B
  have hpos : 0 < Module.finrank A B := Module.finrank_pos
  refine ⟨fun f => ?_, fun F => ?_⟩
  · have h := card_fibre (B := B) f
    obtain ⟨g, hg⟩ := Finset.card_pos.mp (h ▸ hpos)
    exact ⟨g, (Finset.mem_filter.mp hg).2⟩
  · have hsum : (∑ g : B →ₐ[K] C, F (g.comp (IsScalarTower.toAlgHom K A B)))
        = (Module.finrank A B : ℝ) * ∑ f : A →ₐ[K] C, F f := by
      rw [← Finset.sum_fiberwise Finset.univ
        (fun g : B →ₐ[K] C => g.comp (IsScalarTower.toAlgHom K A B)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Finset.sum_congr rfl (g := fun _ => F f)
        (fun g hg => by rw [(Finset.mem_filter.mp hg).2]),
        Finset.sum_const, nsmul_eq_mul]
      congr 2
      convert card_fibre (B := B) f
    have hA : (Module.finrank K A : ℝ) ≠ 0 := by
      exact_mod_cast (Module.finrank_pos (R := K) (M := A)).ne'
    have hB : (Module.finrank A B : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [hsum, ← Module.finrank_mul_finrank K A B]
    push_cast
    field_simp
end GlobalTheory.EmbeddingMean
