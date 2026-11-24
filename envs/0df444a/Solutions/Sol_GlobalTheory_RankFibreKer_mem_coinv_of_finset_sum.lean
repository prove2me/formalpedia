-- Prove2me | solution 1 for GlobalTheory.RankFibreKer.mem_coinv_of_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:14:01.325854+00:00
-- url     : https://prove2.me/submissions/9ddb5165-3e54-418c-b8b4-4194615a840a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OmAOneApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoinvariantOfLocallyConstantTwist
import Theorems.Thm_GlobalTheory_RankFibreKer_omA_one_apply
import Theorems.Thm_GlobalTheory_RankFibreKer_tw_ne_zero
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul
import Theorems.Thm_GlobalTheory_SplitFlip_comp_mul_mem_SB


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
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ν β : kˣ →* ℂˣ) (a b : ℕ) (Φ χ : Matrix (Fin a) (Fin (a + b)) k → ℂ)
    (R : Finset (GL (Fin a) k)) (hΦ : Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k)) (hχ : IsLocallyConstant χ)
    (h1 : ∀ Y, Φ Y = ∑ r ∈ R, χ ((r⁻¹).val * Y) * Φ Y)
    (h2 : ∀ Y, χ Y * ∑ r ∈ R, tw ν (a + b) r * Φ (r.val * Y) = 0) : Φ ∈ coinv ν β a (a + b) := by
  set H : GL (Fin a) k → Matrix (Fin a) (Fin (a + b)) k → ℂ :=
    fun r Y => χ Y * (tw ν (a + b) r * Φ (r.val * Y)) with hH
  have hHSB : ∀ r, H r ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) := by
    intro r
    have hs : (fun Y => Φ (r.val * Y)) ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + b)) k) := by
      have := comp_mul_mem_SB r 1 hΦ
      simp only [Units.val_one, Matrix.mul_one] at this
      exact this
    obtain ⟨hs1, hs2⟩ := hs
    have e : H r = χ * ((fun _ => tw ν (a + b) r) * fun Y => Φ (r.val * Y)) := rfl
    rw [e]
    refine ⟨?_, ?_⟩
    · exact hχ.mul ((IsLocallyConstant.const _).mul hs1)
    · exact HasCompactSupport.mul_left (HasCompactSupport.mul_left hs2)
  have hom : ∀ r, omA ν β r 1 (H r) = fun Y => χ ((r⁻¹).val * Y) * Φ Y := by
    intro r
    funext Y
    rw [omA_one_apply]
    simp only [hH, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    field_simp [tw_ne_zero ν (a + b) r]
  have hsumH : ∑ r ∈ R, H r = 0 := by
    funext Y
    rw [Finset.sum_apply, Pi.zero_apply]
    simp only [hH, ← Finset.mul_sum]
    exact h2 Y
  have hΦeq : Φ = ∑ r ∈ R, (omA ν β r 1 (H r) - H r) := by
    rw [Finset.sum_sub_distrib, hsumH, sub_zero]
    funext Y
    rw [Finset.sum_apply]
    simp only [hom]
    exact h1 Y
  rw [hΦeq]
  refine Submodule.sum_mem _ fun r _ => Submodule.subset_span ⟨r, H r, hHSB r, rfl⟩
end GlobalTheory.RankFibreKer
