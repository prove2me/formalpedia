-- Prove2me | solution 2 for GlobalTheory.DeterminantSimpLemma.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:23:45.304728+00:00
-- url     : https://prove2.me/submissions/474af85c-30ff-4492-b168-044c6f0a44a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ImportsFurther

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DeterminantSimpLemma
open NumberField
namespace GlobalTheory.DeterminantSimpLemma
theorem _root_.solution {K : Type} [inst : Field K] [NumberField K] {n : ℕ}
    {M : Submodule (NumberField.RingOfIntegers K) (Fin n → K)} {x : Fin n → K} :
    x ∈ Submodule.span K (↑M : Set (Fin n → K)) →
      ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • x ∈ M := by
  intro hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ h₁
    · rw [mul_smul]; exact M.smul_mem _ h₂
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : (algebraMap (𝓞 K) K b) ≠ 0 := by
      simpa using hb0
    refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
    have key : (b * d) • (c • y) = a • (d • y) := by
      rw [← algebraMap_smul K (b * d), ← algebraMap_smul K a, ← algebraMap_smul K d,
        smul_smul, smul_smul]
      congr 1
      rw [← hab, map_mul]
      field_simp
    rw [key]
    exact M.smul_mem _ h
end GlobalTheory.DeterminantSimpLemma
