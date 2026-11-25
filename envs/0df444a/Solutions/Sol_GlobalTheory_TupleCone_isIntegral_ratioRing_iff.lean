-- Prove2me | solution 1 for GlobalTheory.TupleCone.isIntegral_ratioRing_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:16:45.260954+00:00
-- url     : https://prove2.me/submissions/3084a826-60bf-4c7a-a100-39809d3007c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin
import Theorems.Thm_GlobalTheory_TupleCone_mem_saturation_of_isIntegral
import Theorems.Thm_GlobalTheory_TupleCone_mem_piece
import Theorems.Thm_GlobalTheory_TupleCone_C_mul_X_mem_cone
import Theorems.Thm_GlobalTheory_TupleCone_mem_piece_one
import Theorems.Thm_GlobalTheory_TupleCone_isIntegral_div_of_mem_piece

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TupleCone
open Polynomial
variable (o : Type*) [CommRing o] {L : Type*} [Field L] [Algebra o L] {σ : Type*} (t : σ → L)
variable {o t}
namespace GlobalTheory.TupleCone
theorem _root_.solution {i : σ} (hi : t i ≠ 0) {f : L} :
    IsIntegral (ratioRing o t i) f ↔ ∃ n, f * t i ^ n ∈ piece o t n := by
  constructor
  · intro hf
    have hx : IsIntegral (cone o t) (C (t i) * X) :=
      isIntegral_algebraMap (x := (⟨_, C_mul_X_mem_cone i⟩ : cone o t))
    have h1 : ∀ s : ratioRing o t i, (C.comp (algebraMap (ratioRing o t i) L)) s ∈
        saturation _ hx := by
      rintro ⟨s, hs⟩
      induction hs using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨s, rfl⟩ := hx
        refine ⟨1, ?_⟩
        have := mem_piece_one (o := o) (t := t) s
        rw [mem_piece, pow_one] at this
        change IsIntegral _ (C (t s / t i) * _)
        rwa [pow_one, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ hi]
      | algebraMap r =>
        refine ⟨0, ?_⟩
        rw [pow_zero, mul_one]
        exact isIntegral_algebraMap (x := algebraMap o (cone o t) r)
      | add x y _ _ hx hy => simpa using add_mem hx hy
      | mul x y _ _ hx hy => simpa using mul_mem hx hy
    obtain ⟨n, hn⟩ := mem_saturation_of_isIntegral hx
      (hf.map_of_comp_eq (RingHom.codRestrict _ _ h1) C rfl)
    refine ⟨n, ?_⟩
    rwa [mem_piece, map_mul, map_pow, mul_assoc, ← mul_pow]
  · rintro ⟨n, hn⟩
    simpa [hi] using isIntegral_div_of_mem_piece i hn
end GlobalTheory.TupleCone
