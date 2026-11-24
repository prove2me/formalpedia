-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KrullLocal.exists_mul_eq_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:48:33.67445+00:00
-- url     : https://prove2.me/submissions/bb6bb61d-9c60-4bc8-a143-7023c9da7294

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorPrimeLocalizationCriterion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KrullLocal
namespace GlobalTheory.CompanionTheory.KrullLocal
theorem _root_.solution {B R C : Type} [CommRing B] [CommRing R] [CommRing C] [Algebra B R]
    [Algebra B C] (q : Ideal C) [hq : q.IsPrime]
    (h1 : ∀ c : C, ∃ b t : B, algebraMap B C t ∉ q ∧ ∃ v : C, v ∉ q ∧
      v * (algebraMap B C t * c) = v * algebraMap B C b)
    (w : R ⊗[B] C) :
    ∃ (s : B) (v : C) (r : R), algebraMap B C s ∉ q ∧ v ∉ q ∧
      ((1 : R) ⊗ₜ[B] (v * algebraMap B C s)) * w = r ⊗ₜ[B] v := by
  have hmul : ∀ {x y : C}, x ∉ q → y ∉ q → x * y ∉ q := fun hx hy hm =>
    (hq.mem_or_mem hm).elim hx hy
  have hone : (1 : C) ∉ q := fun h => hq.ne_top ((Ideal.eq_top_iff_one q).2 h)
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1, 1, 0, by simpa using hone, hone, by simp⟩
  | tmul r0 c =>
    obtain ⟨b, t, ht, v, hv, h⟩ := h1 c
    refine ⟨t, v, b • r0, ht, hv, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_assoc, h, TensorProduct.smul_tmul,
      Algebra.smul_def, mul_comm]
  | add x y hx hy =>
    obtain ⟨s, v, r, hs, hv, e⟩ := hx
    obtain ⟨s', v', r', hs', hv', e'⟩ := hy
    refine ⟨s * s', v * v', s' • r + s • r', by rw [map_mul]; exact hmul hs hs', hmul hv hv', ?_⟩
    have a1 : ((1 : R) ⊗ₜ[B] (v * v' * algebraMap B C (s * s'))) =
        ((1 : R) ⊗ₜ[B] (v' * algebraMap B C s')) * ((1 : R) ⊗ₜ[B] (v * algebraMap B C s)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]
      congr 1
      ring
    have a2 : ((1 : R) ⊗ₜ[B] (v * v' * algebraMap B C (s * s'))) =
        ((1 : R) ⊗ₜ[B] (v * algebraMap B C s)) * ((1 : R) ⊗ₜ[B] (v' * algebraMap B C s')) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul]
      congr 1
      ring
    rw [mul_add]
    nth_rewrite 1 [a1]
    rw [a2, mul_assoc, mul_assoc, e, e', Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, TensorProduct.add_tmul,
      TensorProduct.smul_tmul, TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def]
    congr 2 <;> ring
end GlobalTheory.CompanionTheory.KrullLocal
