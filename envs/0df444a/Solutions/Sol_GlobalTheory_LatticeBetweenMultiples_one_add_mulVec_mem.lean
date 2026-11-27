-- Prove2me | solution 1 for GlobalTheory.LatticeBetweenMultiples.one_add_mulVec_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:38:40.160745+00:00
-- url     : https://prove2.me/submissions/7442334b-ea78-4ddd-986f-15da4ae0b652

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqMultipleOfStandardLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField Matrix
open GlobalTheory GlobalTheory.LatticeBetweenMultiples
namespace GlobalTheory.LatticeBetweenMultiples
theorem _root_.solution {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {n : ℕ}
    (S : AddSubgroup (Fin n → v.adicCompletion F))
    (hGL : ∀ x : GL (Fin n) (v.adicCompletion F), (∀ i j, x.1 i j ∈ v.adicCompletionIntegers F) →
      (∀ i j, (x⁻¹).1 i j ∈ v.adicCompletionIntegers F) → ∀ w ∈ S, x.1.mulVec w ∈ S)
    (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) (hN : N * N = 0)
    (hNi : ∀ i j, N i j ∈ v.adicCompletionIntegers F) {w : Fin n → v.adicCompletion F}
    (hw : w ∈ S) : (1 + N).mulVec w ∈ S := by
  have h1 : (1 + N) * (1 - N) = 1 := by
    rw [add_mul, one_mul, mul_sub, mul_one, hN, sub_zero, sub_add_cancel]
  have h2 : (1 - N) * (1 + N) = 1 := by
    rw [sub_mul, one_mul, mul_add, mul_one, hN, add_zero, add_sub_cancel_right]
  have h1m : ∀ i j, (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈
      v.adicCompletionIntegers F := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hp : ∀ i j, (1 + N) i j ∈ v.adicCompletionIntegers F := by
    intro i j; rw [Matrix.add_apply]; exact add_mem (h1m i j) (hNi i j)
  have hm : ∀ i j, (1 - N) i j ∈ v.adicCompletionIntegers F := by
    intro i j; rw [Matrix.sub_apply]; exact sub_mem (h1m i j) (hNi i j)
  exact hGL ⟨1 + N, 1 - N, h1, h2⟩ hp hm w hw
end GlobalTheory.LatticeBetweenMultiples
