-- Prove2me | solution 1 for GlobalTheory.det_notMem_span_mulVec_of_socle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:02:32.590256+00:00
-- url     : https://prove2.me/submissions/8f5955f0-9c71-4a9c-a920-d371b3312ee6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetUpdateRowAlternatingMulVecMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MvPowerSeriesVariablesSyzygySocle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DetNotMemSpanMulVecOfSocle
import Theorems.Thm_GlobalTheory_det_sub_det_mem_span_of_mulVec_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {T : Type} [CommRing T] {g N : ℕ} (x : Fin g → T)
    (hsyz : ∀ r : Fin g → T, ∑ i, r i * x i = 0 → ∃ s : Matrix (Fin g) (Fin g) T,
      s.transpose = -s ∧ (∀ i, s i i = 0) ∧ r = s.mulVec x)
    (hsoc : ∏ i, x i ^ N ∉ Ideal.span (Set.range fun i => x i ^ (N + 1)))
    (a : Matrix (Fin g) (Fin g) T)
    (h : ∀ i, x i ^ (N + 1) ∈ Ideal.span (Set.range (a.mulVec x))) :
    a.det ∉ Ideal.span (Set.range (a.mulVec x)) := by
  intro hdet
  have h' : ∀ i, ∃ c : Fin g → T, ∑ j, c j * a.mulVec x j = x i ^ (N + 1) := fun i =>
    Ideal.mem_span_range_iff_exists_fun.mp (h i)
  choose b hb using h'
  let B : Matrix (Fin g) (Fin g) T := Matrix.of b
  have hB : B.mulVec (a.mulVec x) = fun i => x i ^ (N + 1) := by
    funext i
    exact hb i
  set J : Ideal T := Ideal.span (Set.range fun i => x i ^ (N + 1)) with hJ
  have hf : ∀ i, B.det * a.mulVec x i ∈ J := by
    intro i
    have e : B.adjugate.mulVec (B.mulVec (a.mulVec x)) = B.det • a.mulVec x := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have e' := congrFun e i
    rw [hB, Pi.smul_apply, smul_eq_mul] at e'
    rw [← e']
    exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨fun j => B.adjugate i j, rfl⟩
  have hBa : (B * a).det ∈ J := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hdet
    rw [Matrix.det_mul, ← hc, Finset.mul_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [mul_left_comm]
    exact Ideal.mul_mem_left _ _ (hf j)
  have hBx : (B * a).mulVec x = fun i => x i ^ (N + 1) := by
    rw [← Matrix.mulVec_mulVec, hB]
  have hD : (Matrix.diagonal fun i => x i ^ N).mulVec x = fun i => x i ^ (N + 1) := by
    funext i
    rw [Matrix.mulVec_diagonal, pow_succ]
  have key := GlobalTheory.det_sub_det_mem_span_of_mulVec_eq T g x hsyz (B * a)
    (Matrix.diagonal fun i => x i ^ N) (hBx.trans hD.symm)
  rw [hBx, Matrix.det_diagonal] at key
  have := J.sub_mem hBa key
  rw [sub_sub_cancel] at this
  exact hsoc this
end GlobalTheory
