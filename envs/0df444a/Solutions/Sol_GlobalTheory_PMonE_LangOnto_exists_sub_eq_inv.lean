-- Prove2me | solution 1 for GlobalTheory.PMonE.LangOnto.exists_sub_eq_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:35:09.264032+00:00
-- url     : https://prove2.me/submissions/ac460862-f800-46d9-989a-ab518c720ba0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_GroundTheory_PAdicHodge_SemilinearResidue
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralSolutionFrobeniusSubMulVecEq
import Theorems.Thm_GlobalTheory_PMonE_LangOnto_backPoly_zero
import Theorems.Thm_GlobalTheory_PMonE_LangOnto_backPoly_succ
import Theorems.Thm_GlobalTheory_PMonE_LangOnto_backPoly_natDegree
import Theorems.Thm_GroundTheory_PAdicHodge_SemilinearResidue_exists_rel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE GlobalTheory.PMonE.LangOnto
open Polynomial Finset GlobalTheory.PMonE
namespace GlobalTheory.PMonE.LangOnto
theorem _root_.solution {k : Type*} [Field k] [IsAlgClosed k] {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {q : ℕ} (hq : 2 ≤ q) (ψ : V →+ V)
    (hψ : ∀ (c : k) (x : V), ψ (c ^ q • x) = c • ψ x) (z : V) : ∃ y, y - ψ y = z := by
  obtain ⟨m, ⟨c, hrel⟩, -⟩ := GroundTheory.PAdicHodge.SemilinearResidue.exists_rel k (fun i => (⇑ψ)^[i] z)
  cases m with
  | zero => exact ⟨0, by simpa using hrel.symm⟩
  | succ n =>
    have hdeg : (backPoly q n c (n + 1) - C 1).degree ≠ 0 := by
      rw [degree_sub_C (natDegree_pos_iff_degree_pos.mp (backPoly_natDegree hq n c (n + 1)))]
      exact (natDegree_pos_iff_degree_pos.mp (backPoly_natDegree hq n c (n + 1))).ne'
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root _ hdeg
    set u : ℕ → k := fun i => (backPoly q n c (n - i)).eval t with hu
    have h0 : u 0 ^ q = 1 + c 0 * t := by
      have := ht.eq_zero
      simp only [backPoly_succ, eval_sub, eval_pow, eval_mul, eval_C, eval_X, Nat.sub_self] at this
      simp only [hu, Nat.sub_zero]
      linear_combination this
    have hn : u n = t := by simp [hu, backPoly_zero]
    have hs : ∀ i ∈ range n, u (i + 1) ^ q = u i + c (i + 1) * t := by
      intro i hi
      have hi' : i < n := mem_range.mp hi
      have e1 : n - i = (n - (i + 1)) + 1 := by omega
      have e2 : n - (n - (i + 1)) = i + 1 := by omega
      simp only [hu]
      rw [e1]
      simp only [backPoly_succ, eval_sub, eval_pow, eval_mul, eval_C, eval_X, e2]
      ring
    have hit : ∀ i, ψ ((⇑ψ)^[i] z) = (⇑ψ)^[i + 1] z := fun i =>
      (Function.iterate_succ_apply' _ _ _).symm
    refine ⟨∑ i ∈ range (n + 1), u i ^ q • (⇑ψ)^[i] z, ?_⟩
    rw [map_sum]
    simp_rw [hψ, hit]
    have hA : ∑ i ∈ range n, u (i + 1) ^ q • (⇑ψ)^[i + 1] z
        = ∑ i ∈ range n, (u i + c (i + 1) * t) • (⇑ψ)^[i + 1] z :=
      sum_congr rfl (fun i hi => by rw [hs i hi])
    rw [sum_range_succ (fun i => u i • (⇑ψ)^[i + 1] z), hn, hrel, smul_sum, sum_range_succ' _ n,
      sum_range_succ' (fun i => t • c i • (⇑ψ)^[i] z) n, hA, h0]
    simp only [Function.iterate_zero, id, smul_smul, add_smul, sum_add_distrib, one_smul, mul_comm t]
    abel
end GlobalTheory.PMonE.LangOnto
