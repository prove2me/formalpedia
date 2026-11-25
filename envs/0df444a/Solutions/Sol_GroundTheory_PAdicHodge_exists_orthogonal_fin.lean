-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_orthogonal_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:29:27.621198+00:00
-- url     : https://prove2.me/submissions/6d138973-9487-4489-ad11-58abe423f77c

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_OrthoBasis
import Theorems.Thm_GroundTheory_PAdicHodge_exists_sub_far_of_isClosed
import Theorems.Thm_GroundTheory_PAdicHodge_le_norm_smul_add_of_far

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
variable {k E : Type*} [NontriviallyNormedField k] [IsUltrametricDist k]
  [NormedAddCommGroup E] [NormedSpace k E] [IsUltrametricDist E]
variable [CompleteSpace k]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (n : ℕ) : ∀ (v : Fin n → E), LinearIndependent k v →
    ∀ {τ : ℝ}, 0 < τ → τ < 1 →
    ∃ w : Fin n → E, (∀ i, w i ≠ 0) ∧ (∀ i, w i ∈ Submodule.span k (Set.range v)) ∧
      ∀ (c : Fin n → k) (i : Fin n), τ * ‖c i • w i‖ ≤ ‖∑ j, c j • w j‖ := by
  induction n with
  | zero =>
    intro v _ τ _ _
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun _ i => i.elim0⟩
  | succ n ih =>
    intro v hv τ hτ0 hτ1
    set s := Real.sqrt τ with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 hτ0
    have hs1 : s < 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_lt_sqrt hτ0.le hτ1
    have hss : s * s = τ := Real.mul_self_sqrt hτ0.le
    obtain ⟨w', hw'0, hw'mem, hw'⟩ :=
      ih (fun i => v i.castSucc) (hv.comp _ (Fin.castSucc_injective n)) hs0 hs1
    set U := Submodule.span k (Set.range w') with hUdef
    have : FiniteDimensional k U := FiniteDimensional.span_of_finite k (Set.finite_range w')
    have hUc : IsClosed (U : Set E) := U.closed_of_finiteDimensional
    have hrange : (Set.range fun i : Fin n => v i.castSucc) = v '' Set.range Fin.castSucc :=
      Set.range_comp v Fin.castSucc
    have hUv : U ≤ Submodule.span k (Set.range fun i : Fin n => v i.castSucc) :=
      Submodule.span_le.2 (Set.range_subset_iff.2 hw'mem)
    have hvv : Submodule.span k (Set.range fun i : Fin n => v i.castSucc) ≤
        Submodule.span k (Set.range v) :=
      Submodule.span_mono (Set.range_comp_subset_range _ _)
    have hx : v (Fin.last n) ∉ U := by
      intro h
      have h' := hUv h
      rw [hrange] at h'
      exact hv.notMem_span_image (s := Set.range Fin.castSucc) (x := Fin.last n)
        (by rintro ⟨j, hj⟩; exact (Fin.castSucc_lt_last j).ne hj) h'
    obtain ⟨u, huU, hu⟩ := exists_sub_far_of_isClosed hUc hx hs0 hs1
    set x := v (Fin.last n) - u with hxdef
    have hx0 : x ≠ 0 := by
      intro h
      apply hx
      rw [sub_eq_zero] at h
      rw [h]; exact huU
    have hfar : ∀ u' ∈ U, s * ‖x‖ ≤ ‖x - u'‖ := hu
    refine ⟨(Fin.snoc w' x : Fin (n + 1) → E), ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last => simpa using hx0
      | cast i => simpa using hw'0 i
    · intro i
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        exact Submodule.sub_mem _ (Submodule.subset_span ⟨Fin.last n, rfl⟩) (hvv (hUv huU))
      | cast i =>
        simp only [Fin.snoc_castSucc]
        exact hvv (hw'mem i)
    · intro c i
      have hsum : ∑ j, c j • (Fin.snoc w' x : Fin (n + 1) → E) j =
          c (Fin.last n) • x + ∑ j : Fin n, c j.castSucc • w' j := by
        rw [Fin.sum_univ_castSucc, add_comm]
        simp
      have hu'U : ∑ j : Fin n, c j.castSucc • w' j ∈ U :=
        Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      obtain ⟨h1, h2⟩ := le_norm_smul_add_of_far hs0 hs1.le hfar (c (Fin.last n)) hu'U
      rw [hsum]
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last]
        have : τ * ‖c (Fin.last n) • x‖ ≤ s * ‖c (Fin.last n) • x‖ := by
          rw [← hss]
          exact mul_le_mul_of_nonneg_right (by nlinarith) (norm_nonneg _)
        linarith
      | cast i =>
        simp only [Fin.snoc_castSucc]
        have h3 := hw' (fun j => c j.castSucc) i
        rw [← hss, mul_assoc]
        nlinarith
end GroundTheory.PAdicHodge
