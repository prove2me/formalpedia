-- Prove2me | solution 1 for MeasureTheory.exists_contDiff_iteratedFDeriv_eq_iteratedFDerivWithin_halfSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/28380d35-f916-5063-8779-79e2658e407d

import Mathlib
import Theorems.Thm_MeasureTheory_exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero
import Theorems.Thm_MeasureTheory_exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_contDiff_iteratedFDeriv_eq_iteratedFDerivWithin_halfSpace

set_option autoImplicit false

theorem solution
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (Ψ : E × ℝ → F) (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ {p : E × ℝ | 0 ≤ p.2})
    (C : Set E) (hC : IsCompact C) (hsupp : ∀ p : E × ℝ, p.1 ∉ C → Ψ p = 0) :
    ∃ B : E × ℝ → F, ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ (n : ℕ) (e : E),
        iteratedFDeriv ℝ n B (e, 0) = iteratedFDerivWithin ℝ n Ψ {p : E × ℝ | 0 ≤ p.2} (e, 0) := by
  classical
  obtain ⟨a, ha, hasupp, hflatΨ⟩ :=
    MeasureTheory.exists_contDiff_forall_iteratedFDerivWithin_sub_sum_pow_smul_halfSpace_eq_zero Ψ hΨ C hC hsupp
  obtain ⟨B, hB, hflatB⟩ :=
    MeasureTheory.exists_contDiff_forall_iteratedFDeriv_sub_sum_pow_smul_eq_zero C hC a ha hasupp
  refine ⟨B, hB, fun n e => ?_⟩
  set H : Set (E × ℝ) := {p : E × ℝ | 0 ≤ p.2} with hH
  set P : E × ℝ → F := fun p => ∑ k ∈ Finset.range (n + 1), (p.2 ^ k / (k.factorial : ℝ)) • a k p.1 with hP
  have hPc : ContDiff ℝ (⊤ : ℕ∞) P := by
    refine ContDiff.sum fun k _ => ?_
    exact ((contDiff_snd.pow k).div_const _).smul ((ha k).comp contDiff_fst)
  have hHu : UniqueDiffOn ℝ H := by
    refine uniqueDiffOn_convex ?_ ?_
    · exact convex_halfSpace_ge (f := fun p : E × ℝ => p.2) ⟨fun x y => rfl, fun c x => rfl⟩ 0
    · refine ⟨((0 : E), (1 : ℝ)), ?_⟩
      rw [mem_interior_iff_mem_nhds]
      have ho : IsOpen {p : E × ℝ | 0 < p.2} := isOpen_lt continuous_const continuous_snd
      exact Filter.mem_of_superset (ho.mem_nhds (by simp)) (fun p hp => by
        simp only [hH, Set.mem_setOf_eq] at hp ⊢
        exact le_of_lt hp)
  have hmem : ((e, (0 : ℝ)) : E × ℝ) ∈ H := by simp [hH]

  have hBP : ContDiff ℝ (⊤ : ℕ∞) (fun p => B p - P p) := hB.sub hPc
  have h1 : iteratedFDeriv ℝ n B (e, 0) =
      iteratedFDeriv ℝ n (fun p => B p - P p) (e, 0) + iteratedFDeriv ℝ n P (e, 0) := by
    have : B = (fun p => B p - P p) + P := by funext p; simp
    conv_lhs => rw [this]
    exact iteratedFDeriv_add_apply (hBP.of_le (by exact_mod_cast le_top)).contDiffAt (hPc.of_le (by exact_mod_cast le_top)).contDiffAt

  have hΨP : ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun p => Ψ p - P p) H (e, 0) :=
    (hΨ (e, 0) hmem).sub hPc.contDiffWithinAt
  have h2 : iteratedFDerivWithin ℝ n Ψ H (e, 0) =
      iteratedFDerivWithin ℝ n (fun p => Ψ p - P p) H (e, 0) + iteratedFDerivWithin ℝ n P H (e, 0) := by
    have : Ψ = (fun p => Ψ p - P p) + P := by funext p; simp
    conv_lhs => rw [this]
    exact iteratedFDerivWithin_add_apply (hΨP.of_le (by exact_mod_cast le_top)) (hPc.contDiffWithinAt.of_le (by exact_mod_cast le_top)) hHu hmem
  have h3 : iteratedFDerivWithin ℝ n P H (e, 0) = iteratedFDeriv ℝ n P (e, 0) :=
    iteratedFDerivWithin_eq_iteratedFDeriv hHu (hPc.of_le (by exact_mod_cast le_top)).contDiffAt hmem
  rw [h1, h2, h3, hflatB n n le_rfl e, hflatΨ n n le_rfl e, zero_add]

end S_MeasureTheory_exists_contDiff_iteratedFDeriv_eq_iteratedFDerivWithin_halfSpace
end P2MW
export P2MW.S_MeasureTheory_exists_contDiff_iteratedFDeriv_eq_iteratedFDerivWithin_halfSpace (solution)
