-- Prove2me | solution 1 for GlobalTheory.exists_smooth_compactSupport_hasSum_lattice_translates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:46:48.448889+00:00
-- url     : https://prove2.me/submissions/828bcbd3-30aa-4599-9ff3-c041af8130d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmoothPeriodicPartitionOfUnity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothCompactSupportHasSumLatticeTranslate
import Theorems.Thm_GlobalTheory_exists_radius_lattice_translate_norm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L], ∃ η : V → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ ∀ y, HasSum (fun l : L => η (y + l)) 1 := by
  intro V _ _ _ L _ _
  classical
  obtain ⟨R, hR, hcov⟩ := exists_radius_lattice_translate_norm_le V L
  let φ : ContDiffBump (0 : V) := ⟨R + 1, R + 2, by linarith, by linarith⟩
  have hrIn : φ.rIn = R + 1 := rfl
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L
  have hspan : Submodule.span ℤ (Set.range b) = L :=
    (Module.Free.chooseBasis ℤ L).ofZLatticeBasis_span ℝ
  have hfin : ∀ (x : V) (r : ℝ), {l : L | ‖x + (l : V)‖ < r}.Finite := by
    intro x r
    have hs := ZSpan.setFinite_inter b (Metric.isBounded_ball (x := -x) (r := r))
    rw [hspan] at hs
    refine (hs.preimage Subtype.val_injective.injOn).subset ?_
    intro l hl
    refine ⟨?_, l.2⟩
    show dist (l : V) (-x) < r
    rw [dist_eq_norm, sub_neg_eq_add, add_comm]
    exact hl
  let S : V → ℝ := fun y => ∑' l : L, φ (y + l)
  have hsupp : ∀ y, (Function.support fun l : L => φ (y + l)).Finite := by
    intro y
    refine (hfin y φ.rOut).subset fun l hl => ?_
    have h : y + (l : V) ∈ Metric.ball (0 : V) φ.rOut := by
      rw [← φ.support_eq]
      exact hl
    simpa [mem_ball_zero_iff] using h
  have hsum : ∀ y, HasSum (fun l : L => φ (y + l)) (S y) :=
    fun y => (summable_of_hasFiniteSupport (hsupp y)).hasSum
  have hper : ∀ y (l₀ : L), S (y + l₀) = S y := by
    intro y l₀
    calc S (y + l₀) = ∑' c : L, φ (y + ((l₀ + c : L) : V)) := by
          simp only [S, Submodule.coe_add, add_assoc]
      _ = S y := (Equiv.addLeft l₀).tsum_eq (fun l : L => φ (y + l))
  have hpos : ∀ y, 0 < S y := by
    intro y
    obtain ⟨l, hl⟩ := hcov y
    have h1 : φ (y + l) = 1 :=
      φ.one_of_mem_closedBall (by rw [mem_closedBall_zero_iff, hrIn]; linarith)
    have h2 := le_hasSum (hsum y) l (fun _ _ => φ.nonneg)
    linarith
  have hS : ContDiff ℝ ∞ S := by
    rw [contDiff_iff_contDiffAt]
    intro x
    let F := (hfin x (φ.rOut + 1)).toFinset
    have heq : S =ᶠ[nhds x] fun y => ∑ l ∈ F, φ (y + l) := by
      filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
      refine (hsum y).unique (hasSum_sum_of_ne_finset_zero ?_)
      intro l hl
      rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_lt] at hl
      apply φ.zero_of_le_dist
      rw [dist_zero_right]
      have h2 : ‖x + (l : V)‖ ≤ ‖y + (l : V)‖ + ‖x - y‖ := by
        calc ‖x + (l : V)‖ = ‖(y + (l : V)) + (x - y)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have h3 : ‖x - y‖ < 1 := by
        rw [← dist_eq_norm, dist_comm]
        exact hy
      linarith
    exact (ContDiff.contDiffAt (ContDiff.sum fun l _ =>
      φ.contDiff.comp (contDiff_id.add contDiff_const))).congr_of_eventuallyEq heq
  refine ⟨fun y => φ y / S y, φ.contDiff.div hS fun y => (hpos y).ne', ?_, ?_⟩
  · refine φ.hasCompactSupport.mono fun y hy => ?_
    simp only [Function.mem_support] at hy ⊢
    intro h
    apply hy
    simp [h]
  · intro y
    show HasSum (fun l : L => φ (y + l) / S (y + l)) 1
    simp_rw [hper y]
    rw [← div_self (hpos y).ne']
    exact (hsum y).div_const _
end GlobalTheory
