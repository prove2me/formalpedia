-- Prove2me | solution 1 for NearlyOptimalPPR.Computation.recursive_level_work
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:16:29.15179+00:00
-- url     : https://prove2.me/submissions/8a109291-c233-4fa6-9b08-14a7c06d0b86

import Definitions.Def_NearlyOptimalPPR_Computation_work_analysis
import Definitions.Def_NearlyOptimalPPR_Computation_push
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_residual_identities
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_control_parameters
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_queue_domains
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_numerical_invariants
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_finite_prefix_counts
import Theorems.Thm_NearlyOptimalPPR_Computation_recursive_work_recurrences

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation
noncomputable section
variable {n : ℕ}
lemma region_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    RegionInvariant (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_residual_identities m n g s α q ℓ schedule t).1

theorem root_identity_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    RootIdentity g s α (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_residual_identities m n g s α q ℓ schedule t).2.1

lemma layer_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    LayerIdentity g (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_residual_identities m n g s α q ℓ schedule t).2.2.1

lemma root_threshold_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ((recursiveRun m g s α q ℓ schedule t).frames 0).q = q := by
  exact (recursive_residual_identities m n g s α q ℓ schedule t).2.2.2

lemma depth_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    (recursiveRun m g s α q ℓ schedule t).top ≤ ℓ := by
  exact (recursive_control_parameters m n g s α q ℓ schedule t).1

lemma budget_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    BudgetInvariant (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_control_parameters m n g s α q ℓ schedule t).2.1

lemma cache_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    CacheControlInvariant ℓ (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_control_parameters m n g s α q ℓ schedule t).2.2.1

lemma parameters_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 < q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    ParameterInvariant (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_control_parameters m n g s α q ℓ schedule t).2.2.2 hq

lemma keys_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    KeysInvariant g (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_queue_domains m n g s α q ℓ schedule t).1 hq

lemma isolate_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    IsolateResidual g (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_queue_domains m n g s α q ℓ schedule t).2.1 hs

lemma stored_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hq : 0 ≤ q) (hs : 0 < g.graph.degree s) (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    StoredInvariant g (recursiveRun m g s α q ℓ schedule t) := by
  exact (recursive_queue_domains m n g s α q ℓ schedule t).2.2 hq hs

lemma numerical_run (m : SolveModel) (g : InputGraph n) (s : Fin n) (α q : ℝ)
    (hα : 0 < α ∧ α < 1) (hq : 0 < q) (hs : 0 < g.graph.degree s)
    (ℓ : ℕ) (schedule : BlockSchedule) (t : ℕ) :
    NumericalInvariant g (recursiveRun m g s α q ℓ schedule t) := by
  exact recursive_numerical_invariants m n g s α q hα hq hs ℓ schedule t

end
end NearlyOptimalPPR.Computation


-- Proof module: Solutions.OverheadMonotone

set_option autoImplicit false
namespace NearlyOptimalPPR.Computation

lemma overhead_base_one (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ : ℕ) :
    1 ≤ 2+Real.log (2/ε)+(ℓ : ℝ) := by
  have hL := Real.log_nonneg ((le_div_iff₀ hε.1).mpr (by linarith [hε.2]) : 1 ≤ 2/ε)
  have hl : (0 : ℝ) ≤ (ℓ : ℝ) := by positivity
  linarith

lemma overhead_mono (ε : ℝ) (hε : 0 < ε ∧ ε ≤ 1) (ℓ a b : ℕ) (C D : ℝ)
    (hC : 0 ≤ C) (hCD : C ≤ D) (hab : a ≤ b) : overhead C a ε ℓ ≤ overhead D b ε ℓ := by
  have hX := overhead_base_one ε hε ℓ
  unfold overhead
  calc
    _ ≤ C*(2+Real.log (2/ε)+(ℓ : ℝ))^b := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX hab) hC
    _ ≤ _ := mul_le_mul_of_nonneg_right hCD (by positivity)

end NearlyOptimalPPR.Computation

set_option autoImplicit false
open Finset Matrix NearlyOptimalPPR.Computation
open scoped ENNReal
noncomputable section

theorem solution (m : SolveModel) :
    ∃ (C : ℝ) (c : ℕ), 0 < C ∧ 0 < c ∧
      ∀ (ε : ℝ) (ℓ : ℕ) (schedule : BlockSchedule), 0 < ε → ε ≤ 1 →
        let P := overhead C c ε ℓ
        (∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α : ℝ),
          0 < α → α ≤ 1 / 2 → 0 < g.graph.degree s →
          ∀ (t id : ℕ) (info : CallInformation),
            let run := recursiveRun m g s α (rootThreshold ε ℓ) ℓ schedule
            (run t).information id = some info →
              ((run t).episodes id : ℝ) ≤ P * info.scale / info.block ∧
              ((run t).fullSolves id : ℝ) ≤ P * info.scale / info.block ∧
              (∀ k ∈ (run t).episodeChildCounts id, k ≤ 1) ∧
              (∀ i ≤ (run t).top, ((run t).frames i).id = id →
                ((run t).frames i).childrenThisEpisode ≤ 1) ∧
              ∃ t' ≥ t, id ∈ (run t').closed) ∧
        (∀ (j : ℕ) (N : ℝ), j < ℓ → 1 ≤ N →
          let b := blockScale schedule ℓ j N
          workEnvelope m ε ℓ schedule j N ≤
            ENNReal.ofReal P *
              (ENNReal.ofReal (N ^ 2 / b) +
                ENNReal.ofReal (N / b) * workEnvelope m ε ℓ schedule (j + 1) b) +
              ENNReal.ofReal (P * N)) ∧
        (∀ N : ℝ, 1 ≤ N →
          let b := blockScale schedule ℓ ℓ N
          workEnvelope m ε ℓ schedule ℓ N ≤ ENNReal.ofReal (P * (N ^ 2 / b + N * b)))  := by
  obtain ⟨Cr,cr,hCr,hcr,hRec⟩ := recursive_work_recurrences m
  obtain ⟨Ck,hCk,hCount⟩ := recursive_finite_prefix_counts
  let C := Cr+Ck
  let c := max cr 4
  refine ⟨C,c,by dsimp only [C]; positivity,lt_of_lt_of_le hcr (le_max_left _ _),?_⟩
  intro ε ℓ schedule he he1 P
  have hmonoR := overhead_mono ε ⟨he,he1⟩ ℓ cr c Cr C hCr.le (by dsimp only [C]; linarith) (le_max_left _ _)
  have hmonoK := overhead_mono ε ⟨he,he1⟩ ℓ 4 c Ck C hCk.le (by dsimp only [C]; linarith) (le_max_right _ _)
  obtain ⟨hrNonleaf,hrLeaf⟩ := hRec ε ℓ schedule he he1
  refine ⟨?_,?_,?_⟩
  · intro n g s α ha ha1 hs t id info run hi
    obtain ⟨hepisodes,hfull,hchildren,hcurrent,hcloses⟩ := hCount m ε ℓ schedule he he1 n g s α ha ha1 hs t id info hi
    have hBase : 0 < 2+Real.log (2/ε)+(ℓ : ℝ) := by linarith [overhead_base_one ε ⟨he,he1⟩ ℓ]
    have hPrice : 0 < overhead Ck 4 ε ℓ := by unfold overhead; positivity
    have hRatio : 0 ≤ info.scale/(info.block : ℝ) := by
      have hE : 0 ≤ ((run t).episodes id : ℝ) := Nat.cast_nonneg _
      have hMul : 0 ≤ overhead Ck 4 ε ℓ*(info.scale/info.block) := by
        rw [show overhead Ck 4 ε ℓ*(info.scale/info.block)=overhead Ck 4 ε ℓ*info.scale/info.block by ring]
        linarith
      nlinarith
    refine ⟨?_,?_,hchildren,hcurrent,hcloses⟩
    · apply hepisodes.trans
      have hh := mul_le_mul_of_nonneg_right hmonoK hRatio
      simpa only [div_eq_mul_inv,mul_assoc] using hh
    · apply hfull.trans
      have hh := mul_le_mul_of_nonneg_right hmonoK hRatio
      simpa only [div_eq_mul_inv,mul_assoc] using hh
  · intro j N hj hN b
    apply (hrNonleaf j N hj hN).trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hmonoR) (by positivity)
    · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hmonoR (by linarith))
  · intro N hN b
    apply (hrLeaf N hN).trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right hmonoR
    exact add_nonneg (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
      (mul_nonneg (by linarith) (Nat.cast_nonneg _))
