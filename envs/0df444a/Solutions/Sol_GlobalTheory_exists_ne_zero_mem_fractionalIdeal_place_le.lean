-- Prove2me | solution 1 for GlobalTheory.exists_ne_zero_mem_fractionalIdeal_place_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:44:52.440716+00:00
-- url     : https://prove2.me/submissions/a3ff731a-b734-4cce-b479-6506c66fd85a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped nonZeroDivisors NNReal ENNReal
variable (K : Type*) [Field K] [NumberField K]
open scoped Classical
namespace GlobalTheory
theorem _root_.solution (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (g : InfinitePlace K → ℝ≥0) (h : minkowskiBound K I ≤ volume (convexBodyLT K g)) :
    ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), a ≠ 0 ∧ ∀ w : InfinitePlace K, w a ≤ g w := by
  set S : Set (mixedSpace K) :=
    (Set.univ.pi (fun w : { w : InfinitePlace K // IsReal w } => Metric.closedBall 0 (g w))) ×ˢ
    (Set.univ.pi (fun w : { w : InfinitePlace K // IsComplex w } => Metric.closedBall 0 (g w)))
    with hS
  have hsub : convexBodyLT K g ⊆ S :=
    Set.prod_mono (Set.pi_mono fun _ _ => Metric.ball_subset_closedBall)
      (Set.pi_mono fun _ _ => Metric.ball_subset_closedBall)
  have hneg : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    simp only [hS, Set.mem_prod, Prod.fst_neg, Set.mem_pi, Set.mem_univ, Pi.neg_apply,
      mem_closedBall_zero_iff, norm_neg, forall_true_left, Prod.snd_neg] at hx ⊢
    exact hx
  have hconv : Convex ℝ S :=
    Convex.prod (convex_pi (fun _ _ => convex_closedBall _ _))
      (convex_pi (fun _ _ => convex_closedBall _ _))
  have hcomp : IsCompact S :=
    IsCompact.prod (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
      (isCompact_univ_pi fun _ => isCompact_closedBall _ _)
  have h_fund := ZSpan.isAddFundamentalDomain' (fractionalIdealLatticeBasis K I) volume
  have : Countable (Submodule.span ℤ
      (Set.range (fractionalIdealLatticeBasis K I))).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range (fractionalIdealLatticeBasis K I)))
    infer_instance
  obtain ⟨⟨x, hx⟩, h_nz, h_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      h_fund hneg hconv hcomp (h.trans (measure_mono hsub))
  rw [Submodule.mem_toAddSubgroup, mem_span_fractionalIdealLatticeBasis] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨a, ha, by simpa using h_nz, fun w => ?_⟩
  simp only [hS, Set.mem_prod, Set.mem_pi, Set.mem_univ, forall_true_left,
    mem_closedBall_zero_iff] at h_mem
  rw [← normAtPlace_apply]
  rcases isReal_or_isComplex w with hw | hw
  · rw [normAtPlace_apply_of_isReal hw]
    exact h_mem.1 ⟨w, hw⟩
  · rw [normAtPlace_apply_of_isComplex hw]
    exact h_mem.2 ⟨w, hw⟩
end GlobalTheory
