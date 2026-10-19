-- Prove2me | solution 1 for OAI.Problem356.exists_uniform_compact_separation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:16:45.504251+00:00
-- url     : https://prove2.me/submissions/80cdbe94-c6df-4c38-86e2-e7ec6af18588

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling

open OAI OAI.Problem356
universe uAlpha uIndex


theorem solution {α : Type uAlpha} {ι : Type uIndex} [MetricSpace α] [Finite ι]
    (K : ι → Set α) (hcompact : ∀ i, IsCompact (K i))
    (hdisjoint : Pairwise (fun i j => Disjoint (K i) (K j))) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, eta ≤ dist x y := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  have hpair : ∀ p : ι × ι, ∃ e : ℝ, 0 < e ∧ (p.1 ≠ p.2 → ∀ x ∈ K p.1, ∀ y ∈ K p.2, e ≤ dist x y) := by
    rintro ⟨i, j⟩
    by_cases hij : i = j
    · exact ⟨1, one_pos, fun h => absurd hij h⟩
    · obtain ⟨r, hr, hr'⟩ := Metric.exists_pos_forall_lt_edist (hcompact i) (hcompact j).isClosed (hdisjoint hij)
      refine ⟨r, by exact_mod_cast hr, fun _ x hx y hy => ?_⟩
      have := hr' x hx y hy
      rw [edist_dist] at this
      rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff'] at this
      have h2 := this.1
      exact h2.le
  choose e he hesep using hpair
  obtain ⟨p0, hp0⟩ := Finite.exists_min e
  refine ⟨e p0, he p0, fun i j hij x hx y hy => le_trans (hp0 (i, j)) (hesep (i, j) hij x hx y hy)⟩

