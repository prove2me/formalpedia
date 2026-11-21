-- Prove2me | solution 1 for MasulloGRH.strictLF_quotient_weakQ_of_localized_closures
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T00:14:12.946091+00:00
-- url     : https://prove2.me/submissions/4e840d92-1360-4cd0-baa2-bb895fd87626

import Theorems.Thm_LocallyConvex_strictLF_localized_nullSequence_bounded

set_option autoImplicit false
open MasulloGRH Filter Topology

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hloc : ∀ n : ℕ, ∃ U ∈ nhds (0 : X n), ∃ j : ℕ,
      closure ((fun x : X n => V.mkQ (x : E)) '' U) ⊆
        Set.range (Submodule.mapQ (V.comap (X j).subtype) V (X j).subtype le_rfl)) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ U' ∈ nhds (0 : X k), ∃ r : ℝ, 0 < r ∧
        ∀ x ∈ U, ∀ y ∈ U', ((x : E) - (y : E)) ∈ V →
          ∃ w ∈ W, ((x : E) - (r : ℂ) • (w : E)) ∈ V := by
  classical
  intro n
  obtain ⟨m, hnm, U, hU, hseq⟩ :=
    LocallyConvex.strictLF_localized_nullSequence_bounded
      E X hmono hexh hX htop V hV hloc n
  refine ⟨m, hnm, U, hU, ?_⟩
  intro k hmk W hW
  letI : TopologicalSpace.MetrizableSpace (X k) := (hX k).2.2
  obtain ⟨A, hA⟩ := (nhds (0 : X k)).exists_antitone_basis
  by_contra hfail
  push_neg at hfail
  have hex (i : ℕ) := hfail (A i) (hA.mem i) ((i : ℝ) + 1) (by positivity)
  choose x hx y hy hxy hbad using hex
  have hyt : Tendsto y atTop (nhds (0 : X k)) := by
    apply tendsto_def.mpr
    intro S hS
    obtain ⟨i, hi⟩ := hA.mem_iff.mp hS
    filter_upwards [eventually_ge_atTop i] with j hj
    exact hi (hA.antitone hj (hy j))
  obtain ⟨R, hR, hbound⟩ := hseq k hmk y hyt (fun i => ⟨x i, hx i, hxy i⟩) W hW
  obtain ⟨i, hi⟩ := exists_nat_gt R
  obtain ⟨w, hw, hyw⟩ := hbound ((i : ℝ) + 1) (by linarith) i
  apply hbad i w hw
  convert V.add_mem (hxy i) hyw using 1 <;> abel
