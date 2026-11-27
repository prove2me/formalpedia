-- Prove2me | solution 1 for MatchingPolytope.Multi.InHull.convex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:23:31.492138+00:00
-- url     : https://prove2.me/submissions/48c5623f-fd3d-4c91-9d06-21d6c2e3ee4b

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
variable [Fintype E]
namespace MatchingPolytope.Multi
namespace InHull
theorem _root_.solution {Q : Finset E → Prop} {x y : E → ℝ} (hx : InHull Q x) (hy : InHull Q y)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : InHull Q (a • x + b • y) := by
  obtain ⟨w, h0, h1, h2, h3⟩ := hx
  obtain ⟨u, g0, g1, g2, g3⟩ := hy
  refine ⟨fun M => a * w M + b * u M, fun M => by have := h0 M; have := g0 M; positivity,
    fun M hM => ?_, ?_, ?_⟩
  · by_cases hw : w M = 0
    · have : u M ≠ 0 := by intro hu; apply hM; simp [hw, hu]
      exact g1 M this
    · exact h1 M hw
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h2, g2]; simpa using hab
  · rw [← h3, ← g3, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro M _
    rw [add_smul, mul_smul, mul_smul]
end InHull
end MatchingPolytope.Multi
