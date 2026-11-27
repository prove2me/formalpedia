-- Prove2me | solution 1 for MatchingPolytope.Multi.gw_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:24:35.48522+00:00
-- url     : https://prove2.me/submissions/b47ce162-71f3-4a4b-bd6e-8ec09453fef6

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
namespace MatchingPolytope.Multi
theorem _root_.solution [Fintype E] {C : Finset E} {x : E → ℝ} (hx : ∀ g ∈ C, x g ≠ 0) {w1 w2 : Finset E → ℝ}
    (h2 : ∀ g ∈ C, ∑ N, w2 N * chi N g = x g)
    (h1' : ∀ M, w1 M ≠ 0 → ∑ g ∈ C, chi M g = 1) (φ : Finset E → ℝ) :
    ∑ p, gw C x w1 w2 p * φ p.1 = ∑ M, w1 M * φ M := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro M _
  simp only [gw, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ g ∈ C, ∑ N, chi M g * chi N g * w1 M * w2 N / x g * φ M =
      chi M g * w1 M * φ M := by
    intro g hg
    have e1 : ∀ N, chi M g * chi N g * w1 M * w2 N / x g * φ M =
        (chi M g * w1 M * φ M / x g) * (w2 N * chi N g) := by
      intro N; field_simp
    simp_rw [e1]
    rw [← Finset.mul_sum, h2 g hg]
    field_simp [hx g hg]
  rw [Finset.sum_congr rfl this]
  by_cases hw : w1 M = 0
  · simp [hw]
  · rw [← Finset.sum_mul, ← Finset.sum_mul, h1' M hw]
    ring
end MatchingPolytope.Multi
