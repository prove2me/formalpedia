-- Prove2me | solution 1 for GlobalTheory.exists_testFunctions_subset_of_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:47:00.058624+00:00
-- url     : https://prove2.me/submissions/dc196572-ecc8-4016-a0aa-cba03d5c3d09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOpenPartialHomeomorphAnalytic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open AffinePoints
namespace GlobalTheory
theorem _root_.solution {A : Type*} [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] {e : A →ₐ[ℂ] ℂ} {U : Set (A →ₐ[ℂ] ℂ)} (hU : U ∈ 𝓝 e) :
    ∃ (n : ℕ) (f : Fin n → A) (ε : ℝ), 0 < ε ∧
      ∀ x : A →ₐ[ℂ] ℂ, (∀ k, ‖x (f k) - e (f k)‖ < ε) → x ∈ U := by
  obtain ⟨n, p, hp⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹Algebra.FiniteType ℂ A›
  rw [(isClosedEmbedding_coords (C := ℂ) p hp).isInducing.nhds_eq_comap, mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨n, fun k => p (MvPolynomial.X k), ε, hε, fun x hx => hVU (hb ?_)⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro k
  rw [dist_eq_norm]
  exact hx k
end GlobalTheory
