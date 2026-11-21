-- Prove2me | solution 1 for MasulloGRH.nuclear_finite_rank_dense
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-21T00:39:10.899174+00:00
-- url     : https://prove2.me/submissions/921444d1-c2ab-4bae-bec7-34dccf6ec3ae

import Theorems.Thm_MasulloGRH_nuclear_finite_rank_approximation
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MasulloGRH Filter Topology Set
open scoped BigOperators

theorem solution (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    (hE : IsNuclear E) (hF : IsHLCS F) :
    Dense {T : E →L[ℂ] F | ∃ (N : ℕ) (φ : Fin N → StrongDual ℂ E) (y : Fin N → F),
      ∀ x, T x = ∑ i, φ i x • y i} := by
  classical
  obtain ⟨⟨ι, hι, p, hp⟩, hT⟩ := hF
  let : ContinuousSMul ℂ F := hp.continuousSMul
  intro T
  rw [mem_closure_iff_nhds_zero]
  intro U hU
  obtain ⟨⟨B, V⟩, ⟨hB, hV⟩, hsub⟩ :=
    (ContinuousLinearMap.hasBasis_nhds_zero (σ := RingHom.id ℂ) (E := E) (F := F)).mem_iff.mp hU
  obtain ⟨J, ε, hε, hJV⟩ := (hp.mem_nhds_iff 0 V).mp hV
  have hq : Continuous (J.sup p : Seminorm ℂ F) := Seminorm.continuous_finsetSup
    (fun i _ => hp.continuous_seminorm i)
  obtain ⟨N, φ, y, ha⟩ :=
    MasulloGRH.nuclear_finite_rank_approximation E F hE T B hB (J.sup p) hq ε hε
  let S : E →L[ℂ] F := ∑ i, (φ i).smulRight (y i)
  have hS (x : E) : S x = ∑ i, φ i x • y i := by simp [S]
  refine ⟨S, ⟨N, φ, y, hS⟩, hsub ?_⟩
  intro x hx
  apply hJV
  rw [Seminorm.mem_ball_zero]
  change (J.sup p) (S x - T x) < ε
  rw [show S x - T x = -(T x - S x) by abel, map_neg_eq_map, hS]
  exact ha x hx
