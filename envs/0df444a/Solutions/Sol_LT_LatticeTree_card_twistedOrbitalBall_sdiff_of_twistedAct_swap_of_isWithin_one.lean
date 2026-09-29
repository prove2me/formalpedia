-- Prove2me | solution 1 for LT.LatticeTree.card_twistedOrbitalBall_sdiff_of_twistedAct_swap_of_isWithin_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/591088c8-d7a0-5859-8fff-14b6a898d13f

import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_LT_LatticeTree_twistedFixedVertexSet_eq_empty_and_twistedOrbitalBall_eq_of_twistedAct_swap
import Theorems.Thm_LT_LatticeTree_finite_setOf_isWithin_or_isWithin_and_card_eq_of_isWithin_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_card_twistedOrbitalBall_sdiff_of_twistedAct_swap_of_isWithin_one

set_option autoImplicit false

private theorem latticeMap_scalarGL_unitOfNeZero_le {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) (L : Submodule R (Fin 2 → K)) :
    LT.LatticeTree.latticeMap (LT.LatticeTree.scalarGL (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero)) L ≤ L := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := LT.LatticeTree.mem_latticeMap_scalarGL.1 hv
  rw [LT.LatticeTree.unitOfNeZero_coe, algebraMap_smul]
  exact L.smul_mem ϖ hw

open LT.LatticeTree in
theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (σ : LT.LatticeTree.IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (x₀ x₁ : LT.LatticeTree.Vertex R K)
    (hadj : LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) 1 x₀ x₁)
    (hne : x₀ ≠ x₁) (h₀ : LT.LatticeTree.Vertex.twistedAct δ σ x₀ = x₁)
    (h₁ : LT.LatticeTree.Vertex.twistedAct δ σ x₁ = x₀) :
    LT.LatticeTree.twistedFixedVertexSet δ σ = ∅ ∧
    (∀ r : ℕ,
        LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 2) δ σ \
          LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) δ σ = ∅) ∧
    ∀ r : ℕ,
      (LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) δ σ \
          LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r) δ σ).Finite ∧
      Nat.card
        ↥(LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) δ σ \
            LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r) δ σ) =
        2 * Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by
  have hL5 := fun n =>
    LT.LatticeTree.twistedFixedVertexSet_eq_empty_and_twistedOrbitalBall_eq_of_twistedAct_swap
      R K ϖ hϖ σ δ x₀ x₁ hadj hne h₀ h₁ n
  have hL6 := fun n =>
    LT.LatticeTree.finite_setOf_isWithin_or_isWithin_and_card_eq_of_isWithin_one R K ϖ hϖ x₀ x₁ hadj hne n
  refine ⟨(hL5 0).1, fun r => ?_, fun r => ?_⟩
  · rw [(hL5 r).2.1, Set.diff_self]
  · rcases r with _ | s
    ·
      have h5 := (hL5 0).2.2
      simp only [Nat.mul_zero, Nat.zero_add] at h5 ⊢
      rw [twistedOrbitalBall_zero, (hL5 0).1, Set.diff_empty, h5]
      refine ⟨(hL6 0).1, ?_⟩
      rw [(hL6 0).2]
      simp
    ·
      have h2 : 2 * (s + 1) = 2 * s + 2 := by ring
      rw [h2, (hL5 s).2.1, (hL5 s).2.2]
      have h4 : 2 * s + 2 + 1 = 2 * (s + 1) + 1 := by ring
      rw [h4, (hL5 (s + 1)).2.2]
      have hsub : {x : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) s x₀ x ∨
            Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) s x₁ x} ⊆
          {x : Vertex R K | Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (s + 1) x₀ x ∨
            Vertex.IsWithin (unitOfNeZero (K := K) hϖ.ne_zero) (s + 1) x₁ x} := by
        rintro x (hx | hx)
        · exact Or.inl (hx.mono (latticeMap_scalarGL_unitOfNeZero_le hϖ) (Nat.le_succ s))
        · exact Or.inr (hx.mono (latticeMap_scalarGL_unitOfNeZero_le hϖ) (Nat.le_succ s))
      refine ⟨(hL6 (s + 1)).1.diff, ?_⟩
      rw [Nat.card_coe_set_eq, Set.ncard_diff hsub (hL6 s).1, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
        (hL6 (s + 1)).2, (hL6 s).2, Finset.sum_range_succ _ (s + 1)]
      omega

end S_LT_LatticeTree_card_twistedOrbitalBall_sdiff_of_twistedAct_swap_of_isWithin_one
end P2MW
export P2MW.S_LT_LatticeTree_card_twistedOrbitalBall_sdiff_of_twistedAct_swap_of_isWithin_one (solution)
