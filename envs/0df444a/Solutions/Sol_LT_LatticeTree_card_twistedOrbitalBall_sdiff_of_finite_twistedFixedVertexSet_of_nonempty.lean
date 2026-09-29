-- Prove2me | solution 1 for LT.LatticeTree.card_twistedOrbitalBall_sdiff_of_finite_twistedFixedVertexSet_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/19b8c101-80f8-5060-a46a-c45de328008b

import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_LT_LatticeTree_twistedOrbitalBall_odd_eq_and_even_eq_setOf_exists_isWithin_of_nonempty
import Theorems.Thm_LT_LatticeTree_finite_sdiff_setOf_exists_isWithin_and_card_eq_of_finite_twistedFixedVertexSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_card_twistedOrbitalBall_sdiff_of_finite_twistedFixedVertexSet_of_nonempty

set_option autoImplicit false

theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (σ : LT.LatticeTree.IntegralAut R K) (δ : Matrix.GeneralLinearGroup (Fin 2) K)
    (hfin : (LT.LatticeTree.twistedFixedVertexSet δ σ).Finite)
    (hne : (LT.LatticeTree.twistedFixedVertexSet δ σ).Nonempty) :
    (∀ r : ℕ,
        LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) δ σ \
          LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r) δ σ = ∅) ∧
    ∀ r : ℕ,
      (LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 2) δ σ \
          LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) δ σ).Finite ∧
      Nat.card
        ↥(LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 2) δ σ \
            LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) δ σ) =
        (LT.LatticeTree.twistedUnitOrbitalCount δ σ * (Nat.card (R ⧸ Ideal.span {ϖ}) - 1) + 2) *
          Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by
  have hodd : ∀ m : ℕ,
      LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * m + 1) δ σ =
        LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * m) δ σ :=
    fun m =>
      (LT.LatticeTree.twistedOrbitalBall_odd_eq_and_even_eq_setOf_exists_isWithin_of_nonempty
        R K ϖ hϖ σ δ hne m).1
  have heven : ∀ m : ℕ,
      LT.LatticeTree.twistedOrbitalBall (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * m) δ σ =
        {x : LT.LatticeTree.Vertex R K | ∃ f ∈ LT.LatticeTree.twistedFixedVertexSet δ σ,
          LT.LatticeTree.Vertex.IsWithin (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) m f x} :=
    fun m =>
      (LT.LatticeTree.twistedOrbitalBall_odd_eq_and_even_eq_setOf_exists_isWithin_of_nonempty
        R K ϖ hϖ σ δ hne m).2
  refine ⟨fun r => ?_, fun r => ?_⟩
  · rw [hodd r, Set.diff_self]
  · have h2 : 2 * r + 2 = 2 * (r + 1) := by ring
    rw [hodd r, h2, heven (r + 1), heven r]
    unfold LT.LatticeTree.twistedUnitOrbitalCount
    exact
      LT.LatticeTree.finite_sdiff_setOf_exists_isWithin_and_card_eq_of_finite_twistedFixedVertexSet
        R K ϖ hϖ σ δ hfin hne r

end S_LT_LatticeTree_card_twistedOrbitalBall_sdiff_of_finite_twistedFixedVertexSet_of_nonempty
end P2MW
export P2MW.S_LT_LatticeTree_card_twistedOrbitalBall_sdiff_of_finite_twistedFixedVertexSet_of_nonempty (solution)
