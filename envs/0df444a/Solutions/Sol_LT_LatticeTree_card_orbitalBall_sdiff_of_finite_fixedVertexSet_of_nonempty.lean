-- Prove2me | solution 1 for LT.LatticeTree.card_orbitalBall_sdiff_of_finite_fixedVertexSet_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/509cddf3-8aca-5209-b280-661e6332b671

import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_LT_LatticeTree_card_twistedOrbitalBall_sdiff_of_finite_twistedFixedVertexSet_of_nonempty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_card_orbitalBall_sdiff_of_finite_fixedVertexSet_of_nonempty
set_option autoImplicit false

theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hfin : (LT.LatticeTree.fixedVertexSet (R := R) g).Finite)
    (hne : (LT.LatticeTree.fixedVertexSet (R := R) g).Nonempty) :
    (∀ r : ℕ,
        LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) g \
          LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r) g = ∅) ∧
    ∀ r : ℕ,
      (LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 2) g \
          LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) g).Finite ∧
      Nat.card
        ↥(LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 2) g \
            LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (2 * r + 1) g) =
        (LT.LatticeTree.unitOrbitalCount R g * (Nat.card (R ⧸ Ideal.span {ϖ}) - 1) + 2) *
          Nat.card (R ⧸ Ideal.span {ϖ}) ^ r := by
  have h := LT.LatticeTree.card_twistedOrbitalBall_sdiff_of_finite_twistedFixedVertexSet_of_nonempty R K ϖ hϖ
    (LT.LatticeTree.IntegralAut.refl R K) g
    (by rw [LT.LatticeTree.twistedFixedVertexSet_refl]; exact hfin)
    (by rw [LT.LatticeTree.twistedFixedVertexSet_refl]; exact hne)
  simp only [LT.LatticeTree.twistedOrbitalBall_refl, LT.LatticeTree.twistedUnitOrbitalCount_refl] at h
  exact h

end S_LT_LatticeTree_card_orbitalBall_sdiff_of_finite_fixedVertexSet_of_nonempty
end P2MW
export P2MW.S_LT_LatticeTree_card_orbitalBall_sdiff_of_finite_fixedVertexSet_of_nonempty (solution)
