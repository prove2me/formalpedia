-- Prove2me | solution 1 for LT.LatticeTree.even_of_mem_fixedVertexSet_and_even_of_mem_orbitalBall_sdiff_of_det_eq_mul_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/7c4a01cf-3399-5699-9e55-9ea68bc99072

import Definitions.Def_LatticeTreeBaseChange
import Theorems.Thm_LT_LatticeTree_even_of_mem_twistedFixedVertexSet_and_even_of_mem_twistedOrbitalBall_sdiff_of_det_eq_mul_zpow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LT_LatticeTree_even_of_mem_fixedVertexSet_and_even_of_mem_orbitalBall_sdiff_of_det_eq_mul_zpow
set_option autoImplicit false

theorem solution
    (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (ϖ : R) (hϖ : Irreducible ϖ)
    (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (k : ℤ) (u : Rˣ)
    (hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) K) = algebraMap R K u * algebraMap R K ϖ ^ k) :
    (∀ x : LT.LatticeTree.Vertex R K, x ∈ LT.LatticeTree.fixedVertexSet (R := R) g → Even k) ∧
    ∀ (n : ℕ) (x : LT.LatticeTree.Vertex R K),
      x ∈
        LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n + 1) g \
          LT.LatticeTree.orbitalBall (R := R) (LT.LatticeTree.unitOfNeZero (K := K) hϖ.ne_zero) (n) g →
      Even ((n : ℤ) + 1 - k) := by
  have h :=
    LT.LatticeTree.even_of_mem_twistedFixedVertexSet_and_even_of_mem_twistedOrbitalBall_sdiff_of_det_eq_mul_zpow
      R K ϖ hϖ (LT.LatticeTree.IntegralAut.refl R K) g k u hdet
  simp only [LT.LatticeTree.twistedFixedVertexSet_refl, LT.LatticeTree.twistedOrbitalBall_refl] at h
  exact h

end S_LT_LatticeTree_even_of_mem_fixedVertexSet_and_even_of_mem_orbitalBall_sdiff_of_det_eq_mul_zpow
end P2MW
export P2MW.S_LT_LatticeTree_even_of_mem_fixedVertexSet_and_even_of_mem_orbitalBall_sdiff_of_det_eq_mul_zpow (solution)
