-- Prove2me | solution 1 for IharaLemma.IdempotentSplitting.eq_smul_of_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/23be5bec-62af-5a6b-9fe7-975912780ef3

import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaLemma_IdempotentSplitting_eq_smul_of_smul_eq_zero

set_option autoImplicit false

namespace IharaLemmaSolCorner

open IharaLemma

theorem smul_eq_zero_of_notMem {B : Type} [CommRing B] (S : IdempotentSplitting B) {M : Type}
    [AddCommGroup M] [Module B M] {u : B} {y : M} (huy : u • y = 0) {j : Fin S.n} (hu : u ∉ S.𝔪 j) :
    S.e j • y = 0 := by
  obtain ⟨t, ht⟩ := exists_mul_mul_eq_of_notMem (S.coi.idem j) (S.𝔪 j)
    (fun J hJ hne => S.mem_of_isMaximal_of_ne j J hJ hne) hu
  rw [← ht, mul_right_comm, mul_smul, huy, smul_zero]

end IharaLemmaSolCorner

theorem solution {B : Type} [CommRing B]
    (S : IharaLemma.IdempotentSplitting B) {M : Type} [AddCommGroup M] [Module B M]
    {u : B} {y : M} (huy : u • y = 0) (i₀ : Fin S.n) (hu : ∀ j, j ≠ i₀ → u ∉ S.𝔪 j) :
    y = S.e i₀ • y := by
  have hsum : (∑ j, S.e j) • y = y := by rw [S.coi.complete, one_smul]
  conv_lhs => rw [← hsum, Finset.sum_smul]
  rw [Finset.sum_eq_single i₀ (fun j _ hj => IharaLemmaSolCorner.smul_eq_zero_of_notMem S huy (hu j hj))
    (fun h => absurd (Finset.mem_univ i₀) h)]

end S_IharaLemma_IdempotentSplitting_eq_smul_of_smul_eq_zero
end P2MW
export P2MW.S_IharaLemma_IdempotentSplitting_eq_smul_of_smul_eq_zero (solution)
