-- Prove2me | solution 1 for ModularCurve.coe_mem_valuationSubring_of_forall_aeval_mem_chartAlgFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/2485eb8f-1e66-58a6-bc8d-bb57d97cc6c7

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coe_mem_valuationSubring_of_forall_aeval_mem_chartAlgFin

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) [Fact (j ≠ 0)]
    (W₀ : ValuationSubring ↥K)
    (hAW₀ : ∀ a : A, algebraMap A ↥K a ∈ W₀)
    (hjW₀ : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 → Polynomial.aeval j P ∈ W₀) :
    ∀ s : ↥(chartAlgFin A (↥K) j), (s : ↥K) ∈ W₀ := by
  classical
  intro s

  let W₀' : Subalgebra A ↥K :=
    { W₀.toSubring with
      algebraMap_mem' := fun a => hAW₀ a }
  have hjmem : j ∈ W₀' := by
    have h := hjW₀ Polynomial.X (by rw [Polynomial.map_X]; exact Polynomial.X_ne_zero)
    rwa [Polynomial.aeval_X] at h
  have hle : Algebra.adjoin A ({j} : Set ↥K) ≤ W₀' := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hjmem)
  have hle' : (Algebra.adjoin A ({j} : Set ↥K)).toSubring ≤ W₀.toSubring := fun x hx => hle hx

  have hs : IsIntegral ↥(Algebra.adjoin A ({j} : Set ↥K)) (s : ↥K) := (mem_chartAlg_iff A (↥K)).mp s.2
  have hs' : IsIntegral ↥W₀ (s : ↥K) :=
    hs.map_of_comp_eq (Subring.inclusion hle') (RingHom.id ↥K) (by ext x; rfl)

  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥W₀) (K := ↥K)).mp hs'
  rw [← hy]
  exact y.2

end S_ModularCurve_coe_mem_valuationSubring_of_forall_aeval_mem_chartAlgFin
end P2MW
export P2MW.S_ModularCurve_coe_mem_valuationSubring_of_forall_aeval_mem_chartAlgFin (solution)
