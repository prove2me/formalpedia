-- Prove2me | solution 1 for IsLocalRing.exists_algHom_powerSeries_map_X_eq_of_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/621de020-ae08-542b-9086-3f826db03c13

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_algHom_powerSeries_map_X_eq_of_mem_maximalIdeal

set_option autoImplicit false

universe u

open IsLocalRing

open scoped PowerSeries.WithPiTopology

theorem solution
    {𝒪 R : Type u} [CommRing 𝒪] [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra 𝒪 R]
    (t : R) (ht : t ∈ maximalIdeal R) :
    ∃ ev : PowerSeries 𝒪 →ₐ[𝒪] R, ev PowerSeries.X = t ∧
      (∀ p : Polynomial 𝒪, ev (p : PowerSeries 𝒪) = Polynomial.aeval t p) ∧
      (∀ (n : ℕ) (F : PowerSeries 𝒪), PowerSeries.X ^ n ∣ F → ev F ∈ maximalIdeal R ^ n) := by
  classical
  letI wI : WithIdeal R := ⟨maximalIdeal R⟩
  letI uO : UniformSpace 𝒪 := ⊥
  haveI : DiscreteUniformity 𝒪 := ⟨rfl⟩
  haveI : ContinuousSMul 𝒪 R := DiscreteTopology.instContinuousSMul 𝒪 R
  have hI : IsAdic (maximalIdeal R) := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete (maximalIdeal R) R)
  have ha : PowerSeries.HasEval t := (PowerSeries.hasEval_def t).mpr (WithIdeal.isTopologicallyNilpotent_of_mem ht)
  refine ⟨PowerSeries.aeval ha, ?_, fun p => PowerSeries.aeval_coe ha p, ?_⟩
  · rw [← Polynomial.coe_X, PowerSeries.aeval_coe, Polynomial.aeval_X]
  · intro n F hF
    obtain ⟨G, rfl⟩ := hF
    rw [map_mul, map_pow, ← Polynomial.coe_X, PowerSeries.aeval_coe, Polynomial.aeval_X]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ht n)

end S_IsLocalRing_exists_algHom_powerSeries_map_X_eq_of_mem_maximalIdeal
end P2MW
export P2MW.S_IsLocalRing_exists_algHom_powerSeries_map_X_eq_of_mem_maximalIdeal (solution)
