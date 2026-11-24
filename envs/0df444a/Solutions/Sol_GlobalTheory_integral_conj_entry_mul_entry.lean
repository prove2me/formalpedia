-- Prove2me | solution 1 for GlobalTheory.integral_conj_entry_mul_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:19:09.781802+00:00
-- url     : https://prove2.me/submissions/5dc42cf2-e393-4e04-ac9a-fe7b8eab3084

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
import Theorems.Thm_GlobalTheory_integral_conj_inner_mul_inner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace ComplexConjugate
open GlobalTheory
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
  (ρ : Representation ℂ K V) (σ : Representation ℂ K W)
namespace GlobalTheory
theorem _root_.solution [ρ.IsIrreducible] (hρc : ∀ v, Continuous fun k => ρ k v)
    (hρu : ∀ k v, ‖ρ k v‖ = ‖v‖) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ V) (i j i' j' : ι) :
    ∫ k, conj ⟪b i, ρ k (b j)⟫_ℂ * ⟪b i', ρ k (b j')⟫_ℂ ∂μ =
      if i = i' ∧ j = j' then (Module.finrank ℂ V : ℂ)⁻¹ else 0 := by
  rw [integral_conj_inner_mul_inner μ ρ hρc hρu, orthonormal_iff_ite.mp b.orthonormal,
    orthonormal_iff_ite.mp b.orthonormal]
  by_cases h1 : i = i' <;> by_cases h2 : j = j' <;> simp [h1, h2, eq_comm]
end GlobalTheory
