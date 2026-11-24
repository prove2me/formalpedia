-- Prove2me | solution 1 for GlobalTheory.functional_eq_sum_coeff_of_vanish
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:58:16.995866+00:00
-- url     : https://prove2.me/submissions/33cc7dc9-20c0-4017-8713-7d0efc0bb18c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NablaValueCopiesBilinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_InvariantValueCopiesEqZeroOfLowCoeffStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NabValNEqSumCoeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {σ K : Type} [CommRing K] [Finite σ]
    (F : MvPowerSeries σ K → K) (N : ℕ)
    (hadd : ∀ f g, F (f + g) = F f + F g) (hsmul : ∀ (t : K) f, F (t • f) = t * F f)
    (hvan : ∀ f, (∀ μ : σ →₀ ℕ, μ.degree ≤ N → MvPowerSeries.coeff μ f = 0) → F f = 0) :
    ∃ S : Finset (σ →₀ ℕ), ∀ f, F f =
      ∑ μ ∈ S, MvPowerSeries.coeff μ f * F (MvPowerSeries.monomial μ (1 : K)) := by
  classical
  let L : MvPowerSeries σ K →ₗ[K] K :=
    { toFun := F, map_add' := hadd, map_smul' := fun t f => by simpa using hsmul t f }
  have hL : ∀ f, L f = F f := fun _ => rfl
  refine ⟨(Finsupp.finite_of_degree_le (σ := σ) N).toFinset, fun f => ?_⟩
  set S := (Finsupp.finite_of_degree_le (σ := σ) N).toFinset with hS
  have hg : F (f - ∑ μ ∈ S, MvPowerSeries.coeff μ f • MvPowerSeries.monomial μ (1 : K)) = 0 := by
    apply hvan
    intro ν hν
    have hνS : ν ∈ S := by simpa [hS] using hν
    rw [map_sub, map_sum, Finset.sum_eq_single_of_mem ν hνS]
    · simp
    · intro μ _ hne
      rw [map_smul, MvPowerSeries.coeff_monomial_ne (Ne.symm hne)]
      simp
  rw [← hL, map_sub, map_sum, sub_eq_zero] at hg
  rw [← hL, hg]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_smul, hL, smul_eq_mul]
end GlobalTheory
