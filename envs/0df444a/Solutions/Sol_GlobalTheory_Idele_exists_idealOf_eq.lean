-- Prove2me | solution 1 for GlobalTheory.Idele.exists_idealOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:37:20.076292+00:00
-- url     : https://prove2.me/submissions/2e9b6dfd-ea08-45dd-b5f7-9e05af68659a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationAlgebraMapEqCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open scoped nonZeroDivisors IsDedekindDomain.FiniteAdeleRing
noncomputable section
open GlobalTheory GlobalTheory.Idele
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace GlobalTheory.Idele
theorem _root_.solution {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    ∃ t : 𝔸ᶠ[R, K]ˣ, idealOf t = I := by
  choose f hf using fun v : HeightOneSpectrum R =>
    valuedAdicCompletion_surjective K v (exp (-FractionalIdeal.count K v I))
  have h1 : ∀ᶠ v in Filter.cofinite, Valued.v (f v) = 1 := by
    filter_upwards [FractionalIdeal.finite_factors I] with v hv
    rw [hf, hv]; simp
  let a : 𝔸ᶠ[R, K] := ⟨f, h1.mono fun v hv => hv.le⟩
  have ha : IsUnit a := by
    refine FiniteAdeleRing.isUnit_iff.2 ⟨fun v h => ?_, h1⟩
    have := hf v
    change f v = 0 at h
    rw [h, map_zero] at this
    exact exp_ne_zero this.symm
  refine ⟨ha.unit, eq_of_count_eq (idealOf_ne_zero _) hI fun v => ?_⟩
  have := valued_idele ha.unit v
  rw [count_idealOf]
  change Valued.v (f v) = _ at this
  rw [hf, exp_inj] at this
  omega
end GlobalTheory.Idele
