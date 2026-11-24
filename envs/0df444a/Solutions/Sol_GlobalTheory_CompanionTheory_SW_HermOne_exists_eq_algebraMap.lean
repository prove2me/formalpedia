-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.HermOne.exists_eq_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:40:20.276873+00:00
-- url     : https://prove2.me/submissions/c671caed-3ee5-47eb-9d8e-a86b4a8a978b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianOneByOneIsScalar
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_HermOne_exists_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HermOne
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
namespace GlobalTheory.CompanionTheory.SW.HermOne
theorem _root_.solution (h : IsCMExt F E σ) {x : E} (hx : σ x = x) :
    ∃ β : F, x = algebraMap F E β := by
  by_contra hc
  push_neg at hc
  have hli : LinearIndependent F ![(1 : E), x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have ht : t = 0 := by
      by_contra ht
      have htE : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
      apply hc (-(s / t))
      rw [map_neg, map_div₀]
      field_simp
      linear_combination hst
    refine ⟨?_, ht⟩
    rw [ht, map_zero, zero_mul, add_zero] at hst
    exact (map_eq_zero_iff _ (algebraMap F E).injective).1 hst
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by
    rw [Fintype.card_fin, h.2.2.1]
  obtain ⟨y, hy⟩ := exists_ne h
  have hid : σ.toLinearMap = LinearMap.id := by
    refine (basisOfLinearIndependentOfCardEqFinrank hli hcard).ext fun i ↦ ?_
    fin_cases i <;> simp [hx]
  exact hy (by simpa using LinearMap.congr_fun hid y)
end GlobalTheory.CompanionTheory.SW.HermOne
