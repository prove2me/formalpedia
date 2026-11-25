-- Prove2me | solution 1 for GlobalTheory.IdeleCharLevel.exists_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:57:23.34795+00:00
-- url     : https://prove2.me/submissions/f1288a8c-318e-4757-851a-1568c1264b95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdeleCongruenceUnitCriterion
import Theorems.Thm_GlobalTheory_AdLat_OpenLat_exists_nsmul_adele


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors Topology
open GlobalTheory GlobalTheory.IdeleCharLevel
variable (K : Type) [Field K] [NumberField K]
namespace GlobalTheory.IdeleCharLevel
theorem _root_.solution (U : Set (FiniteAdeleRing (𝓞 K) K)) (hU : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 K) K)) :
    ∃ M : ℕ, M ≠ 0 ∧ ∀ a : FiniteAdeleRing (𝓞 K) K,
      (∀ P : HeightOneSpectrum (𝓞 K), Valued.v (a P) ≤ P.intValuation (M : 𝓞 K)) → a ∈ U := by
  obtain ⟨M, hM, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele K U hU
  refine ⟨M, hM.ne', fun a ha => ?_⟩
  have hM0 : (M : K) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hM1 : (M : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have := h (algebraMap K (FiniteAdeleRing (𝓞 K) K) (M : K)⁻¹ * a) fun P => by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    change Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) (M : K)⁻¹) P * a P) ≤ 1
    rw [map_mul, FiniteAdeleRing.algebraMap_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀,
      ← map_natCast (algebraMap (𝓞 K) K), HeightOneSpectrum.valuation_of_algebraMap]
    have h0 : P.intValuation (M : 𝓞 K) ≠ 0 := P.intValuation_ne_zero _ hM1
    rw [inv_mul_le_iff₀ (zero_lt_iff.mpr h0), mul_one]
    exact ha P
  rwa [nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap K (FiniteAdeleRing (𝓞 K) K)) M,
    ← map_mul, mul_inv_cancel₀ hM0, map_one, one_mul] at this
end GlobalTheory.IdeleCharLevel
