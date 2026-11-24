-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.QuadIso.exists_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:54:50.345+00:00
-- url     : https://prove2.me/submissions/22a415ea-9f88-43ce-a97b-cfdbed151876

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalHaarQuadraticSubstitutionInvariant
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_le_exp_neg_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_QuadIso_v_quad_lt
import Theorems.Thm_Formalism_FrobeniusOrbits_Group_key
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_key
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix WithZero
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.QuadIso
variable {K : Type} [Field K] [Valued K ℤᵐ⁰]
namespace GlobalTheory.CompanionTheory.SW.QuadIso
theorem _root_.solution {a c x : K} (ha : Valued.v a = 1) (hc : Valued.v c ≤ 1)
    (hx : Valued.v x < 1) (n : ℕ) :
    ∃ t : K, Valued.v t < 1 ∧
      Valued.v ((a * t + c * t ^ 2) - x) ≤ WithZero.exp (-(n + 1 : ℤ)) := by
  induction n with
  | zero =>
    refine ⟨0, by simp, ?_⟩
    simpa using le_exp_neg_one hx
  | succ n ih =>
    obtain ⟨t, ht, he⟩ := ih
    have ha0 : a ≠ 0 := by
      intro h
      rw [h, map_zero] at ha
      exact zero_ne_one ha
    set e := (a * t + c * t ^ 2) - x with he_def
    have hlt : Valued.v e < 1 := Valuation.map_sub_lt _ (v_quad_lt ha hc ht) hx
    have hae : Valued.v (a⁻¹ * e) = Valued.v e := by
      rw [map_mul, map_inv₀, ha]; simp
    have ht' : Valued.v (t - a⁻¹ * e) < 1 := Valuation.map_sub_lt _ ht (by rwa [hae])
    refine ⟨t - a⁻¹ * e, ht', ?_⟩
    have key : (a * (t - a⁻¹ * e) + c * (t - a⁻¹ * e) ^ 2) - x =
        -(a⁻¹ * e * c * (t + (t - a⁻¹ * e))) := by
      have h1 : a * (a⁻¹ * e) = e := by field_simp
      have h2 : x = (a * t + c * t ^ 2) - e := by rw [he_def]; ring
      rw [h2]
      linear_combination (-1 : K) * h1
    rw [key, Valuation.map_neg, map_mul, map_mul, hae]
    have hs : Valued.v (t + (t - a⁻¹ * e)) ≤ WithZero.exp (-1 : ℤ) :=
      le_exp_neg_one (Valuation.map_add_lt _ ht ht')
    calc Valued.v e * Valued.v c * Valued.v (t + (t - a⁻¹ * e))
        ≤ WithZero.exp (-(n + 1 : ℤ)) * 1 * WithZero.exp (-1 : ℤ) := by gcongr
      _ = WithZero.exp (-((n + 1 : ℕ) + 1 : ℤ)) := by
        rw [mul_one, ← WithZero.exp_add]
        congr 1
end GlobalTheory.CompanionTheory.SW.QuadIso
