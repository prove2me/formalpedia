-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdeleCharLocal.exists_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:22:52.70365+00:00
-- url     : https://prove2.me/submissions/1ef1efa1-a37d-4a98-9be3-06af87a91d10

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_HermitianCharacters_SelfDualLatticeFiltrationCharacter
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_algebraMap_eq_pairA
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_ker_mem_nhds
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_trace_mul_ne_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_exists_trace
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleCharLocal_exists_mem_only
import Theorems.Thm_GlobalTheory_AdLat_OpenLat_exists_nsmul_adele
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct RestrictedProduct nonZeroDivisors
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdeleCharLocal
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.AdeleCharLocal
theorem _root_.solution {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ y, psiV F ψ v y ≠ 1 := by
  classical
  by_contra h
  push Not at h
  obtain ⟨a, ha⟩ := exists_trace hψ
  have ha0 := trace_mul_ne_zero hψ ha
  obtain ⟨N, hN, hNU⟩ :=
    GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ (ker_mem_nhds hψ.1 hψ.2.1)
  obtain ⟨t, ht0, htv, htw⟩ := exists_mem_only v
  have key : ∀ y : F, (∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.valuation F y ≤ 1) →
      ∃ n : ℤ, Algebra.trace ℚ F (a * (N * y)) = n := fun y hy => by
    let β : Af F := algebraMap F (Af F) y - singleV F v (algebraMap F (Fv F v) y)
    have hβ : ∀ w, β w ∈ w.adicCompletionIntegers F := fun w => by
      have e : β w = algebraMap F (Fv F w) y -
        Pi.single (M := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v
          (algebraMap F (Fv F v) y) w := rfl
      rw [e]
      by_cases hw : w = v
      · subst hw
        rw [Pi.single_eq_same, sub_self]
        exact zero_mem _
      · rw [Pi.single_eq_of_ne hw, sub_zero, HeightOneSpectrum.mem_adicCompletionIntegers]
        exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w y).trans_le (hy w hw)
    have h1 : ψ (pairA F 0 (N • β)) = 1 := hNU _ hβ
    have h2 : ψ (N • pairA F 0 (singleV F v (algebraMap F (Fv F v) y))) = 1 := by
      rw [AddChar.map_nsmul_eq_pow]
      exact (congrArg (· ^ N) (h _)).trans (one_pow N)
    have h3 : pairA F 0 (algebraMap F (Af F) (N * y)) =
        pairA F 0 (N • β) + N • pairA F 0 (singleV F v (algebraMap F (Fv F v) y)) := by
      refine Prod.ext ?_ ?_
      · change (0 : Ainf F) = 0 + N • 0
        simp
      · change algebraMap F (Af F) (N * y) = N • β + N • singleV F v (algebraMap F (Fv F v) y)
        rw [← nsmul_add, sub_add_cancel, map_mul, map_natCast, nsmul_eq_mul]
    have h4 := hψ.2.2.1 (N * y)
    rw [algebraMap_eq_pairA, AddChar.map_add_eq_mul, h3, AddChar.map_add_eq_mul, h1, h2, mul_one, mul_one,
      ha, Complex.exp_eq_one_iff] at h4
    obtain ⟨n, hn⟩ := h4
    rw [mul_comm (n : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero] at hn
    exact ⟨n, by exact_mod_cast hn⟩
  let D := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)
  have h1 : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
    first
      | exact one_ne_zero
      | exact FractionalIdeal.one_ne_zero
      | simp
      | (rw [← FractionalIdeal.coeIdeal_top]; exact FractionalIdeal.coeIdeal_ne_zero.2 top_ne_bot)
      | (rw [← Ideal.one_eq_top, FractionalIdeal.coeIdeal_one]; simp)
  have hD : ∀ k : ℕ, a * N / (t : F) ^ k ∈ D := fun k => by
    rw [FractionalIdeal.mem_dual h1]
    intro x hx
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
    obtain ⟨n, hn⟩ := key (algebraMap (𝓞 F) F r / (t : F) ^ k) fun w hw => by
      have e : w.valuation F (t : F) = 1 :=
        le_antisymm (w.valuation_le_one t)
          (not_lt.1 fun hl => htw w hw ((w.valuation_lt_one_iff_mem t).1 hl))
      rw [map_div₀, map_pow, e, one_pow, div_one]
      exact w.valuation_le_one r
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply, eq_intCast, ← hn]
    congr 1
    ring
  obtain ⟨d, hd, hdD⟩ := D.isFractional
  have hd0 : algebraMap (𝓞 F) F d ≠ 0 := by simpa using nonZeroDivisors.ne_zero hd
  have hc : v.valuation F (algebraMap (𝓞 F) F d * (a * N)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (mul_ne_zero hd0 (mul_ne_zero ha0 (Nat.cast_ne_zero.2 hN.ne')))
  have htl : v.valuation F (t : F) < 1 := (v.valuation_lt_one_iff_mem t).2 htv
  obtain ⟨k, hk⟩ := exists_pow_lt₀ htl (Units.mk0 _ hc)
  obtain ⟨s, hs⟩ := hdD _ (hD k)
  have ht0' : (t : F) ≠ 0 := by simpa using ht0
  have e : algebraMap (𝓞 F) F d * (a * N) = algebraMap (𝓞 F) F s * (t : F) ^ k := by
    rw [hs, Algebra.smul_def]
    field_simp
  rw [Units.val_mk0, e, map_mul, map_pow] at hk
  exact absurd hk (not_lt.2 (mul_le_of_le_one_left' (v.valuation_le_one s)))
end GlobalTheory.CompanionTheory.AdeleCharLocal
