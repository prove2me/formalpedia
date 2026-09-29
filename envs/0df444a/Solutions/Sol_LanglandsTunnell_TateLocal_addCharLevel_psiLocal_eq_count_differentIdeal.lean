-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.addCharLevel_psiLocal_eq_count_differentIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/7fc5d255-4bc9-52b5-81b2-40ff20155d32

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_NumberField_StandardAddChar_stdAddChar_apply_mk_zero_eq_fourierChar_trace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.StandardAddChar
open scoped nonZeroDivisors

namespace LanglandsTunnell
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "addCharLevel addCharLevel_def"
namespace PsiLocalLevel
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem single_mul_eq (x : v.adicCompletion K) (z : FiniteAdeleRing (𝓞 K) K) :
    finAdeleSingleAt K v x * z = finAdeleSingleAt K v (x * z v) := by
  refine FiniteAdeleRing.ext K fun w => ?_
  show finAdeleSingleAt K v x w * z w = finAdeleSingleAt K v (x * z v) w
  by_cases hw : w = v
  · subst hw
    rw [finAdeleSingleAt_apply_self, finAdeleSingleAt_apply_self]
  · rw [finAdeleSingleAt_apply_of_ne K v x hw, finAdeleSingleAt_apply_of_ne K v _ hw, zero_mul]

private theorem stdAddChar_finitePart_spec (w : FiniteAdeleRing (𝓞 K) K) :
    (∀ z ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K, stdAddChar K (0, w * z) = 1) ↔
      ∃ r : K, r ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) :
          FractionalIdeal (𝓞 K)⁰ K)
        ∧ w - algebraMap K (FiniteAdeleRing (𝓞 K) K) r
            ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K :=
  NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual K
    (isGlobalAddChar_stdAddChar K) (stdAddChar_apply_mk_zero_eq_fourierChar_trace K) w

section Different

variable (K)

private theorem coe_differentIdeal_eq :
    ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
      = (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K))⁻¹ :=
  coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := K) (B := 𝓞 K)

private theorem dual_one_eq_inv :
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)
      = (((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
  rw [coe_differentIdeal_eq, inv_inv]

private theorem coe_differentIdeal_ne_zero :
    ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
  rw [coe_differentIdeal_eq]
  exact inv_ne_zero (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)

private theorem differentIdeal_ne_bot' : differentIdeal ℤ (𝓞 K) ≠ ⊥ := fun h =>
  coe_differentIdeal_ne_zero K (by rw [h]; exact FractionalIdeal.coeIdeal_bot)

end Different

private theorem psiLocal_eq_one_of_le {n : ℕ} (hn : v.asIdeal ^ n ∣ differentIdeal ℤ (𝓞 K))
    (x : v.adicCompletion K) (hx : Valued.v x ≤ WithZero.exp (n : ℤ)) : psiLocal K v x = 1 := by
  obtain ⟨k, hk⟩ := NumberField.AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 K) K
    (finAdeleSingleAt K v x)
  have hk' : ∀ w : HeightOneSpectrum (𝓞 K),
      (algebraMap K (FiniteAdeleRing (𝓞 K) K) k + finAdeleSingleAt K v x) w
        ∈ w.adicCompletionIntegers K := hk

  have hkw : ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v → w.valuation K k ≤ 1 := by
    intro w hw
    have h := hk' w
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    have hcomp : (algebraMap K (FiniteAdeleRing (𝓞 K) K) k + finAdeleSingleAt K v x) w
        = (k : w.adicCompletion K) := by
      show algebraMap K (FiniteAdeleRing (𝓞 K) K) k w + finAdeleSingleAt K v x w = _
      rw [finAdeleSingleAt_apply_of_ne K v x hw, add_zero, FiniteAdeleRing.algebraMap_apply]
    rwa [hcomp, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h

  have hkv : v.valuation K k ≤ WithZero.exp (n : ℤ) := by
    have h := hk' v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    have hcomp : (algebraMap K (FiniteAdeleRing (𝓞 K) K) k + finAdeleSingleAt K v x) v
        = (k : v.adicCompletion K) + x := by
      show algebraMap K (FiniteAdeleRing (𝓞 K) K) k v + finAdeleSingleAt K v x v = _
      rw [finAdeleSingleAt_apply_self, FiniteAdeleRing.algebraMap_apply]
    rw [hcomp] at h
    have h1 : (1 : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (n : ℤ) := by
      rw [← WithZero.exp_zero]
      exact WithZero.exp_le_exp.mpr (Int.natCast_nonneg n)
    have hk1 : Valued.v ((k : v.adicCompletion K)) ≤ WithZero.exp (n : ℤ) := by
      rw [← add_sub_cancel_right (k : v.adicCompletion K) x]
      exact Valuation.map_sub_le Valued.v (h.trans h1) hx
    rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hk1

  have hD0 := coe_differentIdeal_ne_zero K
  have hr : (-k) ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) :
      FractionalIdeal (𝓞 K)⁰ K) := by
    rw [dual_one_eq_inv K, FractionalIdeal.mem_inv_iff hD0]
    intro y hy
    rw [FractionalIdeal.mem_coeIdeal] at hy
    obtain ⟨a, ha, rfl⟩ := hy
    rw [FractionalIdeal.mem_one_iff]
    have hint : -k * algebraMap (𝓞 K) K a ∈ (algebraMap (𝓞 K) K).range := by
      refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) (K := K)
        (-k * algebraMap (𝓞 K) K a) (fun w => ?_)
      rw [Valuation.map_mul, Valuation.map_neg]
      by_cases hw : w = v
      · subst hw
        have ha' : w.valuation K (algebraMap (𝓞 K) K a) ≤ WithZero.exp (-(n : ℤ)) := by
          rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]
          exact Ideal.le_of_dvd hn ha
        calc w.valuation K k * w.valuation K (algebraMap (𝓞 K) K a)
            ≤ WithZero.exp (n : ℤ) * WithZero.exp (-(n : ℤ)) := mul_le_mul' hkv ha'
          _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
      · exact mul_le_one' (hkw w hw) (HeightOneSpectrum.valuation_le_one w a)
    obtain ⟨b, hb⟩ := RingHom.mem_range.mp hint
    exact ⟨b, hb⟩

  have hker := (stdAddChar_finitePart_spec (finAdeleSingleAt K v x)).mpr
    ⟨-k, hr, by rw [map_neg, sub_neg_eq_add, add_comm]; exact hk⟩
  have h1 := hker 1 (fun w => by
    have : (1 : FiniteAdeleRing (𝓞 K) K) w = 1 := rfl
    rw [this]
    exact one_mem _)
  rw [mul_one] at h1
  rw [psiLocal_apply]
  exact h1

private theorem exists_psiLocal_ne_one {n : ℕ}
    (hn : ¬ v.asIdeal ^ (n + 1) ∣ differentIdeal ℤ (𝓞 K)) :
    ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp ((n : ℤ) + 1) ∧ psiLocal K v x ≠ 1 := by
  by_contra hcon
  have hcon' : ∀ x : v.adicCompletion K,
      Valued.v x ≤ WithZero.exp ((n : ℤ) + 1) → psiLocal K v x = 1 := fun x hx => by
    by_contra hne
    exact hcon ⟨x, hx, hne⟩

  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  set t : K := π⁻¹ ^ (n + 1) with ht
  have hvt : v.valuation K t = WithZero.exp ((n : ℤ) + 1) := by
    rw [ht, map_pow, map_inv₀, hπ, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_nsmul, nsmul_eq_mul,
      mul_one, Nat.cast_add, Nat.cast_one]
  set x₀ : v.adicCompletion K := (t : v.adicCompletion K) with hx₀
  have hvx₀ : Valued.v x₀ = WithZero.exp ((n : ℤ) + 1) := by
    rw [hx₀, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hvt]

  have hall : ∀ z ∈ NumberField.AdelicBox.integralFiniteAdeles (𝓞 K) K,
      stdAddChar K (0, finAdeleSingleAt K v x₀ * z) = 1 := by
    intro z hz
    have hz' : ∀ w : HeightOneSpectrum (𝓞 K), z w ∈ w.adicCompletionIntegers K := hz
    have hzv : Valued.v (z v) ≤ 1 := by
      have h := hz' v
      rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    rw [single_mul_eq, ← psiLocal_apply]
    refine hcon' _ ?_
    rw [Valuation.map_mul, hvx₀]
    calc WithZero.exp ((n : ℤ) + 1) * Valued.v (z v)
        ≤ WithZero.exp ((n : ℤ) + 1) * 1 := mul_le_mul' le_rfl hzv
      _ = WithZero.exp ((n : ℤ) + 1) := mul_one _
  obtain ⟨r, hr, hint⟩ := (stdAddChar_finitePart_spec (finAdeleSingleAt K v x₀)).mp hall
  have hint' : ∀ w : HeightOneSpectrum (𝓞 K),
      (finAdeleSingleAt K v x₀ - algebraMap K (FiniteAdeleRing (𝓞 K) K) r) w
        ∈ w.adicCompletionIntegers K := hint

  have hv1 : Valued.v (x₀ - (r : v.adicCompletion K)) ≤ 1 := by
    have h := hint' v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
    have hcomp : (finAdeleSingleAt K v x₀ - algebraMap K (FiniteAdeleRing (𝓞 K) K) r) v
        = x₀ - (r : v.adicCompletion K) := by
      show finAdeleSingleAt K v x₀ v - algebraMap K (FiniteAdeleRing (𝓞 K) K) r v = _
      rw [finAdeleSingleAt_apply_self, FiniteAdeleRing.algebraMap_apply]
    rwa [hcomp] at h
  have hvr : v.valuation K r = WithZero.exp ((n : ℤ) + 1) := by
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    have hlt : Valued.v (x₀ - (r : v.adicCompletion K)) < Valued.v x₀ := by
      refine hv1.trans_lt ?_
      rw [hvx₀, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by omega)
    rw [← sub_sub_cancel x₀ (r : v.adicCompletion K), Valuation.map_sub_eq_of_lt_left Valued.v hlt,
      hvx₀]

  have hnle : ¬ (differentIdeal ℤ (𝓞 K) ≤ v.asIdeal ^ (n + 1)) := fun h =>
    hn (Ideal.dvd_iff_le.mpr h)
  obtain ⟨a, haD, haP⟩ := SetLike.not_le_iff_exists.mp hnle
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact haP (zero_mem _)
  have hva : WithZero.exp (-((n : ℤ) + 1)) < v.valuation K (algebraMap (𝓞 K) K a) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    have h : ¬ v.intValuation a ≤ WithZero.exp (-((n + 1 : ℕ) : ℤ)) := by
      rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
      exact haP
    push_cast at h
    exact not_le.mp h

  have hD0 := coe_differentIdeal_ne_zero K
  rw [dual_one_eq_inv K, FractionalIdeal.mem_inv_iff hD0] at hr
  have hra := hr (algebraMap (𝓞 K) K a) (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ haD)
  rw [FractionalIdeal.mem_one_iff] at hra
  obtain ⟨b, hb⟩ := hra
  have hle : v.valuation K (r * algebraMap (𝓞 K) K a) ≤ 1 := by
    rw [← hb]
    exact HeightOneSpectrum.valuation_le_one v b
  rw [Valuation.map_mul, hvr] at hle

  have hva0 : v.valuation K (algebraMap (𝓞 K) K a) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr ha0)
  have hexp : v.valuation K (algebraMap (𝓞 K) K a)
      = WithZero.exp (WithZero.log (v.valuation K (algebraMap (𝓞 K) K a))) :=
    (WithZero.exp_log hva0).symm
  rw [hexp, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp] at hle
  rw [hexp, WithZero.exp_lt_exp] at hva
  omega

end LanglandsTunnell.TateLocal.PsiLocalLevel

open _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal.LanglandsTunnell.TateLocal LanglandsTunnell.TateLocal.PsiLocalLevel in

theorem solution
    (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    addCharLevel (psiLocal K v)
      = FractionalIdeal.count K v (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  have hD : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot' K
  have hcount := FractionalIdeal.count_coe K v (J := differentIdeal ℤ (𝓞 K)) hD
  set n : ℕ := (Associates.mk v.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 K))).factors
    with hn
  have hD' : Associates.mk (differentIdeal ℤ (𝓞 K)) ≠ 0 := Associates.mk_ne_zero.mpr hD
  have hdvd : v.asIdeal ^ n ∣ differentIdeal ℤ (𝓞 K) := by
    have h := (Associates.prime_pow_dvd_iff_le hD' v.associates_irreducible).mpr (le_refl n)
    rwa [← Associates.mk_pow, Associates.mk_le_mk_iff_dvd] at h
  have hndvd : ¬ v.asIdeal ^ (n + 1) ∣ differentIdeal ℤ (𝓞 K) := by
    intro h
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow,
      Associates.prime_pow_dvd_iff_le hD' v.associates_irreducible] at h
    omega
  have hS : {m : ℤ | ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp m → psiLocal K v x = 1}
      = Set.Iic (n : ℤ) := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_Iic]
    constructor
    · intro hm
      by_contra hlt
      obtain ⟨x, hx, hne⟩ := exists_psiLocal_ne_one v hndvd
      exact hne (hm x (hx.trans (WithZero.exp_le_exp.mpr (by omega))))
    · intro hm x hx
      exact psiLocal_eq_one_of_le v hdvd x (hx.trans (WithZero.exp_le_exp.mpr hm))
  rw [hcount, addCharLevel_def, hS]
  exact csSup_Iic

end S_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_addCharLevel_psiLocal_eq_count_differentIdeal (solution)
