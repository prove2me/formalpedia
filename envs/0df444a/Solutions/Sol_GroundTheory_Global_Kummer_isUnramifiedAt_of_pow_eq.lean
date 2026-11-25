-- Prove2me | solution 1 for GroundTheory.Global.Kummer.isUnramifiedAt_of_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:13:37.056852+00:00
-- url     : https://prove2.me/submissions/60a0967f-147f-4660-a5dc-4827e231da34

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Unramified
import Theorems.Thm_GroundTheory_Global_Kummer_exists_mul_pow_integral_notMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Global.Kummer
variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [Field M] [NumberField M] [Algebra K M]
namespace GroundTheory.Global.Kummer
theorem _root_.solution {n : ℕ} (a : Kˣ) {α : M} (hα : α ^ n = algebraMap K M a)
    (hgen : IntermediateField.adjoin K {α} = ⊤) (v : HeightOneSpectrum (𝓞 K))
    (hnv : (n : 𝓞 K) ∉ v.asIdeal) (hav : (n : ℤ) ∣ WithZero.log (v.valuation K (a : K)))
    (P : Ideal (𝓞 M)) [P.IsPrime] [P.LiesOver v.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 K) P := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact hnv (by simp)
  obtain ⟨c, hc, b, hb, hbv⟩ := exists_mul_pow_integral_notMem v hn a hav
  set x : M := algebraMap K M c * α with hx
  have hxn : x ^ n = algebraMap K M (algebraMap (𝓞 K) K b) := by
    rw [hx, mul_pow, hα, hb, map_mul, map_pow]
    ring
  have hxint : IsIntegral ℤ x := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hn) ?_
    rw [hxn]
    exact b.isIntegral_coe.algebraMap
  let y : 𝓞 M := ⟨x, hxint⟩
  have hyx : algebraMap (𝓞 M) M y = x := rfl
  have hyb : y ^ n = algebraMap (𝓞 K) (𝓞 M) b := by
    apply FaithfulSMul.algebraMap_injective (𝓞 M) M
    rw [map_pow, hyx, hxn, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 M) M]
  have hKx : IntermediateField.adjoin K {x} = ⊤ := by
    rw [eq_top_iff, ← hgen, IntermediateField.adjoin_simple_le_iff]
    have : α = algebraMap K M c⁻¹ * x := by
      rw [hx, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
    rw [this]
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.mem_adjoin_simple_self K x)
  have hgen' : Algebra.adjoin K {algebraMap (𝓞 M) M y} = ⊤ := by
    rw [hyx, ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic x), hKx, IntermediateField.top_toSubalgebra]
  have hyint : IsIntegral (𝓞 K) y := Algebra.IsIntegral.isIntegral y
  obtain ⟨g, hg⟩ : minpoly (𝓞 K) y ∣ X ^ n - C b :=
    minpoly.isIntegrallyClosed_dvd hyint (by simp [hyb])
  have hder : aeval y (derivative (minpoly (𝓞 K) y)) * aeval y g = (n : 𝓞 M) * y ^ (n - 1) := by
    have := congrArg (fun p => aeval y (derivative p)) hg
    simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_add,
      map_mul, minpoly.aeval, zero_mul, add_zero] at this
    rw [← this]
    simp
  have hnP : (n : 𝓞 M) ∉ P := by
    intro h
    apply hnv
    rw [Ideal.LiesOver.over (P := P) (p := v.asIdeal), Ideal.under, Ideal.mem_comap]
    simpa using h
  have hyP : y ∉ P := by
    intro h
    apply hbv
    have : algebraMap (𝓞 K) (𝓞 M) b ∈ P :=
      hyb ▸ Ideal.pow_mem_of_mem P h n (Nat.pos_of_ne_zero hn)
    rw [Ideal.LiesOver.over (P := P) (p := v.asIdeal), Ideal.under, Ideal.mem_comap]
    exact this
  have hfP : aeval y (derivative (minpoly (𝓞 K) y)) ∉ P := by
    intro h
    have : (n : 𝓞 M) * y ^ (n - 1) ∈ P := hder ▸ Ideal.mul_mem_right _ P h
    rcases Ideal.IsPrime.mem_or_mem ‹_› this with h1 | h1
    · exact hnP h1
    · exact hyP (Ideal.IsPrime.mem_of_pow_mem ‹_› _ h1)
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 K) K M y hgen'
  rw [← not_dvd_differentIdeal_iff]
  intro hdvd
  exact hfP (Ideal.le_of_dvd hdvd hmem)
end GroundTheory.Global.Kummer
