-- Prove2me | solution 1 for GroundTheory.Global.summable_indicator_not_prime
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T04:00:05.629446+00:00
-- url     : https://prove2.me/submissions/2fb9728d-8c0e-4041-b572-487ea65cfcd5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
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
open NumberField IsDedekindDomain Filter Topology Set
noncomputable section
variable {K L : Type*} [Field L] [NumberField L]


private theorem by_prime_under (g : HeightOneSpectrum (𝓞 L) → ℝ) {h : ℕ → ℝ}
    (hg : ∀ w, 0 ≤ g w) (hh0 : ∀ n, 0 ≤ h n) (hh : Summable h)
    (hgh : ∀ w, g w ≤ h (rationalPrimeUnder w)) : Summable g := by
  classical
  let p : HeightOneSpectrum (𝓞 L) → ℕ := rationalPrimeUnder
  let d := Module.finrank ℚ L
  refine summable_of_sum_le (c := (d : ℝ) * ∑' n, h n) hg ?_
  intro T
  have fiber (n : ℕ) (hn : n ∈ T.image p) : (T.filter fun w => p w = n).card ≤ d := by
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hn
    let J := v.asIdeal.under ℤ
    have J0 : J ≠ ⊥ := Ideal.under_ne_bot ℤ v.ne_bot
    haveI : J.IsMaximal := (inferInstance : J.IsPrime).isMaximal J0
    refine le_trans (Finset.card_le_card_of_injOn HeightOneSpectrum.asIdeal (t := IsDedekindDomain.primesOverFinset J (𝓞 L)) ?_ HeightOneSpectrum.asIdeal_injective.injOn) ?_
    · intro w hw
      have he : p w = p v := (Finset.mem_filter.mp hw).2
      have hu : w.asIdeal.under ℤ = J := by
        rw [← Int.ideal_span_absNorm_eq_self (w.asIdeal.under ℤ), ← Int.ideal_span_absNorm_eq_self J]; change Ideal.span {((p w : ℕ) : ℤ)} = Ideal.span {((p v : ℕ) : ℤ)}; rw [he]
      apply (IsDedekindDomain.mem_primesOverFinset_iff J0 _).mpr; exact ⟨w.isPrime, ⟨hu.symm⟩⟩
    · exact Ideal.card_primesOverFinset_le_finrank (𝓞 L) ℚ L J0
  calc
    _ ≤ ∑ w ∈ T, h (p w) := Finset.sum_le_sum fun w _ => hgh w
    _ = ∑ n ∈ T.image p, ∑ w ∈ T.filter (fun w => p w = n), h (p w) := (Finset.sum_fiberwise_of_maps_to (fun _ => Finset.mem_image_of_mem p) _).symm
    _ ≤ ∑ n ∈ T.image p, (d : ℝ) * h n := by
      apply Finset.sum_le_sum; intro n hn
      calc
        _ = ∑ _w ∈ T.filter (fun w => p w = n), h n := Finset.sum_congr rfl (fun w hw => congrArg h (Finset.mem_filter.mp hw).2)
        _ = ((T.filter fun w => p w = n).card : ℝ) * h n := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast fiber n hn) (hh0 n)
    _ ≤ _ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hh.sum_le_tsum _ (fun n _ => hh0 n)) (Nat.cast_nonneg _)



theorem solution {s : ℝ} (hs : 1 / 2 < s) :
    Summable ({w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime}.indicator
      fun w => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s)) := by
  classical
  apply by_prime_under (h := fun p => (p : ℝ) ^ (-2 * s))
  · intro w; unfold Set.indicator; split <;> positivity
  · intro n; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  · exact Real.summable_nat_rpow.mpr (by linarith)
  · intro w; by_cases hm : (Ideal.absNorm w.asIdeal).Prime
    · rw [Set.indicator_of_notMem (by simpa using hm)]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · rw [Set.indicator_of_mem (show w ∈ {z : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm z.asIdeal).Prime} from hm)]
      let J := w.asIdeal.under ℤ
      have hJ : (rationalPrimeUnder w).Prime := (Int.prime_absNorm J).mpr (Ideal.prime_of_isPrime (Ideal.under_ne_bot ℤ w.ne_bot) inferInstance)
      let f := w.asIdeal.inertiaDeg ℤ
      have H : (rationalPrimeUnder w) ^ f = Ideal.absNorm w.asIdeal := Ideal.absNorm_pow_inertiaDeg J w.asIdeal
      have hfpos : 0 < f := Ideal.inertiaDeg_pos w.asIdeal ℤ
      have hf : 2 ≤ f := by
        by_contra! hh; have ho : f = 1 := by omega
        exact hm (by simpa [← H,ho] using hJ)
      have hsq : (rationalPrimeUnder w)^2 ≤ Ideal.absNorm w.asIdeal := H ▸ Nat.pow_le_pow_right hJ.pos hf
      have hc : (rationalPrimeUnder w : ℝ)^2 ≤ (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast hsq
      calc
        _ ≤ ((rationalPrimeUnder w : ℝ)^2) ^ (-s) := Real.rpow_le_rpow_of_nonpos (by exact pow_pos (Nat.cast_pos.mpr hJ.pos) 2) hc (by linarith)
        _ = _ := by rw [← Real.rpow_natCast (rationalPrimeUnder w : ℝ) 2, ← Real.rpow_mul (Nat.cast_nonneg _)]; congr 1 <;> push_cast <;> ring
