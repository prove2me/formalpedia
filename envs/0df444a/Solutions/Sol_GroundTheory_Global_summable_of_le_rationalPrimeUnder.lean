-- Prove2me | solution 1 for GroundTheory.Global.summable_of_le_rationalPrimeUnder
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T03:59:54.913917+00:00
-- url     : https://prove2.me/submissions/19708b0d-c254-4b23-ae5e-06b981365922

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


theorem solution (g : HeightOneSpectrum (𝓞 L) → ℝ) {h : ℕ → ℝ}
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
