-- Prove2me | solution 1 for GlobalTheory.CompleteDiscreteValuationRing.exists_dvr_of_dim_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:20:59.185973+00:00
-- url     : https://prove2.me/submissions/0321c6cb-429f-464d-a105-09d9ca7e644b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDvrOfDimOne
import Theorems.Thm_GlobalTheory_CompleteDiscreteValuationRing_fg_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.CompleteDiscreteValuationRing
namespace GlobalTheory.CompleteDiscreteValuationRing
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O]
    [IsNoetherianRing O] [Ring.KrullDimLE 1 O] (t : O) (ht0 : t ≠ 0) (ht : ¬ IsUnit t) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (f : O →+* W), Function.Injective f ∧ ¬ IsUnit (f t) := by
  let K := FractionRing O
  obtain ⟨B, hB, hloc⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap O K)
  let f : O →+* B := (algebraMap O K).codRestrict B.toSubring hB
  have hf : ∀ x, ((f x : B) : K) = algebraMap O K x := fun _ => rfl
  have finj : Function.Injective f := fun x y h =>
    IsFractionRing.injective O K (by rw [← hf, ← hf, h])
  have hft : ¬ IsUnit (f t) := fun h => ht (hloc.1 _ h)
  have hpow : ∀ s : O, s ≠ 0 → ∃ n : ℕ, s ∣ t ^ n := by
    intro s hs
    have : t ∈ (Ideal.span {s}).radical := by
      rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
      rintro P ⟨hP, hP'⟩
      have hne : P ≠ ⊥ := by
        rintro rfl
        exact hs (by simpa using hP)
      have hmax : Ideal.IsMaximal P :=
        Ring.krullDimLE_one_iff_of_noZeroDivisors.1 inferInstance P hne hP'
      rw [IsLocalRing.eq_maximalIdeal hmax]
      exact ht
    obtain ⟨n, hn⟩ := this
    exact ⟨n, Ideal.mem_span_singleton.1 hn⟩
  have hfrac : ∀ x : B, ∃ r s : O, s ≠ 0 ∧ f s * x = f r := by
    intro x
    obtain ⟨r, s, hs, e⟩ := IsFractionRing.div_surjective (A := O) (x : K)
    have hs0 := nonZeroDivisors.ne_zero hs
    refine ⟨r, s, hs0, Subtype.ext ?_⟩
    have : algebraMap O K s ≠ 0 := fun h => hs0 (IsFractionRing.injective O K (by simpa using h))
    change algebraMap O K s * (x : K) = algebraMap O K r
    rw [← e]; exact mul_div_cancel₀ _ this
  letI : Algebra O B := f.toAlgebra
  have hN : IsNoetherianRing B := by
    rw [isNoetherianRing_iff_ideal_fg]
    intro J
    by_cases hJ : J = ⊥
    · rw [hJ]; exact Submodule.fg_bot
    obtain ⟨x, hxJ, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
    obtain ⟨r, s, hs, e⟩ := hfrac x
    have hr : r ≠ 0 := by
      rintro rfl
      rw [map_zero] at e
      exact mul_ne_zero ((map_ne_zero_iff f finj).2 hs) hx0 e
    obtain ⟨n, c, hc⟩ := hpow r hr
    have hne : t ^ (n + 1) ≠ 0 := pow_ne_zero _ ht0
    refine fg_of_mem (t ^ (n + 1)) ((map_ne_zero_iff f finj).2 hne) ?_ ?_ J ?_
    · exact (isFiniteLength_iff_isNoetherian_isArtinian.1
        (isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hne))).2
    · intro y
      obtain ⟨r', s', hs', e'⟩ := hfrac y
      obtain ⟨m, c', hc'⟩ := hpow s' hs'
      refine ⟨m, r' * c' * t ^ (n * m), ?_⟩
      change f _ ^ m * y = f _
      rw [map_mul, map_mul, ← e', ← map_pow, ← pow_mul, add_mul, one_mul, pow_add, hc',
        map_mul, map_mul]
      ring
    · change f _ ∈ J
      rw [pow_succ, hc, map_mul, map_mul, ← e]
      exact J.mul_mem_right _ (J.mul_mem_right _ (J.mul_mem_left _ hxJ))
  have hP : IsPrincipalIdealRing B := IsPrincipalIdealRing.of_isNoetherianRing_of_isBezout
  have hD : IsDiscreteValuationRing B :=
    { not_a_field' := fun h => by
        have h1 : f t ∈ maximalIdeal B := hft
        rw [h] at h1
        exact ht0 ((map_eq_zero_iff f finj).1 h1) }
  exact ⟨B, inferInstance, inferInstance, hD, f, finj, hft⟩
end GlobalTheory.CompleteDiscreteValuationRing
