-- Prove2me | solution 1 for KStar.Ram.existsUnique_padic_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:51:23.734949+00:00
-- url     : https://prove2.me/submissions/68934e3c-2229-4da9-a11f-c06e3cac1f62

import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_HeckeCharacterChoice_TendstoUnderCofinite
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_InertiaRamification_ComplDefY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace KStar.Ram
open NumberField IsDedekindDomain IsLocalRing
variable {E : Type*} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
private theorem cdy_val (a : 𝓞 E) :
    Valued.v ((algebraMap (𝓞 E) (w.adicCompletionIntegers E) a : w.adicCompletionIntegers E) :
      w.adicCompletion E) = w.intValuation a := by
  rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact w.valuation_of_algebraMap a
private theorem cdy_max {π : 𝓞 E} (hπ : w.intValuation π = WithZero.exp (-1 : ℤ)) :
    maximalIdeal (w.adicCompletionIntegers E) =
      Ideal.span {algebraMap (𝓞 E) (w.adicCompletionIntegers E) π} := by
  ext y
  rw [Ideal.mem_span_singleton,
    (HeightOneSpectrum.adicCompletionIntegers.integers E w).dvd_iff_le, mem_maximalIdeal,
    mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  change ¬ Valued.v (y : w.adicCompletion E) = 1 ↔ Valued.v (y : w.adicCompletion E) ≤
    Valued.v ((algebraMap (𝓞 E) (w.adicCompletionIntegers E) π : w.adicCompletionIntegers E) :
      w.adicCompletion E)
  rw [cdy_val, hπ]
  have hy : Valued.v (y : w.adicCompletion E) ≤ 1 := y.2
  generalize Valued.v (y : w.adicCompletion E) = t at hy
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · rw [← WithZero.exp_log ht, ← WithZero.exp_zero, WithZero.exp_le_exp] at hy
    rw [← WithZero.exp_log ht, ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.exp_inj]
    omega
private theorem cdy_pow (π : 𝓞 E) (hπ : w.intValuation π = WithZero.exp (-1 : ℤ)) (n : ℕ) :
    w.intValuation (π ^ n) = WithZero.exp (-(n : ℤ)) := by
  rw [map_pow, hπ, ← WithZero.exp_nsmul]
  simp
private theorem cdy_mem (n : ℕ) (y : w.adicCompletionIntegers E) :
    y ∈ maximalIdeal (w.adicCompletionIntegers E) ^ n ↔
      Valued.v (y : w.adicCompletion E) ≤ WithZero.exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  rw [cdy_max w hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    (HeightOneSpectrum.adicCompletionIntegers.integers E w).dvd_iff_le, ← map_pow,
    ← cdy_pow w π hπ n, ← cdy_val]
  rfl
private theorem cdy_comap (n : ℕ) : (maximalIdeal (w.adicCompletionIntegers E) ^ n).comap
    (algebraMap (𝓞 E) (w.adicCompletionIntegers E)) = w.asIdeal ^ n := by
  ext a
  rw [Ideal.mem_comap, cdy_mem, cdy_val, w.intValuation_le_pow_iff_mem]
variable (l : ℕ) [Fact l.Prime] [w.asIdeal.LiesOver (Ideal.span {(l : ℤ)})]
end KStar.Ram
end

set_option autoImplicit false
open KStar KStar.Ram
open NumberField IsDedekindDomain IsLocalRing
variable {E : Type*} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
variable (l : ℕ) [Fact l.Prime] [w.asIdeal.LiesOver (Ideal.span {(l : ℤ)})]
namespace KStar.Ram
theorem _root_.solution :
    ∃ (f : ℤ_[l] →+* w.adicCompletionIntegers E) (F : ℚ_[l] →+* w.adicCompletion E),
      Function.Injective f ∧ Continuous F ∧ (∀ x : ℤ_[l], F x = f x) ∧ (∀ f', f' = f) ∧
        ∀ F' : ℚ_[l] →+* w.adicCompletion E, Continuous F' → F' = F := by
  let p : Nat.Primes := ⟨l, Fact.out⟩
  let u : HeightOneSpectrum (𝓞 ℚ) := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p
  have hl : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    have : (l : ℤ) ∈ Ideal.span {(l : ℤ)} := Ideal.mem_span_singleton_self _
    rw [Ideal.mem_of_liesOver w.asIdeal] at this
    simpa using this
  have hu : u.asIdeal = Ideal.span {((l : ℕ) : 𝓞 ℚ)} := by
    change (Ideal.span {(l : ℤ)}).map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm = _
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  have : w.asIdeal.LiesOver u.asIdeal := by
    refine ⟨u.isMaximal.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) ?_⟩
    rw [hu, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hl
  let F : ℚ_[l] →+* w.adicCompletion E :=
    (KStar.Choice.complMap u w).comp (Padic.adicCompletionEquiv (𝓞 ℚ) p).toRingEquiv.toRingHom
  have hF : Continuous F :=
    (KStar.Choice.continuous_complMap u w).comp (Padic.adicCompletionEquiv (𝓞 ℚ) p).continuous
  have hm : ∀ x : ℤ_[l], F.comp PadicInt.Coe.ringHom x ∈ w.adicCompletionIntegers E := by
    intro x
    refine KStar.Choice.complMap_mem u w ?_
    have := (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p x).2
    rw [PadicInt.coe_adicCompletionIntegersEquiv_apply] at this
    exact this
  let f : ℤ_[l] →+* w.adicCompletionIntegers E :=
    (F.comp PadicInt.Coe.ringHom).codRestrict (w.adicCompletionIntegers E) hm
  refine ⟨f, F, fun x y h => ?_, hF, fun x => rfl, fun f' => ?_, fun F' hF' => ?_⟩
  · exact Subtype.ext (F.injective (congrArg Subtype.val h))
  · have hlm : ((l : ℕ) : w.adicCompletionIntegers E) ∈
        maximalIdeal (w.adicCompletionIntegers E) := by
      have h1 := cdy_comap w 1
      rw [pow_one, pow_one] at h1
      rw [← h1, Ideal.mem_comap, map_natCast] at hl
      exact hl
    refine RingHom.ext fun x => ?_
    rw [← sub_eq_zero, ← Ideal.mem_bot,
      ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (w.adicCompletionIntegers E))
        (maximalIdeal.isMaximal _).ne_top, Ideal.mem_iInf]
    intro k
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.1 (PadicInt.appr_spec k x)
    have hx : x = (x.appr k : ℤ_[l]) + (l : ℤ_[l]) ^ k * z := by rw [← hz]; ring
    have : f' x - f x = (l : w.adicCompletionIntegers E) ^ k * (f' z - f z) := by
      conv_lhs => rw [hx]
      simp only [map_add, map_mul, map_pow, map_natCast]
      ring
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlm k)
  · refine DFunLike.coe_injective ((Padic.denseRange_ratCast l).equalizer hF' hF ?_)
    funext q
    simp only [Function.comp_apply, map_ratCast]
end KStar.Ram
