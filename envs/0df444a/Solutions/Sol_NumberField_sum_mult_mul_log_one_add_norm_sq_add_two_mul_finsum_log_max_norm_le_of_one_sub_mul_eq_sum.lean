-- Prove2me | solution 1 for NumberField.sum_mult_mul_log_one_add_norm_sq_add_two_mul_finsum_log_max_norm_le_of_one_sub_mul_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/43ffa0cf-a862-5d9c-8498-18d0305a5ebe

import Mathlib
import Theorems.Thm_NumberField_finsum_posLog_inv_norm_one_sub_add_sum_mult_mul_posLog_inv_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_sum_mult_mul_log_one_add_norm_sq_add_two_mul_finsum_log_max_norm_le_of_one_sub_mul_eq_sum

set_option autoImplicit false

open NumberField IsDedekindDomain

noncomputable section

namespace ExcHeight

variable {F : Type} [Field F] [NumberField F]

def evf (v : HeightOneSpectrum (𝓞 F)) : AdeleRing (𝓞 F) F →+* v.adicCompletion F :=
  (RestrictedProduct.evalRingHom _ v).comp (RingHom.snd _ _)

theorem evf_apply (v : HeightOneSpectrum (𝓞 F)) (a : AdeleRing (𝓞 F) F) : evf v a = a.2 v := rfl

theorem evf_algebraMap (v : HeightOneSpectrum (𝓞 F)) (a : F) :
    evf v (algebraMap F (AdeleRing (𝓞 F) F) a) = algebraMap F (v.adicCompletion F) a := rfl

def evi (w : InfinitePlace F) : AdeleRing (𝓞 F) F →+* w.Completion :=
  (Pi.evalRingHom _ w).comp (RingHom.fst _ _)

theorem evi_apply (w : InfinitePlace F) (a : AdeleRing (𝓞 F) F) : evi w a = a.1 w := rfl

theorem norm_evi_algebraMap (w : InfinitePlace F) (a : F) : ‖evi w (algebraMap F (AdeleRing (𝓞 F) F) a)‖ = w a := by
  have : evi w (algebraMap F (AdeleRing (𝓞 F) F) a) = (((WithAbs.equiv w.1).symm a : WithAbs w.1) : w.Completion) := rfl
  rw [this, NumberField.InfinitePlace.Completion.norm_coe]
  simp

theorem log_max_one_eq_posLog {t : ℝ} (ht : 0 ≤ t) : Real.log (max 1 t) = Real.posLog t := by
  simp only [Real.posLog_def, Pi.sup_apply, Pi.zero_apply]
  rcases le_total t 1 with h | h
  · rw [max_eq_left h, Real.log_one, max_eq_left (Real.log_nonpos ht h)]
  · rw [max_eq_right h, max_eq_right (Real.log_nonneg h)]

theorem posLog_of_one_le {t : ℝ} (ht : 1 ≤ t) : Real.posLog t = Real.log t :=
  Real.posLog_eq_log (by rwa [abs_of_nonneg (zero_le_one.trans ht)])

theorem posLog_pow_of_one_le {t : ℝ} (ht : 1 ≤ t) (n : ℕ) : Real.posLog (t ^ n) = n * Real.log t := by
  rw [posLog_of_one_le (one_le_pow₀ ht), Real.log_pow]

theorem posLog_natCast (n : ℕ) : Real.posLog (n : ℝ) = Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.posLog_def]
  · exact posLog_of_one_le (by exact_mod_cast hn)

theorem log_one_add_sq_le (t : ℝ) (ht : 0 ≤ t) : Real.log (1 + t ^ 2) ≤ Real.log 2 + 2 * Real.posLog t := by
  have hm : 1 ≤ max 1 t := le_max_left _ _
  have h1 : 1 + t ^ 2 ≤ 2 * (max 1 t) ^ 2 := by
    have : t ≤ max 1 t := le_max_right _ _
    nlinarith
  calc Real.log (1 + t ^ 2) ≤ Real.log (2 * (max 1 t) ^ 2) :=
        Real.log_le_log (by positivity) h1
    _ = Real.log 2 + 2 * Real.posLog t := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, log_max_one_eq_posLog ht]; push_cast; ring

theorem posLog_le_of_le_mul_mul {t a b e : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e)
    (h : t ≤ a * b * e) : Real.posLog t ≤ Real.posLog a + Real.posLog b + Real.posLog e := by
  have h1 := Real.posLog_le_posLog ht h
  have h2 : Real.posLog (a * b * e) ≤ Real.posLog (a * b) + Real.posLog e := Real.posLog_mul
  have h3 : Real.posLog (a * b) ≤ Real.posLog a + Real.posLog b := Real.posLog_mul
  linarith

end ExcHeight

open ExcHeight in
theorem solution
    (F : Type) [Field F] [NumberField F] (c : F) (hc : c ≠ 1) (ℓ : ℕ)
    (x : AdeleRing (𝓞 F) F) (P U Q : ℕ → AdeleRing (𝓞 F) F)
    (hx : algebraMap F (AdeleRing (𝓞 F) F) (1 - c) * x = ∑ j ∈ Finset.range ℓ, P j * U j)
    (hcQ : algebraMap F (AdeleRing (𝓞 F) F) c = ∏ i ∈ Finset.range ℓ, Q i)
    (W : Finset (HeightOneSpectrum (𝓞 F))) (Λ : HeightOneSpectrum (𝓞 F) → ℝ) (Λinf : InfinitePlace F → ℝ)
    (hΛ : ∀ w, 1 ≤ Λ w) (hΛW : ∀ w, w ∉ W → Λ w = 1) (hΛinf : ∀ w, 1 ≤ Λinf w)
    (hP : ∀ j, j < ℓ → (∀ w : HeightOneSpectrum (𝓞 F), ‖(P j).2 w‖ ≤ Λ w) ∧ ∀ w : InfinitePlace F, ‖(P j).1 w‖ ≤ Λinf w)
    (hU : ∀ j, j < ℓ → (∀ w : HeightOneSpectrum (𝓞 F), ‖(U j).2 w‖ ≤ Λ w) ∧ ∀ w : InfinitePlace F, ‖(U j).1 w‖ ≤ Λinf w)
    (hQ : ∀ i, i < ℓ → (∀ w : HeightOneSpectrum (𝓞 F), ‖(Q i).2 w‖ ≤ Λ w) ∧ ∀ w : InfinitePlace F, ‖(Q i).1 w‖ ≤ Λinf w) :
    (∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (1 + ‖x.1 w‖ ^ 2)) +
        2 * ∑ᶠ v : HeightOneSpectrum (𝓞 F), Real.log (max 1 ‖x.2 v‖) ≤
      (2 * ℓ + 4) * ((∑ w ∈ W, Real.log (Λ w)) + ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (Λinf w)) +
        (4 * Real.log 2 + 2 * Real.log ℓ) * ∑ w : InfinitePlace F, (w.mult : ℝ) := by
  classical
  set d : F := 1 - c with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 (Ne.symm hc)

  have hdv : ∀ v : HeightOneSpectrum (𝓞 F), algebraMap F (v.adicCompletion F) d ≠ 0 := fun v => (map_ne_zero _).2 hd0
  have hcompv : ∀ v : HeightOneSpectrum (𝓞 F),
      algebraMap F (v.adicCompletion F) d * x.2 v = ∑ j ∈ Finset.range ℓ, (P j).2 v * (U j).2 v := by
    intro v
    have := congrArg (evf v) hx
    rwa [map_mul, map_sum, evf_algebraMap] at this
  have hΛ0 : ∀ w, 0 ≤ Λ w := fun w => zero_le_one.trans (hΛ w)
  have hxv : ∀ v : HeightOneSpectrum (𝓞 F), ‖x.2 v‖ ≤ Λ v ^ 2 * ‖algebraMap F (v.adicCompletion F) d‖⁻¹ := by
    intro v
    have hs : ‖∑ j ∈ Finset.range ℓ, (P j).2 v * (U j).2 v‖ ≤ Λ v ^ 2 := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j hj => ?_
      rw [norm_mul, sq]
      have hj' := Finset.mem_range.1 hj
      exact mul_le_mul ((hP j hj').1 v) ((hU j hj').1 v) (norm_nonneg _) (hΛ0 v)
    have hx' : x.2 v = (algebraMap F (v.adicCompletion F) d)⁻¹ * ∑ j ∈ Finset.range ℓ, (P j).2 v * (U j).2 v := by
      rw [← hcompv v, ← mul_assoc, inv_mul_cancel₀ (hdv v), one_mul]
    rw [hx', norm_mul, norm_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right hs (inv_nonneg.2 (norm_nonneg _))
  have hfinpt : ∀ v : HeightOneSpectrum (𝓞 F),
      Real.log (max 1 ‖x.2 v‖) ≤ 2 * Real.log (Λ v) + Real.posLog ‖algebraMap F (v.adicCompletion F) d‖⁻¹ := by
    intro v
    rw [log_max_one_eq_posLog (norm_nonneg _)]
    calc Real.posLog ‖x.2 v‖ ≤ Real.posLog (Λ v ^ 2 * ‖algebraMap F (v.adicCompletion F) d‖⁻¹) :=
          Real.posLog_le_posLog (norm_nonneg _) (hxv v)
      _ ≤ Real.posLog (Λ v ^ 2) + Real.posLog ‖algebraMap F (v.adicCompletion F) d‖⁻¹ := Real.posLog_mul
      _ = 2 * Real.log (Λ v) + Real.posLog ‖algebraMap F (v.adicCompletion F) d‖⁻¹ := by
          rw [posLog_pow_of_one_le (hΛ v)]; push_cast; ring

  have hcv : ∀ v : HeightOneSpectrum (𝓞 F), Real.posLog ‖algebraMap F (v.adicCompletion F) c‖ ≤ ℓ * Real.log (Λ v) := by
    intro v
    have hc' : algebraMap F (v.adicCompletion F) c = ∏ i ∈ Finset.range ℓ, (Q i).2 v := by
      have := congrArg (evf v) hcQ
      rwa [map_prod, evf_algebraMap] at this
    have hle : ‖algebraMap F (v.adicCompletion F) c‖ ≤ Λ v ^ ℓ := by
      rw [hc', norm_prod]
      calc ∏ i ∈ Finset.range ℓ, ‖(Q i).2 v‖ ≤ ∏ i ∈ Finset.range ℓ, Λ v :=
            Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i hi => (hQ i (Finset.mem_range.1 hi)).1 v
        _ = Λ v ^ ℓ := by rw [Finset.prod_const, Finset.card_range]
    calc Real.posLog ‖algebraMap F (v.adicCompletion F) c‖ ≤ Real.posLog (Λ v ^ ℓ) := Real.posLog_le_posLog (norm_nonneg _) hle
      _ = ℓ * Real.log (Λ v) := posLog_pow_of_one_le (hΛ v) ℓ

  have hdw : ∀ w : InfinitePlace F, 0 < w d := fun w => AbsoluteValue.pos w.1 hd0
  have hcompw : ∀ w : InfinitePlace F, evi w (algebraMap F (AdeleRing (𝓞 F) F) d) * x.1 w =
      ∑ j ∈ Finset.range ℓ, (P j).1 w * (U j).1 w := by
    intro w
    have := congrArg (evi w) hx
    rwa [map_mul, map_sum] at this
  have hΛi0 : ∀ w, 0 ≤ Λinf w := fun w => zero_le_one.trans (hΛinf w)
  have hxw : ∀ w : InfinitePlace F, ‖x.1 w‖ ≤ (ℓ : ℝ) * Λinf w ^ 2 * (w d)⁻¹ := by
    intro w
    have hs : ‖∑ j ∈ Finset.range ℓ, (P j).1 w * (U j).1 w‖ ≤ (ℓ : ℝ) * Λinf w ^ 2 := by
      calc ‖∑ j ∈ Finset.range ℓ, (P j).1 w * (U j).1 w‖ ≤ ∑ j ∈ Finset.range ℓ, ‖(P j).1 w * (U j).1 w‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ Finset.range ℓ, Λinf w ^ 2 := Finset.sum_le_sum fun j hj => by
            rw [norm_mul, sq]
            have hj' := Finset.mem_range.1 hj
            exact mul_le_mul ((hP j hj').2 w) ((hU j hj').2 w) (norm_nonneg _) (hΛi0 w)
        _ = (ℓ : ℝ) * Λinf w ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hne : evi w (algebraMap F (AdeleRing (𝓞 F) F) d) ≠ 0 := by
      intro h0; have := norm_evi_algebraMap w d; rw [h0, norm_zero] at this; exact (hdw w).ne' this.symm
    have hx' : x.1 w = (evi w (algebraMap F (AdeleRing (𝓞 F) F) d))⁻¹ * ∑ j ∈ Finset.range ℓ, (P j).1 w * (U j).1 w := by
      rw [← hcompw w, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    rw [hx', norm_mul, norm_inv, norm_evi_algebraMap, mul_comm]
    exact mul_le_mul_of_nonneg_right hs (inv_nonneg.2 (hdw w).le)
  have hinfpt : ∀ w : InfinitePlace F, Real.log (1 + ‖x.1 w‖ ^ 2) ≤
      Real.log 2 + 2 * (Real.log ℓ + 2 * Real.log (Λinf w) + Real.posLog (w d)⁻¹) := by
    intro w
    refine (log_one_add_sq_le _ (norm_nonneg _)).trans ?_
    have h1 : Real.posLog ‖x.1 w‖ ≤ Real.posLog (ℓ : ℝ) + Real.posLog (Λinf w ^ 2) + Real.posLog (w d)⁻¹ :=
      posLog_le_of_le_mul_mul (norm_nonneg _) (Nat.cast_nonneg _) (by positivity) (inv_nonneg.2 (hdw w).le) (hxw w)
    rw [posLog_natCast, posLog_pow_of_one_le (hΛinf w)] at h1
    push_cast at h1
    linarith
  have hcw : ∀ w : InfinitePlace F, Real.posLog (w c) ≤ ℓ * Real.log (Λinf w) := by
    intro w
    have hc' : evi w (algebraMap F (AdeleRing (𝓞 F) F) c) = ∏ i ∈ Finset.range ℓ, (Q i).1 w := by
      have := congrArg (evi w) hcQ
      rwa [map_prod] at this
    have hle : w c ≤ Λinf w ^ ℓ := by
      rw [← norm_evi_algebraMap w c, hc', norm_prod]
      calc ∏ i ∈ Finset.range ℓ, ‖(Q i).1 w‖ ≤ ∏ i ∈ Finset.range ℓ, Λinf w :=
            Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i hi => (hQ i (Finset.mem_range.1 hi)).2 w
        _ = Λinf w ^ ℓ := by rw [Finset.prod_const, Finset.card_range]
    calc Real.posLog (w c) ≤ Real.posLog (Λinf w ^ ℓ) := Real.posLog_le_posLog (AbsoluteValue.nonneg _ _) hle
      _ = ℓ * Real.log (Λinf w) := posLog_pow_of_one_le (hΛinf w) ℓ

  have hsuppW : ∀ v, v ∉ W → Real.log (Λ v) = 0 := fun v hv => by rw [hΛW v hv, Real.log_one]
  obtain hSd := (algebraMap F (AdeleRing (𝓞 F) F) d⁻¹).2.2
  set Sd : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.1 hSd).toFinset with hSddef
  have hoffSd : ∀ v, v ∉ Sd → Real.posLog ‖algebraMap F (v.adicCompletion F) d‖⁻¹ = 0 := by
    intro v hv
    have hmem : (algebraMap F (AdeleRing (𝓞 F) F) d⁻¹).2 v ∈ v.adicCompletionIntegers F := by
      by_contra h; exact hv ((Set.Finite.mem_toFinset _).2 h)
    have h1 : ‖algebraMap F (v.adicCompletion F) d⁻¹‖ ≤ 1 :=
      (Valued.toNormedField.norm_le_one_iff).2 ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ v).1 hmem)
    rw [map_inv₀, norm_inv] at h1
    simp only [Real.posLog_def, Pi.sup_apply, Pi.zero_apply]
    rw [max_eq_left (Real.log_nonpos (inv_nonneg.2 (norm_nonneg _)) h1)]
  set S : Finset (HeightOneSpectrum (𝓞 F)) := W ∪ Sd with hSdef
  have hsub1 : (Function.support fun v : HeightOneSpectrum (𝓞 F) => Real.log (max 1 ‖x.2 v‖)) ⊆ ↑S := by
    intro v hv
    by_contra hS
    rw [Finset.mem_coe, hSdef, Finset.mem_union, not_or] at hS
    apply hv
    have h := hfinpt v
    rw [hsuppW v hS.1, hoffSd v hS.2] at h
    have h0 : 0 ≤ Real.log (max 1 ‖x.2 v‖) := Real.log_nonneg (le_max_left _ _)
    linarith
  have hsub2 : (Function.support fun v : HeightOneSpectrum (𝓞 F) => Real.posLog ‖algebraMap F (v.adicCompletion F) d‖⁻¹) ⊆ ↑S := by
    intro v hv; by_contra hS
    rw [Finset.mem_coe, hSdef, Finset.mem_union, not_or] at hS
    exact hv (hoffSd v hS.2)
  have hsub3 : (Function.support fun v : HeightOneSpectrum (𝓞 F) => Real.posLog ‖algebraMap F (v.adicCompletion F) c‖) ⊆ ↑W := by
    intro v hv; by_contra hW'
    apply hv
    have h := hcv v
    rw [hsuppW v hW', mul_zero] at h
    exact le_antisymm h Real.posLog_nonneg
  have hfin_sum : (∑ᶠ v : HeightOneSpectrum (𝓞 F), Real.log (max 1 ‖x.2 v‖)) ≤
      2 * (∑ w ∈ W, Real.log (Λ w)) + ∑ᶠ v : HeightOneSpectrum (𝓞 F), Real.posLog ‖algebraMap F (v.adicCompletion F) d‖⁻¹ := by
    rw [finsum_eq_sum_of_support_subset _ hsub1, finsum_eq_sum_of_support_subset _ hsub2]
    have hW' : ∑ w ∈ W, Real.log (Λ w) = ∑ v ∈ S, Real.log (Λ v) := by
      refine (Finset.sum_subset Finset.subset_union_left fun v _ hv => hsuppW v hv)
    rw [hW', Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun v _ => hfinpt v
  have hcfin_sum : (∑ᶠ v : HeightOneSpectrum (𝓞 F), Real.posLog ‖algebraMap F (v.adicCompletion F) c‖) ≤ ℓ * ∑ w ∈ W, Real.log (Λ w) := by
    rw [finsum_eq_sum_of_support_subset _ hsub3, Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ => hcv v

  have hm0 : ∀ w : InfinitePlace F, 0 ≤ (w.mult : ℝ) := fun w => Nat.cast_nonneg _
  have hinf_sum : (∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (1 + ‖x.1 w‖ ^ 2)) ≤
      (Real.log 2 + 2 * Real.log ℓ) * (∑ w : InfinitePlace F, (w.mult : ℝ)) +
        4 * (∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (Λinf w)) +
        2 * ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.posLog (w d)⁻¹ := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w _ => ?_
    have := mul_le_mul_of_nonneg_left (hinfpt w) (hm0 w)
    linarith
  have hcinf_sum : (∑ w : InfinitePlace F, (w.mult : ℝ) * (Real.log 2 + Real.posLog (w c))) ≤
      Real.log 2 * (∑ w : InfinitePlace F, (w.mult : ℝ)) + ℓ * ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (Λinf w) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun w _ => ?_
    have := mul_le_mul_of_nonneg_left (hcw w) (hm0 w)
    linarith

  have hPF := NumberField.finsum_posLog_inv_norm_one_sub_add_sum_mult_mul_posLog_inv_le F c
  have hH0 : 0 ≤ ∑ w ∈ W, Real.log (Λ w) := Finset.sum_nonneg fun w _ => Real.log_nonneg (hΛ w)
  have hHi0 : 0 ≤ ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (Λinf w) :=
    Finset.sum_nonneg fun w _ => mul_nonneg (hm0 w) (Real.log_nonneg (hΛinf w))
  have hM0 : 0 ≤ ∑ w : InfinitePlace F, (w.mult : ℝ) := Finset.sum_nonneg fun w _ => hm0 w
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hℓ0 : 0 ≤ (ℓ : ℝ) := Nat.cast_nonneg _
  nlinarith [hfin_sum, hcfin_sum, hinf_sum, hcinf_sum, hPF, hH0, hHi0, hM0, hlog2, hℓ0,
    mul_nonneg hℓ0 hH0, mul_nonneg hℓ0 hHi0, mul_nonneg hlog2 hM0]

end
end S_NumberField_sum_mult_mul_log_one_add_norm_sq_add_two_mul_finsum_log_max_norm_le_of_one_sub_mul_eq_sum
end P2MW
export P2MW.S_NumberField_sum_mult_mul_log_one_add_norm_sq_add_two_mul_finsum_log_max_norm_le_of_one_sub_mul_eq_sum (solution)
