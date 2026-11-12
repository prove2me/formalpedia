-- Prove2me | solution 1 for LinearHashingPoissonesque.ExpectedLoads.poisson_approximation_expectation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T22:14:52.193851+00:00
-- url     : https://prove2.me/submissions/4ba5fd8a-885b-4c0b-a559-65919e2625d0

import Mathlib
import Definitions.Def_LinMaxLoad_avgLin
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_LogPotential
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_ExtremeLoads
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_PoissonThresholds
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_VariationalBounds
import Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_variational_expectation

section
set_option autoImplicit false

namespace LinearHashingPoissonesque.Dev.PoissonApprox
open LinearHashingPoissonesque.ExpectedLoads

lemma take_le_reverse_take (l : List ℕ) (hl : l.Pairwise (· ≤ ·)) (r : ℕ) (hr : r ≤ l.length) :
    (l.take r).sum ≤ (l.reverse.take r).sum := by
  have h1 : l.reverse.take r = (l.drop (l.length - r)).reverse := by
    rw [List.take_reverse]
  rw [h1, List.sum_reverse]
  have hlen : (l.take r).length = (l.drop (l.length - r)).length := by
    simp; omega
  refine List.Forall₂.sum_le_sum ?_
  rw [List.forall₂_iff_get]
  refine ⟨hlen, fun i h1 h2 => ?_⟩
  simp only [List.get_eq_getElem, List.getElem_take, List.getElem_drop]
  have hi : i < r := by simp at h1; exact h1.1
  have hi2 : i < l.length := by omega
  rcases Nat.eq_zero_or_pos (l.length - r) with h0 | h0
  · have : l.length - r + i = i := by omega
    simp only [this]
    exact le_rfl
  · exact List.pairwise_iff_getElem.mp hl i (l.length - r + i) hi2 (by omega) (by omega)

lemma sorted_loads_len {A B : Type*} [Fintype B] (S : Finset A) (f : A → B) :
    (sortedLoads S f).length = Fintype.card B := by
  unfold sortedLoads
  rw [Multiset.length_sort]; simp

lemma sorted_loads_pw {A B : Type*} [Fintype B] (S : Finset A) (f : A → B) :
    (sortedLoads S f).Pairwise (· ≤ ·) := by
  unfold sortedLoads
  exact Multiset.pairwise_sort _ _

lemma light_le_heavy {A B : Type*} [Fintype B] (S : Finset A) (f : A → B) (r : ℕ)
    (hr : r ≤ Fintype.card B) : lightestAverage S f r ≤ heaviestAverage S f r := by
  unfold lightestAverage heaviestAverage
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast take_le_reverse_take _ (sorted_loads_pw S f) r (by rw [sorted_loads_len]; exact hr)

lemma light_nonneg {A B : Type*} [Fintype B] (S : Finset A) (f : A → B) (r : ℕ) :
    0 ≤ lightestAverage S f r := by
  unfold lightestAverage
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma avgLin_mono (K E : Type*) [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]
    (r : ℕ) (X Y : (E →ₗ[K] (Fin r → K)) → ℝ) (h : ∀ x, X x ≤ Y x) :
    LinMaxLoad.avgLin K E r X ≤ LinMaxLoad.avgLin K E r Y := by
  unfold LinMaxLoad.avgLin
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (Nat.cast_nonneg _)

lemma avgLin_nonneg (K E : Type*) [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]
    (r : ℕ) (X : (E →ₗ[K] (Fin r → K)) → ℝ) (h : ∀ x, 0 ≤ X x) :
    0 ≤ LinMaxLoad.avgLin K E r X := by
  unfold LinMaxLoad.avgLin
  exact div_nonneg (Finset.sum_nonneg fun x _ => h x) (Nat.cast_nonneg _)

/-! Analytic part -/

lemma vv_log (mu : ℝ) (n r : ℕ) (hmu : 0 < mu) (t : ℝ) (ht : 0 < t)
    (hD : poissonDivergence t mu = Real.log ((n : ℝ) / (r : ℝ))) (hne : t ≠ mu) :
    variationalValue mu n r (Real.log (t / mu)) = t := by
  have hl : Real.log (t / mu) ≠ 0 := by
    intro h
    rcases Real.log_eq_zero.mp h with h | h | h
    · exact absurd (div_eq_zero_iff.mp h |>.elim (fun h => by linarith) (fun h => by linarith)) id
    · exact hne (by field_simp at h; linarith)
    · have : t / mu > 0 := by positivity
      linarith
  unfold variationalValue
  rw [← hD, Real.exp_log (by positivity)]
  unfold poissonDivergence
  field_simp
  ring

lemma vv_le_mu (mu : ℝ) (n r : ℕ) (hmu : 0 ≤ mu) (hL : 0 ≤ Real.log ((n : ℝ) / (r : ℝ)))
    (lam : ℝ) (hlam : lam < 0) : variationalValue mu n r lam ≤ mu := by
  unfold variationalValue
  rw [div_le_iff_of_neg hlam]
  have := Real.add_one_le_exp lam
  nlinarith

lemma vv_lower_zero (mu : ℝ) (n r : ℕ) (hmu : 0 < mu) (hL : Real.log ((n : ℝ) / (r : ℝ)) = 0)
    (eps : ℝ) (heps : 0 < eps) : ∃ lam : ℝ, lam < 0 ∧ mu - eps < variationalValue mu n r lam := by
  have h := (Real.hasDerivAt_exp 0).tendsto_slope_zero_left
  have h2 := (h.eventually (lt_mem_nhds (show (1 : ℝ) - eps / mu < Real.exp 0 by
    have : 0 < eps / mu := by positivity
    rw [Real.exp_zero]; linarith)))
  obtain ⟨a, ha⟩ := (h2.and self_mem_nhdsWithin).exists
  refine ⟨a, ha.2, ?_⟩
  have ha1 := ha.1
  simp only [zero_add, Real.exp_zero, smul_eq_mul] at ha1
  unfold variationalValue
  rw [hL, add_zero]
  have : mu * (Real.exp a - 1) / a = mu * (a⁻¹ * (Real.exp a - 1)) := by ring
  rw [this]
  have h3 : (1 - eps / mu) * mu < a⁻¹ * (Real.exp a - 1) * mu := by
    exact mul_lt_mul_of_pos_right ha1 hmu
  have : (1 - eps / mu) * mu = mu - eps := by field_simp
  nlinarith

lemma vv_upper_zero (mu : ℝ) (n r : ℕ) (hmu : 0 < mu) (hL : Real.log ((n : ℝ) / (r : ℝ)) = 0)
    (eps : ℝ) (heps : 0 < eps) : ∃ lam : ℝ, 0 < lam ∧ variationalValue mu n r lam < mu + eps := by
  have h := (Real.hasDerivAt_exp 0).tendsto_slope_zero_right
  have h2 := (h.eventually (gt_mem_nhds (show Real.exp 0 < (1 : ℝ) + eps / mu by
    have : 0 < eps / mu := by positivity
    rw [Real.exp_zero]; linarith)))
  obtain ⟨a, ha⟩ := (h2.and self_mem_nhdsWithin).exists
  refine ⟨a, ha.2, ?_⟩
  have ha1 := ha.1
  simp only [zero_add, Real.exp_zero, smul_eq_mul] at ha1
  unfold variationalValue
  rw [hL, add_zero]
  have : mu * (Real.exp a - 1) / a = mu * (a⁻¹ * (Real.exp a - 1)) := by ring
  rw [this]
  have h3 : a⁻¹ * (Real.exp a - 1) * mu < (1 + eps / mu) * mu :=
    mul_lt_mul_of_pos_right ha1 hmu
  have : (1 + eps / mu) * mu = mu + eps := by field_simp
  nlinarith

lemma root_le_lower (mu : ℝ) (n r : ℕ) (hmu : 0 < mu) (hL : 0 ≤ Real.log ((n : ℝ) / (r : ℝ)))
    (t : ℝ) (ht0 : 0 < t) (htm : t ≤ mu)
    (hD : poissonDivergence t mu = Real.log ((n : ℝ) / (r : ℝ))) :
    t ≤ variationalLower mu n r := by
  have hbdd : BddAbove {z : ℝ | ∃ lam : ℝ, lam < 0 ∧ z = variationalValue mu n r lam} :=
    ⟨mu, by rintro z ⟨lam, hl, rfl⟩; exact vv_le_mu mu n r hmu.le hL lam hl⟩
  unfold variationalLower
  rcases htm.lt_or_eq with hlt | heq
  · have := vv_log mu n r hmu t ht0 hD hlt.ne
    have hneg : Real.log (t / mu) < 0 := Real.log_neg (by positivity) ((div_lt_one hmu).mpr hlt)
    rw [← this]
    exact le_csSup hbdd ⟨_, hneg, rfl⟩
  · subst heq
    have hL0 : Real.log ((n : ℝ) / (r : ℝ)) = 0 := by
      rw [← hD]; unfold poissonDivergence; simp
    by_contra hcon
    push Not at hcon
    obtain ⟨lam, hlam, hv⟩ := vv_lower_zero t n r hmu hL0 (t - sSup _) (by linarith)
    have := le_csSup hbdd ⟨lam, hlam, rfl⟩
    linarith

lemma root_ge_upper (mu : ℝ) (n r : ℕ) (hmu : 0 < mu) (hL : 0 ≤ Real.log ((n : ℝ) / (r : ℝ)))
    (t : ℝ) (htm : mu ≤ t)
    (hD : poissonDivergence t mu = Real.log ((n : ℝ) / (r : ℝ))) :
    variationalUpper mu n r ≤ t := by
  have hbdd : BddBelow {z : ℝ | ∃ lam : ℝ, 0 < lam ∧ z = variationalValue mu n r lam} := by
    refine ⟨0, ?_⟩
    rintro z ⟨lam, hl, rfl⟩
    unfold variationalValue
    apply div_nonneg _ hl.le
    have := Real.add_one_le_exp lam
    nlinarith
  unfold variationalUpper
  rcases htm.lt_or_eq with hlt | heq
  · have ht0 : 0 < t := by linarith
    have := vv_log mu n r hmu t ht0 hD hlt.ne'
    have hpos : 0 < Real.log (t / mu) := Real.log_pos ((one_lt_div hmu).mpr hlt)
    rw [← this]
    exact csInf_le hbdd ⟨_, hpos, rfl⟩
  · subst heq
    have hL0 : Real.log ((n : ℝ) / (r : ℝ)) = 0 := by
      rw [← hD]; unfold poissonDivergence; simp
    by_contra hcon
    push Not at hcon
    obtain ⟨lam, hlam, hv⟩ := vv_upper_zero mu n r hmu hL0 (sInf _ - mu) (by linarith)
    have := csInf_le hbdd ⟨lam, hlam, rfl⟩
    linarith

lemma pd_continuous (mu : ℝ) (hm : mu ≠ 0) : Continuous (fun t => poissonDivergence t mu) := by
  have h := Real.continuous_mul_log
  have : (fun t => poissonDivergence t mu) =
      fun t => (t * Real.log t) - t * Real.log mu - t + mu := by
    funext t
    unfold poissonDivergence
    rcases eq_or_ne t 0 with rfl | ht
    · simp
    rw [Real.log_div ht hm]; ring
  rw [this]
  fun_prop

lemma lower_root_exists (mu L : ℝ) (hmu : 0 < mu) (hL : 0 ≤ L) (hlt : L < mu) :
    ∃ t, 0 < t ∧ t ≤ mu ∧ poissonDivergence t mu = L := by
  have hc := (pd_continuous mu hmu.ne').continuousOn (s := Set.Icc 0 mu)
  have h0 : poissonDivergence 0 mu = mu := by simp [poissonDivergence]
  have h1 : poissonDivergence mu mu = 0 := by simp [poissonDivergence, div_self hmu.ne']
  obtain ⟨t, ht, htL⟩ := intermediate_value_Icc' hmu.le hc
    (show L ∈ Set.Icc (poissonDivergence mu mu) (poissonDivergence 0 mu) from
      ⟨by rw [h1]; exact hL, by rw [h0]; linarith⟩)
  simp only at htL
  refine ⟨t, ?_, ht.2, htL⟩
  rcases ht.1.eq_or_lt with h | h
  · subst h; rw [h0] at htL; linarith
  · exact h

lemma upper_root_exists (mu L : ℝ) (hmu : 0 < mu) (hL : 0 ≤ L) :
    ∃ t, mu ≤ t ∧ poissonDivergence t mu = L := by
  set t0 := mu * Real.exp (1 + L / mu) with ht0
  have hmt : mu ≤ t0 := by
    have : 1 ≤ Real.exp (1 + L / mu) := Real.one_le_exp (by positivity)
    nlinarith
  have hD : poissonDivergence t0 mu = t0 * (L / mu) + mu := by
    unfold poissonDivergence
    rw [ht0, mul_div_cancel_left₀ _ hmu.ne', Real.log_exp]; ring
  have hge : L ≤ poissonDivergence t0 mu := by
    rw [hD]
    have : t0 * (L / mu) ≥ mu * (L / mu) := mul_le_mul_of_nonneg_right hmt (by positivity)
    have : mu * (L / mu) = L := by field_simp
    linarith
  have hc := (pd_continuous mu hmu.ne').continuousOn (s := Set.Icc mu t0)
  have h1 : poissonDivergence mu mu = 0 := by simp [poissonDivergence, div_self hmu.ne']
  obtain ⟨t, ht, htL⟩ := intermediate_value_Icc hmt hc
    (show L ∈ Set.Icc (poissonDivergence mu mu) (poissonDivergence t0 mu) from
      ⟨by rw [h1]; exact hL, hge⟩)
  simp only at htL
  exact ⟨t, ht.1, htL⟩

end LinearHashingPoissonesque.Dev.PoissonApprox

namespace LinearHashingPoissonesque.ExpectedLoads
open LinearHashingPoissonesque.Dev.PoissonApprox in
theorem chk_poisson_approximation_expectation {u ell m : ℕ} (hu : ell ≤ u) (hell : 1 ≤ ell) (hm : 1 ≤ m)
    (S : Finset (Fin u → ZMod 2)) (hS : S.card = m)
    (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ 2 ^ ell) :
    lowerThreshold (m : ℝ) (2 ^ ell) r ≤
      LinMaxLoad.avgLin (ZMod 2) (Fin u → ZMod 2) ell
        (fun h => lightestAverage S h r) ∧
    LinMaxLoad.avgLin (ZMod 2) (Fin u → ZMod 2) ell
        (fun h => lightestAverage S h r) ≤
      LinMaxLoad.avgLin (ZMod 2) (Fin u → ZMod 2) ell
        (fun h => heaviestAverage S h r) ∧
    LinMaxLoad.avgLin (ZMod 2) (Fin u → ZMod 2) ell
        (fun h => heaviestAverage S h r) ≤ upperThreshold (m : ℝ) (2 ^ ell) r := by
  have hcard : ∀ h : (Fin u → ZMod 2) →ₗ[ZMod 2] (Fin ell → ZMod 2), r ≤ Fintype.card (Fin ell → ZMod 2) := by
    intro h; simpa [Fintype.card_fun, ZMod.card] using hrn
  have hcast : (((2 ^ ell : ℕ)) : ℝ) = (2 : ℝ) ^ ell := by push_cast; rfl
  have hmu : 0 < (m : ℝ) / ((2 ^ ell : ℕ) : ℝ) := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hnr : (r : ℝ) ≤ ((2 ^ ell : ℕ) : ℝ) := by exact_mod_cast hrn
  have hL : 0 ≤ Real.log (((2 ^ ell : ℕ) : ℝ) / (r : ℝ)) :=
    Real.log_nonneg ((one_le_div (by linarith)).mpr hnr)
  have hVL := (variational_expectation hu hell hm S hS r hr hrn .lightest).1
  have hVU := (variational_expectation hu hell hm S hS r hr hrn .heaviest).2
  simp only [extremeAverage] at hVL hVU
  rw [← hcast] at hVL hVU
  refine ⟨?_, ?_, ?_⟩
  · unfold lowerThreshold
    split_ifs with hc
    · exact avgLin_nonneg _ _ _ _ fun h => light_nonneg S h r
    · push Not at hc
      obtain ⟨t, ht0, htm, htD⟩ := lower_root_exists _ _ hmu hL hc
      refine le_trans ?_ (le_trans (root_le_lower _ _ _ hmu hL t ht0 htm htD) hVL)
      exact csInf_le ⟨0, by rintro s ⟨hs, -⟩; exact hs.le⟩ ⟨ht0, htm, htD⟩
  · exact avgLin_mono _ _ _ _ _ fun h => light_le_heavy S h r (hcard h)
  · obtain ⟨t, htm, htD⟩ := upper_root_exists _ _ hmu hL
    refine le_trans hVU (le_csInf ⟨t, htm, htD⟩ ?_)
    rintro s ⟨hs, hsD⟩
    exact root_ge_upper _ _ _ hmu hL s hs hsD

end LinearHashingPoissonesque.ExpectedLoads
end

theorem solution : type_of% @LinearHashingPoissonesque.ExpectedLoads.chk_poisson_approximation_expectation := @LinearHashingPoissonesque.ExpectedLoads.chk_poisson_approximation_expectation
