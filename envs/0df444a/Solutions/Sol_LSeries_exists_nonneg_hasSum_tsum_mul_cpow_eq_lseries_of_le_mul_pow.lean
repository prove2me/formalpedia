-- Prove2me | solution 1 for LSeries.exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/c4ff3c9d-ba33-5bbd-89d0-15987e1ee1ca

import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LSeries_exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow

set_option autoImplicit false

open scoped ComplexOrder

namespace PPSeries43

open Complex

variable {ι : Type*} (N : ι → ℕ) (hN : ∀ i : ι, (N i).Prime) (hinj : Function.Injective N)

include hN hinj in

theorem key_inj {q q' : ι × ℕ} (hq : 0 < q.2) (_hq' : 0 < q'.2) (h : N q.1 ^ q.2 = N q'.1 ^ q'.2) :
    q = q' := by
  have hp := hN q.1
  have hp' := hN q'.1
  have h1 : N q.1 = N q'.1 := by
    have hd : N q.1 ∣ N q'.1 ^ q'.2 := by
      rw [← h]; exact dvd_pow_self _ hq.ne'
    exact (Nat.prime_dvd_prime_iff_eq hp hp').mp (hp.dvd_of_dvd_pow hd)
  have hm : q.2 = q'.2 := by
    rw [h1] at h
    exact Nat.pow_right_injective hp'.two_le h
  exact Prod.ext (hinj h1) hm

include hN hinj in
theorem main
    (c : ι → ℕ → ℝ) (hc0 : ∀ i : ι, c i 0 = 0) (hc : ∀ (i : ι) (m : ℕ), 0 ≤ c i m)
    (B : ℝ) (hcB : ∀ (i : ι) (m : ℕ), c i m ≤ B * (N i : ℝ) ^ m) :
    ∃ d : ℕ → ℝ, (∀ n : ℕ, 0 ≤ d n) ∧
      (∀ (i : ι) (m : ℕ), 0 < m → d (N i ^ m) = c i m) ∧
      (∀ n : ℕ, d n ≠ 0 → ∃ (i : ι) (m : ℕ), 0 < m ∧ N i ^ m = n) ∧
      LSeries.abscissaOfAbsConv (fun n => (d n : ℂ)) ≤ ((2 : ℝ) : EReal) ∧
      (∀ s : ℂ, 2 < s.re →
        (∀ i : ι, Summable (fun m : ℕ => (c i m : ℂ) * (((N i : ℕ) : ℂ) ^ (-s)) ^ m)) ∧
        HasSum (fun i : ι => ∑' m : ℕ, (c i m : ℂ) * (((N i : ℕ) : ℂ) ^ (-s)) ^ m)
          (LSeries (fun n => (d n : ℂ)) s)) ∧
      ∀ σ : ℝ, LSeriesSummable (fun n => (d n : ℂ)) σ →
        Summable (fun i : ι => c i 1 * (N i : ℝ) ^ (-σ)) ∧
        ∑' i : ι, c i 1 * (N i : ℝ) ^ (-σ) ≤ (LSeries (fun n => (d n : ℂ)) σ).re := by
  classical

  let P : ℕ → Prop := fun n => ∃ q : ι × ℕ, 0 < q.2 ∧ N q.1 ^ q.2 = n
  let d : ℕ → ℝ := fun n => if h : P n then c h.choose.1 h.choose.2 else 0
  have hNpos : ∀ i, 0 < N i := fun i => (hN i).pos
  have hNR : ∀ i, (1 : ℝ) < (N i : ℝ) := fun i => by exact_mod_cast (hN i).one_lt
  have hd_pow : ∀ (i : ι) (m : ℕ), 0 < m → d (N i ^ m) = c i m := by
    intro i m hm
    have h : P (N i ^ m) := ⟨(i, m), hm, rfl⟩
    have hq : h.choose = (i, m) := key_inj N hN hinj h.choose_spec.1 hm h.choose_spec.2
    show (if h : P (N i ^ m) then c h.choose.1 h.choose.2 else 0) = c i m
    rw [dif_pos h, hq]
  have hd_nonneg : ∀ n, 0 ≤ d n := by
    intro n
    show 0 ≤ (if h : P n then c h.choose.1 h.choose.2 else 0)
    split_ifs with h
    · exact hc _ _
    · exact le_rfl
  have hd_P : ∀ n, d n ≠ 0 → P n := by
    intro n hn
    by_contra hP
    exact hn (dif_neg hP)
  have hd_notP : ∀ n, ¬ P n → d n = 0 := fun n hP => dif_neg hP
  have hd0 : d 0 = 0 := hd_notP 0 (by
    rintro ⟨q, -, hq⟩
    exact pow_ne_zero _ (hN q.1).ne_zero hq)
  have hd0C : (fun n => (d n : ℂ)) 0 = 0 := by simp [hd0]
  have hB : ∀ n, d n ≤ max B 0 * n := by
    intro n
    by_cases h : P n
    · obtain ⟨q, hq, hqn⟩ := h
      rw [← hqn, hd_pow q.1 q.2 hq]
      calc c q.1 q.2 ≤ B * (N q.1 : ℝ) ^ q.2 := hcB _ _
        _ ≤ max B 0 * (N q.1 : ℝ) ^ q.2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ = max B 0 * ((N q.1 ^ q.2 : ℕ) : ℝ) := by push_cast; ring
    · rw [hd_notP n h]; positivity
  have hbound : ∃ C : ℝ, ∀ n : ℕ, n ≠ 0 → ‖((d n : ℝ) : ℂ)‖ ≤ C * (n : ℝ) ^ ((2 : ℝ) - 1) := by
    refine ⟨max B 0, fun n _ => ?_⟩
    rw [Complex.norm_real, Real.norm_of_nonneg (hd_nonneg n), show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    exact hB n
  have hsummable : ∀ s : ℂ, 2 < s.re → LSeriesSummable (fun n => (d n : ℂ)) s :=
    fun s hs => LSeriesSummable_of_le_const_mul_rpow hs hbound
  refine ⟨d, hd_nonneg, hd_pow, fun n hn => ?_, ?_, fun s hs => ?_, fun σ hσ => ?_⟩
  · obtain ⟨q, hq, hqn⟩ := hd_P n hn
    exact ⟨q.1, q.2, hq, hqn⟩
  · exact LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      hsummable y (by simpa using hy)
  ·
    set σ : ℝ := s.re with hσdef
    let F : ι × ℕ → ℂ := fun q => (c q.1 q.2 : ℂ) * (((N q.1 : ℕ) : ℂ) ^ (-s)) ^ q.2

    have hinner : ∀ i : ι, Summable (fun m : ℕ => F (i, m)) := by
      intro i
      have hp : (0 : ℝ) < N i := by exact_mod_cast hNpos i
      set r : ℝ := (N i : ℝ) ^ (1 - σ) with hr
      have hr0 : 0 ≤ r := Real.rpow_nonneg hp.le _
      have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (hNR i) (by linarith)
      refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr1).mul_left (max B 0)) fun m => ?_
      have hnorm : ‖F (i, m)‖ = c i m * ((N i : ℝ) ^ (-σ)) ^ m := by
        show ‖(c i m : ℂ) * (((N i : ℕ) : ℂ) ^ (-s)) ^ m‖ = _
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hc i m),
          Complex.norm_natCast_cpow_of_pos (hNpos i), Complex.neg_re]
      rw [hnorm]
      have hre : (N i : ℝ) ^ m * ((N i : ℝ) ^ (-σ)) ^ m = r ^ m := by
        rw [← mul_pow, hr, show (1 : ℝ) - σ = 1 + -σ by ring, Real.rpow_add hp, Real.rpow_one]
      calc c i m * ((N i : ℝ) ^ (-σ)) ^ m ≤ (B * (N i : ℝ) ^ m) * ((N i : ℝ) ^ (-σ)) ^ m :=
            mul_le_mul_of_nonneg_right (hcB i m) (by positivity)
        _ ≤ (max B 0 * (N i : ℝ) ^ m) * ((N i : ℝ) ^ (-σ)) ^ m :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
              (by positivity)
        _ = max B 0 * r ^ m := by rw [mul_assoc, hre]
    refine ⟨hinner, ?_⟩

    let T : Set (ι × ℕ) := {q | 0 < q.2}
    let eT : T → ℕ := fun q => N q.1.1 ^ q.1.2
    have heT : Function.Injective eT := by
      intro q q' h
      exact Subtype.ext (key_inj N hN hinj q.2 q'.2 h)
    have hrange : ∀ n : ℕ, n ∉ Set.range eT → LSeries.term (fun n => (d n : ℂ)) s n = 0 := by
      intro n hn
      have hP : ¬ P n := by
        rintro ⟨q, hq, hqn⟩
        exact hn ⟨⟨q, hq⟩, hqn⟩
      rw [LSeries.term_def₀ hd0C, hd_notP n hP]
      simp
    have h1 : HasSum (LSeries.term (fun n => (d n : ℂ)) s) (LSeries (fun n => (d n : ℂ)) s) :=
      (hsummable s hs).LSeriesHasSum
    have h2 : HasSum (LSeries.term (fun n => (d n : ℂ)) s ∘ eT) (LSeries (fun n => (d n : ℂ)) s) :=
      (heT.hasSum_iff hrange).mpr h1
    have hterm : ∀ q : T, LSeries.term (fun n => (d n : ℂ)) s (eT q) = F q.1 := by
      intro q
      rw [LSeries.term_def₀ hd0C]
      show ((d (N q.1.1 ^ q.1.2) : ℝ) : ℂ) * (((N q.1.1 ^ q.1.2 : ℕ) : ℂ)) ^ (-s) =
        (c q.1.1 q.1.2 : ℂ) * (((N q.1.1 : ℕ) : ℂ) ^ (-s)) ^ q.1.2
      rw [hd_pow _ _ q.2, Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
    have h3 : HasSum (F ∘ (↑) : T → ℂ) (LSeries (fun n => (d n : ℂ)) s) := by
      have hfun : (LSeries.term (fun n => (d n : ℂ)) s ∘ eT) = (F ∘ (↑) : T → ℂ) := funext hterm
      rw [← hfun]; exact h2
    have hsupp : Function.support F ⊆ T := by
      intro q hq
      by_contra hq0
      apply hq
      have h0 : q.2 = 0 := Nat.eq_zero_of_not_pos hq0
      show (c q.1 q.2 : ℂ) * (((N q.1 : ℕ) : ℂ) ^ (-s)) ^ q.2 = 0
      rw [h0, hc0]; simp
    have h4 : HasSum F (LSeries (fun n => (d n : ℂ)) s) :=
      (hasSum_subtype_iff_of_support_subset hsupp).mp h3
    exact h4.prod_fiberwise fun i => (hinner i).hasSum
  ·
    let g : ℕ → ℝ := fun n => d n * (n : ℝ) ^ (-σ)
    have hg0 : ∀ n, 0 ≤ g n := fun n => mul_nonneg (hd_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have hterm : ∀ n, LSeries.term (fun n => (d n : ℂ)) (σ : ℂ) n = ((g n : ℝ) : ℂ) := by
      intro n
      rw [LSeries.term_def₀ hd0C]
      show ((d n : ℝ) : ℂ) * ((n : ℕ) : ℂ) ^ (-(σ : ℂ)) = (((d n * (n : ℝ) ^ (-σ) : ℝ)) : ℂ)
      rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, Complex.ofReal_neg]
    have hre : ∀ n, (LSeries.term (fun n => (d n : ℂ)) (σ : ℂ) n).re = g n := fun n => by
      rw [hterm n, Complex.ofReal_re]
    have hg : Summable g := by
      have := Complex.hasSum_re hσ.LSeriesHasSum
      simp_rw [hre] at this
      exact this.summable
    have hgN : (fun i : ι => c i 1 * (N i : ℝ) ^ (-σ)) = g ∘ N := by
      funext i
      show c i 1 * (N i : ℝ) ^ (-σ) = d (N i) * ((N i : ℕ) : ℝ) ^ (-σ)
      rw [← pow_one (N i), hd_pow i 1 one_pos, pow_one]
    rw [hgN]
    refine ⟨hg.comp_injective hinj, ?_⟩
    calc ∑' i : ι, (g ∘ N) i ≤ ∑' n, g n := tsum_comp_le_tsum_of_inj hg hg0 hinj
      _ = ∑' n, (LSeries.term (fun n => (d n : ℂ)) (σ : ℂ) n).re := by simp_rw [hre]
      _ = (LSeries (fun n => (d n : ℂ)) σ).re := (Complex.re_tsum hσ).symm

end PPSeries43

theorem solution
    {ι : Type*} (N : ι → ℕ) (hN : ∀ i : ι, (N i).Prime) (hinj : Function.Injective N)
    (c : ι → ℕ → ℝ) (hc0 : ∀ i : ι, c i 0 = 0) (hc : ∀ (i : ι) (m : ℕ), 0 ≤ c i m)
    (B : ℝ) (hcB : ∀ (i : ι) (m : ℕ), c i m ≤ B * (N i : ℝ) ^ m) :
    ∃ d : ℕ → ℝ, (∀ n : ℕ, 0 ≤ d n) ∧
      (∀ (i : ι) (m : ℕ), 0 < m → d (N i ^ m) = c i m) ∧
      (∀ n : ℕ, d n ≠ 0 → ∃ (i : ι) (m : ℕ), 0 < m ∧ N i ^ m = n) ∧
      LSeries.abscissaOfAbsConv (fun n => (d n : ℂ)) ≤ ((2 : ℝ) : EReal) ∧
      (∀ s : ℂ, 2 < s.re →
        (∀ i : ι, Summable (fun m : ℕ => (c i m : ℂ) * (((N i : ℕ) : ℂ) ^ (-s)) ^ m)) ∧
        HasSum (fun i : ι => ∑' m : ℕ, (c i m : ℂ) * (((N i : ℕ) : ℂ) ^ (-s)) ^ m)
          (LSeries (fun n => (d n : ℂ)) s)) ∧
      ∀ σ : ℝ, LSeriesSummable (fun n => (d n : ℂ)) σ →
        Summable (fun i : ι => c i 1 * (N i : ℝ) ^ (-σ)) ∧
        ∑' i : ι, c i 1 * (N i : ℝ) ^ (-σ) ≤ (LSeries (fun n => (d n : ℂ)) σ).re :=
  PPSeries43.main N hN hinj c hc0 hc B hcB

end S_LSeries_exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow
end P2MW
export P2MW.S_LSeries_exists_nonneg_hasSum_tsum_mul_cpow_eq_lseries_of_le_mul_pow (solution)
