-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/0ef51111-3277-5f05-85ef-55da181bf4ea

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow

set_option autoImplicit false

namespace ExpLogSumSelection

open Filter Topology Complex Finset

theorem exp_ofReal_mul_I_ne_one {θ : ℝ} (h0 : θ ≠ 0) (hπ : |θ| < Real.pi) :
    Complex.exp (θ * I) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  have him : θ = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  have habs : |(n : ℝ)| * (2 * Real.pi) < Real.pi := by
    have := hπ
    rw [him, abs_mul, abs_of_pos Real.two_pi_pos] at this
    exact this
  have hn1 : |(n : ℝ)| < 1 := by nlinarith [Real.pi_pos, abs_nonneg (n : ℝ)]
  have hn0 : n = 0 := by
    have : |n| < 1 := by exact_mod_cast hn1
    rw [abs_lt] at this
    omega
  apply h0
  rw [him, hn0]
  simp

theorem trigSum_coeff_eq_zero_of_tendsto_zero {κ : Type*} (t : κ → ℝ) :
    ∀ (s : Finset κ) (a : κ → ℂ), Set.InjOn t s →
      Tendsto (fun u : ℝ => ∑ k ∈ s, a k * cexp (t k * u * I)) atTop (𝓝 0) →
      ∀ k ∈ s, a k = 0 := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro a _ _ k hk; simp at hk
  | insert k₀ s hk₀ ih =>
    intro a hinj hP k hk

    set D : ℝ := 1 + ∑ k ∈ s, |t k - t k₀| with hD
    have hDpos : 0 < D := by
      have := Finset.sum_nonneg (fun k (_ : k ∈ s) => abs_nonneg (t k - t k₀)); linarith
    set h : ℝ := Real.pi / D with hh
    have hhpos : 0 < h := div_pos Real.pi_pos hDpos

    have hne : ∀ k ∈ s, cexp (t k * h * I) - cexp (t k₀ * h * I) ≠ 0 := by
      intro k hk
      rw [sub_ne_zero]
      intro heq
      have hkk : t k ≠ t k₀ := by
        intro h'
        have := hinj (mem_insert_of_mem hk) (mem_insert_self _ _) h'
        exact hk₀ (this ▸ hk)
      have h1 : cexp ((((t k - t k₀) * h : ℝ) : ℂ) * I) = 1 := by
        rw [show (((t k - t k₀) * h : ℝ) : ℂ) * I = t k * h * I - t k₀ * h * I by push_cast; ring,
          Complex.exp_sub, heq, div_self (Complex.exp_ne_zero _)]
      refine exp_ofReal_mul_I_ne_one ?_ ?_ h1
      · exact mul_ne_zero (sub_ne_zero.2 hkk) hhpos.ne'
      · rw [abs_mul, abs_of_pos hhpos, hh]
        have hle : |t k - t k₀| ≤ ∑ k ∈ s, |t k - t k₀| :=
          Finset.single_le_sum (f := fun k => |t k - t k₀|) (fun _ _ => abs_nonneg _) hk
        have hlt : |t k - t k₀| / D < 1 := by rw [div_lt_one hDpos]; linarith
        calc |t k - t k₀| * (Real.pi / D) = (|t k - t k₀| / D) * Real.pi := by ring
          _ < 1 * Real.pi := by gcongr
          _ = Real.pi := one_mul _

    set a' : κ → ℂ := fun k => a k * (cexp (t k * h * I) - cexp (t k₀ * h * I)) with ha'
    have hQ : Tendsto (fun u : ℝ => ∑ k ∈ s, a' k * cexp (t k * u * I)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun u : ℝ => ∑ k ∈ insert k₀ s, a k * cexp (t k * (u + h) * I))
          atTop (𝓝 0) := by
        have := hP.comp (tendsto_atTop_add_const_right _ h tendsto_id)
        refine this.congr fun u => ?_
        simp only [Function.comp, id]
        push_cast
        rfl
      have h2 : Tendsto (fun u : ℝ => cexp (t k₀ * h * I) *
          ∑ k ∈ insert k₀ s, a k * cexp (t k * u * I)) atTop (𝓝 0) := by
        simpa using hP.const_mul (cexp (t k₀ * h * I))
      have h3 := h1.sub h2
      rw [sub_zero] at h3
      refine h3.congr fun u => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_insert hk₀]
      have hz : a k₀ * cexp (t k₀ * (u + h) * I) -
          cexp (t k₀ * h * I) * (a k₀ * cexp (t k₀ * u * I)) = 0 := by
        rw [show (t k₀ : ℂ) * ((u : ℂ) + (h : ℂ)) * I = t k₀ * u * I + t k₀ * h * I by ring,
          Complex.exp_add]
        ring
      rw [hz, zero_add]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show (t k : ℂ) * ((u : ℂ) + (h : ℂ)) * I = t k * u * I + t k * h * I by ring,
        Complex.exp_add]
      simp only [ha']
      ring
    have hzero : ∀ k ∈ s, a k = 0 := by
      intro k hk
      have := ih a' (hinj.mono (coe_subset.2 (subset_insert _ _))) hQ k hk
      exact (mul_eq_zero.1 this).resolve_right (hne k hk)
    rcases Finset.mem_insert.1 hk with rfl | hk'
    · have hP' : Tendsto (fun u : ℝ => a k * cexp (t k * u * I)) atTop (𝓝 0) := by
        refine hP.congr fun u => ?_
        rw [Finset.sum_insert hk₀,
          Finset.sum_eq_zero (fun i hi => by rw [hzero i hi, zero_mul]), add_zero]
      have hn : Tendsto (fun u : ℝ => ‖a k * cexp (t k * u * I)‖) atTop (𝓝 ‖a k‖) := by
        refine tendsto_const_nhds.congr fun u => ?_
        rw [norm_mul, show (t k : ℂ) * (u : ℂ) * I = ((t k * u : ℝ) : ℂ) * I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
      have := tendsto_nhds_unique hn hP'.norm
      simpa using this
    · exact hzero k hk'

theorem norm_neg_ofReal_pow {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : ‖(-(u : ℂ)) ^ n‖ = u ^ n := by
  rw [norm_pow, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]

theorem expPolySum_coeff_eq_zero_of_re_lt {ι : Type*} [Fintype ι] (e : ι → ℂ) (j : ι → ℕ)
    (c : ι → ℂ)
    (hinj : Function.Injective fun i => (e i, j i)) (θ₀ M : ℝ)
    (hg : ∀ u : ℝ, 0 ≤ u →
      ‖∑ i, c i * (cexp (-(u * e i)) * (-(u : ℂ)) ^ j i)‖ ≤ M * Real.exp (-(θ₀ * u))) :
    ∀ i, (e i).re < θ₀ → c i = 0 := by
  classical
  intro i₀ hi₀
  by_contra hci₀

  set S : Finset ι := univ.filter fun i => c i ≠ 0 with hS
  have memS : ∀ i, i ∈ S ↔ c i ≠ 0 := fun i => by simp [hS]
  have hi₀S : i₀ ∈ S := (memS i₀).2 hci₀
  have hSne : S.Nonempty := ⟨i₀, hi₀S⟩
  set σ : ℝ := S.inf' hSne fun i => (e i).re with hσ
  have hσle : ∀ i ∈ S, σ ≤ (e i).re := fun i hi => Finset.inf'_le (fun i => (e i).re) hi
  have hσlt : σ < θ₀ := (hσle i₀ hi₀S).trans_lt hi₀
  set S₁ : Finset ι := S.filter fun i => (e i).re = σ with hS₁
  have memS₁ : ∀ i, i ∈ S₁ ↔ c i ≠ 0 ∧ (e i).re = σ := fun i => by simp [hS₁, memS]
  have hS₁ne : S₁.Nonempty := by
    obtain ⟨i, hi, h⟩ := Finset.exists_mem_eq_inf' hSne fun i => (e i).re
    exact ⟨i, (memS₁ i).2 ⟨(memS i).1 hi, h.symm⟩⟩
  set J : ℕ := S₁.sup' hS₁ne j with hJ
  have hJle : ∀ i ∈ S₁, j i ≤ J := fun i hi => Finset.le_sup' j hi
  set S₂ : Finset ι := S₁.filter fun i => j i = J with hS₂
  have memS₂ : ∀ i, i ∈ S₂ ↔ c i ≠ 0 ∧ (e i).re = σ ∧ j i = J := fun i => by
    simp [hS₂, memS₁, and_assoc]
  have hS₂ne : S₂.Nonempty := by
    obtain ⟨i, hi, h⟩ := Finset.exists_mem_eq_sup' hS₁ne j
    exact ⟨i, (memS₂ i).2 ⟨((memS₁ i).1 hi).1, ((memS₁ i).1 hi).2, h.symm⟩⟩

  have hM : 0 ≤ M := by
    have := hg 0 le_rfl
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at this
    exact (norm_nonneg _).trans this

  set T : ι → ℝ → ℂ := fun i u =>
    c i * (cexp (-(u * (e i - σ))) * ((-(u : ℂ)) ^ j i / (-(u : ℂ)) ^ J)) with hT
  have hident : ∀ u : ℝ,
      cexp (σ * u) / (-(u : ℂ)) ^ J * ∑ i, c i * (cexp (-(u * e i)) * (-(u : ℂ)) ^ j i) =
        ∑ i, T i u := by
    intro u
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hT]
    rw [show -((u : ℂ) * (e i - σ)) = σ * u + -(u * e i) by ring, Complex.exp_add]
    ring

  have hsum : Tendsto (fun u => ∑ i, T i u) atTop (𝓝 0) := by
    have hδ : 0 < θ₀ - σ := sub_pos.2 hσlt
    have hlim : Tendsto (fun u : ℝ => M * Real.exp (-((θ₀ - σ) * u))) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hδ)).const_mul M
      simpa using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have hu0 : 0 ≤ u := zero_le_one.trans hu
    rw [← hident, norm_mul, norm_div, Complex.norm_exp, norm_neg_ofReal_pow hu0]
    have hre : ((σ : ℂ) * (u : ℂ)).re = σ * u := by
      rw [← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hre]
    calc Real.exp (σ * u) / u ^ J * ‖∑ i, c i * (cexp (-(u * e i)) * (-(u : ℂ)) ^ j i)‖
        ≤ Real.exp (σ * u) * (M * Real.exp (-(θ₀ * u))) := by
          refine mul_le_mul (div_le_self (Real.exp_pos _).le (one_le_pow₀ hu)) (hg u hu0)
            (norm_nonneg _) (Real.exp_pos _).le
      _ = M * Real.exp (-((θ₀ - σ) * u)) := by
          rw [show -((θ₀ - σ) * u) = σ * u + -(θ₀ * u) by ring, Real.exp_add]; ring

  have hTlim : ∀ i, i ∉ S₂ → Tendsto (T i) atTop (𝓝 0) := by
    intro i hi
    by_cases hc : c i = 0
    · have : T i = fun _ => 0 := by funext u; simp [hT, hc]
      rw [this]; exact tendsto_const_nhds
    have hiS : i ∈ S := (memS i).2 hc

    have hnorm : ∀ u : ℝ, 1 ≤ u →
        ‖T i u‖ = ‖c i‖ * (Real.exp (-(((e i).re - σ) * u)) * (u ^ j i / u ^ J)) := by
      intro u hu
      have hu0 : 0 ≤ u := zero_le_one.trans hu
      simp only [hT]
      rw [norm_mul, norm_mul, norm_div, Complex.norm_exp, norm_neg_ofReal_pow hu0,
        norm_neg_ofReal_pow hu0]
      congr 2
      simp only [Complex.neg_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.ofReal_re]
      ring_nf
    rcases (hσle i hiS).lt_or_eq with hlt | heq
    ·
      have hδ : 0 < (e i).re - σ := sub_pos.2 hlt
      have hlim : Tendsto (fun u : ℝ => ‖c i‖ * (u ^ ((j i : ℕ) : ℝ) *
          Real.exp (-((e i).re - σ) * u))) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((j i : ℕ) : ℝ) _ hδ).const_mul
          ‖c i‖
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
      have hu0 : 0 ≤ u := zero_le_one.trans hu
      rw [hnorm u hu, Real.rpow_natCast]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [mul_comm (u ^ j i), neg_mul]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact div_le_self (pow_nonneg hu0 _) (one_le_pow₀ hu)
    ·
      have hiS₁ : i ∈ S₁ := (memS₁ i).2 ⟨hc, heq.symm⟩
      have hji : j i < J :=
        lt_of_le_of_ne (hJle i hiS₁) fun h => hi ((memS₂ i).2 ⟨hc, heq.symm, h⟩)
      have hlim : Tendsto (fun u : ℝ => ‖c i‖ * u⁻¹) atTop (𝓝 0) := by
        simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul ‖c i‖
      refine squeeze_zero_norm' ?_ hlim
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
      have hu0 : 0 < u := zero_lt_one.trans_le hu
      rw [hnorm u hu, ← heq, sub_self, zero_mul, neg_zero, Real.exp_zero, one_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hji
      rw [hd, show j i + d + 1 = j i + (d + 1) by ring, pow_add, div_mul_eq_div_div,
        div_self (pow_ne_zero _ hu0.ne'), one_div]
      exact inv_anti₀ hu0 (le_self_pow₀ hu (Nat.succ_ne_zero d))

  set t' : ι → ℝ := fun i => -(e i).im with ht'
  have hTS₂ : ∀ i ∈ S₂, ∀ u : ℝ, u ≠ 0 → T i u = c i * cexp (t' i * u * I) := by
    intro i hi u hu
    obtain ⟨-, hre, hjJ⟩ := (memS₂ i).1 hi
    simp only [hT, ht']
    rw [hjJ, div_self (pow_ne_zero _ (neg_ne_zero.2 (Complex.ofReal_ne_zero.2 hu))), mul_one]
    congr 2
    have hei : e i = σ + (e i).im * I := by
      rw [← hre]; exact (Complex.re_add_im (e i)).symm
    conv_lhs => rw [hei]
    push_cast
    ring
  have hP : Tendsto (fun u : ℝ => ∑ i ∈ S₂, c i * cexp (t' i * u * I)) atTop (𝓝 0) := by
    have hrest : Tendsto (fun u : ℝ => ∑ i ∈ univ.filter (fun i => i ∉ S₂), T i u) atTop (𝓝 0) := by
      have := tendsto_finsetSum (univ.filter fun i => i ∉ S₂)
        (fun i hi => hTlim i (by simpa using hi))
      simpa using this
    have h := hsum.sub hrest
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hsplit := Finset.sum_filter_add_sum_filter_not univ (fun i => i ∈ S₂) (fun i => T i u)
    have hfil : univ.filter (fun i => i ∈ S₂) = S₂ := by ext i; simp
    rw [hfil] at hsplit
    rw [← hsplit, add_sub_cancel_right]
    exact Finset.sum_congr rfl fun i hi => hTS₂ i hi u hu.ne'

  have hinjS₂ : Set.InjOn t' S₂ := by
    intro i hi i' hi' h
    obtain ⟨-, hre, hjJ⟩ := (memS₂ i).1 hi
    obtain ⟨-, hre', hjJ'⟩ := (memS₂ i').1 hi'
    have him : (e i).im = (e i').im := neg_injective h
    have hee : e i = e i' := Complex.ext (by rw [hre, hre']) him
    exact hinj (Prod.ext hee (by simp [hjJ, hjJ']))
  obtain ⟨i₁, hi₁⟩ := hS₂ne
  exact ((memS₂ i₁).1 hi₁).1 (trigSum_coeff_eq_zero_of_tendsto_zero t' S₂ c hinjS₂ hP i₁ hi₁)

end ExpLogSumSelection

theorem solution
    {ι : Type*} [Fintype ι] (e : ι → ℂ) (j : ι → ℕ) (c : ι → ℂ)
    (hinj : Function.Injective fun i => (e i, j i))
    (θ₀ : ℝ) (F R : ℝ → ℂ)
    (hF : ∀ y : ℝ, 0 < y → y ≤ 1 → F y = ∑ i, c i * ((y : ℂ) ^ e i * (Real.log y : ℂ) ^ j i) + R y)
    (hR : ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖R y‖ ≤ K * y ^ θ₀)
    (hray : ∃ C : ℝ, ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 → ‖F y₁‖ ≤ C * y₁ ^ θ₀) :
    ∀ i, (e i).re < θ₀ → c i = 0 := by
  obtain ⟨K, hK⟩ := hR
  obtain ⟨C, hC⟩ := hray
  refine ExpLogSumSelection.expPolySum_coeff_eq_zero_of_re_lt e j c hinj θ₀ (|C| + |K|) fun u hu => ?_

  set y : ℝ := Real.exp (-u) with hy
  have hy0 : 0 < y := Real.exp_pos _
  have hy1 : y ≤ 1 := by rw [hy, Real.exp_le_one_iff]; linarith
  have hlog : Real.log y = -u := by rw [hy, Real.log_exp]
  have hpow : y ^ θ₀ = Real.exp (-(θ₀ * u)) := by
    rw [hy, ← Real.exp_mul]; ring_nf
  have hsum : ∑ i, c i * (Complex.exp (-(u * e i)) * (-(u : ℂ)) ^ j i) =
      ∑ i, c i * ((y : ℂ) ^ e i * (Real.log y : ℂ) ^ j i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hy0.ne'), ← Complex.ofReal_log hy0.le,
      hlog]
    push_cast
    ring_nf
  have hFR : ∑ i, c i * ((y : ℂ) ^ e i * (Real.log y : ℂ) ^ j i) = F y - R y := by
    rw [hF y hy0 hy1]; ring
  rw [hsum, hFR, ← hpow]
  calc ‖F y - R y‖ ≤ ‖F y‖ + ‖R y‖ := norm_sub_le _ _
    _ ≤ C * y ^ θ₀ + K * y ^ θ₀ := add_le_add (hC y hy0 hy1) (hK y hy0 hy1)
    _ ≤ |C| * y ^ θ₀ + |K| * y ^ θ₀ := by
        have hp : 0 ≤ y ^ θ₀ := Real.rpow_nonneg hy0.le _
        exact add_le_add (mul_le_mul_of_nonneg_right (le_abs_self C) hp)
          (mul_le_mul_of_nonneg_right (le_abs_self K) hp)
    _ = (|C| + |K|) * y ^ θ₀ := by ring

end S_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow (solution)
