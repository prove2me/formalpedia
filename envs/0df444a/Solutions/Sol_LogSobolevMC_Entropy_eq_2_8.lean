-- Prove2me | solution 1 for LogSobolevMC.Entropy.eq_2_8
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:30:51.963495+00:00
-- url     : https://prove2.me/submissions/b5f23652-72f6-4420-ad57-c7947a2e92d4

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_mixing
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Entropy_Setting



namespace LogSobolevMC.Entropy

open scoped BigOperators

/-- `2(u-1)/(u+1) ≤ log u` for `u ≥ 1`. -/
lemma log_ge_two_mul_sub_div (u : ℝ) (hu : 1 ≤ u) : 2 * (u - 1) / (u + 1) ≤ Real.log u := by
  have hd : ∀ v : ℝ, 0 < v →
      HasDerivAt (fun v => Real.log v - 2 * (v - 1) / (v + 1)) (1 / v - 4 / (v + 1) ^ 2) v := by
    intro v hv
    have h1 := Real.hasDerivAt_log hv.ne'
    have h2 : HasDerivAt (fun v : ℝ => 2 * (v - 1) / (v + 1)) (4 / (v + 1) ^ 2) v := by
      have := (((hasDerivAt_id v).sub_const 1).const_mul 2).div ((hasDerivAt_id v).add_const 1)
        (by simp; linarith)
      refine this.congr_deriv ?_
      simp only [id]
      field_simp
      ring
    exact HasDerivAt.congr_deriv (h1.sub h2) (by rw [one_div])
  have hmono : MonotoneOn (fun v => Real.log v - 2 * (v - 1) / (v + 1)) (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · apply ContinuousOn.sub
      · exact Real.continuousOn_log.mono (fun v hv => by
          simp only [Set.mem_Ici] at hv; simp; linarith)
      · apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro v hv; simp only [Set.mem_Ici] at hv; linarith
    · intro v hv
      rw [interior_Ici] at hv
      exact (hd v (by simp only [Set.mem_Ioi] at hv; linarith)).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Ici] at hv
      simp only [Set.mem_Ioi] at hv
      rw [(hd v (by linarith)).deriv]
      rw [sub_nonneg, div_le_div_iff₀ (by positivity) (by linarith)]
      nlinarith [sq_nonneg (v - 1)]
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hu) hu
  simp at this
  linarith

/-- `log u ≤ 2(u-1)/(u+1)` for `0 < u ≤ 1`. -/
lemma log_le_two_mul_sub_div (u : ℝ) (hu0 : 0 < u) (hu : u ≤ 1) :
    Real.log u ≤ 2 * (u - 1) / (u + 1) := by
  have := log_ge_two_mul_sub_div (1 / u) (by rw [le_div_iff₀ hu0]; linarith)
  rw [Real.log_div (by norm_num) hu0.ne', Real.log_one] at this
  have e : 2 * (1 / u - 1) / (1 / u + 1) = -(2 * (u - 1) / (u + 1)) := by
    field_simp
    ring
  rw [e] at this
  linarith

/-- `log r ≤ (r - 1/r)/2` for `r ≥ 1`. -/
lemma log_le_half_sub_inv (r : ℝ) (hr : 1 ≤ r) : Real.log r ≤ (r - 1 / r) / 2 := by
  have hd : ∀ v : ℝ, 0 < v →
      HasDerivAt (fun v => (v - 1 / v) / 2 - Real.log v) ((1 - (-1 / v ^ 2)) / 2 - 1 / v) v := by
    intro v hv
    have h1 : HasDerivAt (fun v : ℝ => 1 / v) (-1 / v ^ 2) v := by
      have := (hasDerivAt_inv hv.ne')
      simp only [one_div]
      exact this.congr_deriv (by rw [neg_div, one_div])
    have h2 := (((hasDerivAt_id v).sub h1).div_const 2).sub (Real.hasDerivAt_log hv.ne')
    exact h2.congr_deriv (by rw [one_div])
  have hmono : MonotoneOn (fun v => (v - 1 / v) / 2 - Real.log v) (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · exact fun v hv => (hd v (by simp only [Set.mem_Ici] at hv; linarith)).continuousAt.continuousWithinAt
    · intro v hv
      rw [interior_Ici] at hv
      exact (hd v (by simp only [Set.mem_Ioi] at hv; linarith)).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Ici] at hv
      simp only [Set.mem_Ioi] at hv
      rw [(hd v (by linarith)).deriv]
      have e : (1 - (-1 / v ^ 2)) / 2 - 1 / v = (v - 1) ^ 2 / (2 * v ^ 2) := by
        field_simp
        ring
      rw [e]
      positivity
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hr) hr
  simp only [one_div] at this ⊢
  simp at this
  linarith

/-- the function `ψ(r) = (r+2)(r log r - r + 1) - 3/2 (r-1)²` is nonnegative on `[0, ∞)`. -/
lemma psi_nonneg (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ (r + 2) * (r * Real.log r - r + 1) - 3 / 2 * (r - 1) ^ 2 := by
  set ψ : ℝ → ℝ := fun r => (r + 2) * (r * Real.log r - r + 1) - 3 / 2 * (r - 1) ^ 2 with hψ
  have hd : ∀ v : ℝ, 0 < v → HasDerivAt ψ (2 * ((v + 1) * Real.log v - 2 * (v - 1))) v := by
    intro v hv
    have h1 : HasDerivAt (fun v : ℝ => v * Real.log v - v + 1) (Real.log v + 1 - 1) v :=
      ((Real.hasDerivAt_mul_log hv.ne').sub (hasDerivAt_id v)).add_const 1
    have h2 : HasDerivAt (fun v : ℝ => (v + 2) * (v * Real.log v - v + 1))
        (1 * (v * Real.log v - v + 1) + (v + 2) * (Real.log v + 1 - 1)) v :=
      ((hasDerivAt_id v).add_const 2).mul h1
    have h3 : HasDerivAt (fun v : ℝ => 3 / 2 * (v - 1) ^ 2) (3 / 2 * (2 * (v - 1) ^ 1 * 1)) v :=
      (((hasDerivAt_id v).sub_const 1).pow 2).const_mul (3 / 2)
    refine (h2.sub h3).congr_deriv ?_
    ring
  have hcont : ∀ v : ℝ, 0 < v → ContinuousAt ψ v := fun v hv => (hd v hv).continuousAt
  rcases hr.eq_or_lt with h | h
  · subst h
    simp [ψ]
    norm_num
  show 0 ≤ ψ r
  have hψ1 : ψ 1 = 0 := by simp [ψ]
  rcases le_total 1 r with h1 | h1
  · have hmono : MonotoneOn ψ (Set.Ici 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
      · exact fun v hv => (hcont v (by simp only [Set.mem_Ici] at hv; linarith)).continuousWithinAt
      · intro v hv
        rw [interior_Ici] at hv
        exact (hd v (by simp only [Set.mem_Ioi] at hv; linarith)).differentiableAt.differentiableWithinAt
      · intro v hv
        rw [interior_Ici] at hv
        simp only [Set.mem_Ioi] at hv
        rw [(hd v (by linarith)).deriv]
        have := log_ge_two_mul_sub_div v hv.le
        rw [div_le_iff₀ (by linarith)] at this
        nlinarith
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h1) h1
    linarith
  · have hanti : AntitoneOn ψ (Set.Ioc 0 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 1)
      · exact fun v hv => (hcont v hv.1).continuousWithinAt
      · intro v hv
        rw [interior_Ioc] at hv
        exact (hd v hv.1).differentiableAt.differentiableWithinAt
      · intro v hv
        rw [interior_Ioc] at hv
        rw [(hd v hv.1).deriv]
        have := log_le_two_mul_sub_div v hv.1 hv.2.le
        rw [le_div_iff₀ (by linarith [hv.1])] at this
        nlinarith [hv.1, hv.2]
    have := hanti (Set.mem_Ioc.2 ⟨h, h1⟩) (Set.mem_Ioc.2 ⟨one_pos, le_rfl⟩) h1
    linarith

/-- pointwise Pinsker-type bound -/
lemma pinsker_pt (μ π : ℝ) (hμ : 0 ≤ μ) (hπ : 0 < π) :
    3 / 2 * ((μ - π) ^ 2 / (μ + 2 * π)) ≤ μ * Real.log (μ / π) - μ + π := by
  have hr := psi_nonneg (μ / π) (div_nonneg hμ hπ.le)
  rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
  have e1 : (μ / π + 2) * (μ / π * Real.log (μ / π) - μ / π + 1) - 3 / 2 * (μ / π - 1) ^ 2
      = ((μ * Real.log (μ / π) - μ + π) * (μ + 2 * π) - 3 / 2 * (μ - π) ^ 2) / π ^ 2 := by
    field_simp
  rw [e1] at hr
  have := (div_nonneg_iff.1 hr)
  rcases this with ⟨h, _⟩ | ⟨_, h⟩
  · linarith
  · nlinarith [sq_nonneg π, hπ]

/-- pointwise upper bound -/
lemma upper_pt (μ π : ℝ) (hμ : 0 ≤ μ) (hπ : 0 < π) :
    μ * Real.log (μ / π) ≤ (if π ≤ μ then μ - π else 0) + 1 / 2 * ((μ / π - 1) ^ 2 * π) := by
  split_ifs with h
  · have hr : 1 ≤ μ / π := by rw [le_div_iff₀ hπ]; linarith
    have hμpos : 0 < μ := by linarith
    have h2 : Real.log (μ / π) ≤ (μ / π - 1 / (μ / π)) / 2 := log_le_half_sub_inv _ hr
    have e3 : (μ / π - 1 / (μ / π)) / 2 = (μ - π) / μ + (μ - π) ^ 2 / (2 * μ * π) := by
      field_simp
      ring
    rw [e3] at h2
    have h4 : μ * Real.log (μ / π) ≤ μ * ((μ - π) / μ + (μ - π) ^ 2 / (2 * μ * π)) :=
      mul_le_mul_of_nonneg_left h2 hμ
    have e2 : μ * ((μ - π) / μ + (μ - π) ^ 2 / (2 * μ * π)) = (μ - π) + 1 / 2 * ((μ / π - 1) ^ 2 * π) := by
      field_simp
    linarith
  · push_neg at h
    have : μ * Real.log (μ / π) ≤ 0 := by
      apply mul_nonpos_of_nonneg_of_nonpos hμ
      apply Real.log_nonpos (by positivity)
      rw [div_le_one hπ]; linarith
    have : 0 ≤ 1 / 2 * ((μ / π - 1) ^ 2 * π) := by positivity
    linarith

lemma tvDist_le_half_sum {V : Type*} [Fintype V] [DecidableEq V]
    (μ π : V → ℝ) (hμ : ∑ x, μ x = 1) (hπ : ∑ x, π x = 1) :
    MarkovMixing.tvDist μ π ≤ (∑ x, |μ x - π x|) / 2 := by
  unfold MarkovMixing.tvDist
  apply ciSup_le
  intro A
  rw [← Finset.sum_sub_distrib]
  have h2 : ∑ x ∈ A, (μ x - π x) + ∑ x ∈ Aᶜ, (μ x - π x) = 0 := by
    rw [Finset.sum_add_sum_compl, Finset.sum_sub_distrib, hμ, hπ, sub_self]
  have h3 : |∑ x ∈ A, (μ x - π x)| ≤ ∑ x ∈ A, |μ x - π x| := Finset.abs_sum_le_sum_abs _ _
  have h4 : |∑ x ∈ Aᶜ, (μ x - π x)| ≤ ∑ x ∈ Aᶜ, |μ x - π x| := Finset.abs_sum_le_sum_abs _ _
  have h5 : ∑ x, |μ x - π x| = ∑ x ∈ A, |μ x - π x| + ∑ x ∈ Aᶜ, |μ x - π x| :=
    (Finset.sum_add_sum_compl A _).symm
  have h6 : ∑ x ∈ Aᶜ, (μ x - π x) = -∑ x ∈ A, (μ x - π x) := by linarith
  rw [h6, abs_neg] at h4
  linarith

lemma le_tvDist {V : Type*} [Fintype V] [DecidableEq V]
    (μ π : V → ℝ) (A : Finset V) :
    ∑ x ∈ A, (μ x - π x) ≤ MarkovMixing.tvDist μ π := by
  unfold MarkovMixing.tvDist
  have := le_ciSup (f := fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, π x|)
    (Set.finite_range _).bddAbove A
  rw [Finset.sum_sub_distrib]
  exact (le_abs_self _).trans this

theorem eq_2_8_core {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → ℝ) (hπ : MarkovMixing.IsDist π) (hπpos : ∀ x, 0 < π x)
    (μ : V → ℝ) (hμ : MarkovMixing.IsDist μ) :
    2 * MarkovMixing.tvDist μ π ^ 2 ≤ relEnt π μ ∧
      relEnt π μ ≤
        MarkovMixing.tvDist μ π + 1 / 2 * LogSobolevMC.ChiSquare.lpNorm π 2 (fun x => μ x / π x - 1) ^ 2 := by
  have hS := tvDist_le_half_sum μ π hμ.2 hπ.2
  have htv0 : 0 ≤ MarkovMixing.tvDist μ π := by
    have := le_tvDist μ π ∅
    simpa using this
  constructor
  · -- Pinsker
    have hent : relEnt π μ = ∑ x, (μ x * Real.log (μ x / π x) - μ x + π x) := by
      unfold relEnt
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hμ.2, hπ.2]
      ring
    have h1 : 3 / 2 * ∑ x, (μ x - π x) ^ 2 / (μ x + 2 * π x) ≤ relEnt π μ := by
      rw [hent, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x _
      exact pinsker_pt (μ x) (π x) (hμ.1 x) (hπpos x)
    have h2 := Finset.sq_sum_div_le_sum_sq_div (Finset.univ) (fun x => |μ x - π x|)
      (g := fun x => μ x + 2 * π x) (fun x _ => by linarith [hμ.1 x, hπpos x])
    simp only [sq_abs] at h2
    have h3 : ∑ x, (μ x + 2 * π x) = 3 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hμ.2, hπ.2]; norm_num
    rw [h3] at h2
    have h4 : (∑ x, |μ x - π x|) ^ 2 / 3 * (3 / 2) ≤ relEnt π μ := by
      nlinarith
    have h5 : MarkovMixing.tvDist μ π ^ 2 ≤ ((∑ x, |μ x - π x|) / 2) ^ 2 :=
      pow_le_pow_left₀ htv0 hS 2
    nlinarith
  · -- upper bound
    have hnorm : LogSobolevMC.ChiSquare.lpNorm π 2 (fun x => μ x / π x - 1) ^ 2
        = ∑ x, (μ x / π x - 1) ^ 2 * π x := by
      unfold LogSobolevMC.ChiSquare.lpNorm
      have hnn : 0 ≤ ∑ x, |μ x / π x - 1| ^ (2:ℝ) * π x := by
        apply Finset.sum_nonneg; intro x _
        exact mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (hπpos x).le
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hnn]
      apply Finset.sum_congr rfl; intro x _
      rw [Real.rpow_two, sq_abs]
    rw [hnorm]
    have hpt : relEnt π μ ≤ ∑ x, ((if π x ≤ μ x then μ x - π x else 0) + 1 / 2 * ((μ x / π x - 1) ^ 2 * π x)) := by
      unfold relEnt
      apply Finset.sum_le_sum; intro x _
      exact upper_pt (μ x) (π x) (hμ.1 x) (hπpos x)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_filter] at hpt
    have := le_tvDist μ π (Finset.univ.filter fun x => π x ≤ μ x)
    linarith

end LogSobolevMC.Entropy

open LogSobolevMC.Entropy


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → ℝ) (hπ : MarkovMixing.IsDist π) (hπpos : ∀ x, 0 < π x)
    (μ : V → ℝ) (hμ : MarkovMixing.IsDist μ) :
    2 * MarkovMixing.tvDist μ π ^ 2 ≤ relEnt π μ ∧
      relEnt π μ ≤
        MarkovMixing.tvDist μ π + 1 / 2 * LogSobolevMC.ChiSquare.lpNorm π 2 (fun x => μ x / π x - 1) ^ 2 := by
  exact eq_2_8_core π hπ hπpos μ hμ
