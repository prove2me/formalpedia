-- Prove2me | solution 1 for HiringLP.SimUpper.proposition_EC5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:28:20.288033+00:00
-- url     : https://prove2.me/submissions/5fd03292-564d-483e-b0fd-7ca9de39ead3

import Mathlib
import Definitions.Def_HiringLP_SimLower_PoissonRatio
import Definitions.Def_HiringLP_SimUpper_Constants

set_option autoImplicit false
open HiringLP.SimLower Finset

noncomputable def pp (x : ℝ) (j : ℕ) : ℝ := Real.exp (-x) * x ^ j / (j.factorial : ℝ)

noncomputable def SS (m : ℕ) (x : ℝ) : ℝ := ∑ i ∈ range m, pp x i

theorem pp_hasSum (l : ℝ) : HasSum (pp l) 1 := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) l).mul_left (Real.exp (-l))
  rw [← Real.exp_eq_exp_ℝ] at h
  have e : Real.exp (-l) * Real.exp l = 1 := by rw [← Real.exp_add]; simp
  rw [e] at h
  have e2 : pp l = fun j : ℕ => Real.exp (-l) * (l ^ j / (j.factorial : ℝ)) := by
    funext j; unfold pp; ring
  rw [e2]; exact h

theorem pp_rec (l : ℝ) (m : ℕ) : ((m + 1 : ℕ) : ℝ) * pp l (m + 1) = l * pp l m := by
  unfold pp
  rw [Nat.factorial_succ]
  push_cast
  have : ((m.factorial : ℝ)) ≠ 0 := by positivity
  have : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem pp_partial (l : ℝ) (m : ℕ) :
    ∑ i ∈ range (m + 1), (i : ℝ) * pp l i = l * SS m l := by
  unfold SS
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, sum_range_succ _ m, pp_rec l m]
    ring

theorem pp_nonneg (l : ℝ) (hl : 0 ≤ l) (j : ℕ) : 0 ≤ pp l j := by
  unfold pp; positivity

theorem SS_le_one (l : ℝ) (hl : 0 ≤ l) (m : ℕ) : SS m l ≤ 1 :=
  sum_le_hasSum (range m) (fun i _ => pp_nonneg l hl i) (pp_hasSum l)

theorem expMin_formula (x : ℝ) (k : ℕ) :
    expMinPois x k = x * SS k x + k * (1 - SS (k + 1) x) := by
  have hP2 : HasSum (fun n => pp x (n + (k + 1))) (1 - ∑ i ∈ range (k + 1), pp x i) :=
    (hasSum_nat_add_iff' (k + 1)).2 (pp_hasSum x)
  have hF : HasSum (fun n : ℕ => min ((n + (k + 1) : ℕ) : ℝ) (k : ℝ) * pp x (n + (k + 1)))
      ((k : ℝ) * (1 - ∑ i ∈ range (k + 1), pp x i)) := by
    have e : (fun n : ℕ => min ((n + (k + 1) : ℕ) : ℝ) (k : ℝ) * pp x (n + (k + 1))) =
        fun n : ℕ => (k : ℝ) * pp x (n + (k + 1)) := by
      funext n
      have : min ((n + (k + 1) : ℕ) : ℝ) (k : ℝ) = k := by
        apply min_eq_right; exact_mod_cast (by omega : k ≤ n + (k + 1))
      rw [this]
    rw [e]; exact hP2.mul_left _
  have hF2 : HasSum (fun j : ℕ => min (j : ℝ) (k : ℝ) * pp x j)
      ((k : ℝ) * (1 - ∑ i ∈ range (k + 1), pp x i) +
        ∑ i ∈ range (k + 1), min (i : ℝ) (k : ℝ) * pp x i) := by
    refine (hasSum_nat_add_iff' (f := fun j : ℕ => min (j : ℝ) (k : ℝ) * pp x j) (k + 1)).1 ?_
    have e3 : (k : ℝ) * (1 - ∑ i ∈ range (k + 1), pp x i) +
            ∑ i ∈ range (k + 1), min (i : ℝ) (k : ℝ) * pp x i -
            ∑ i ∈ range (k + 1), min (i : ℝ) (k : ℝ) * pp x i =
            (k : ℝ) * (1 - ∑ i ∈ range (k + 1), pp x i) := by ring
    rw [e3]; exact hF
  have hmin : ∑ i ∈ range (k + 1), min (i : ℝ) (k : ℝ) * pp x i =
      ∑ i ∈ range (k + 1), (i : ℝ) * pp x i := by
    apply sum_congr rfl
    intro i hi
    have : (i : ℝ) ≤ (k : ℝ) := by
      have := mem_range.1 hi
      exact_mod_cast (by omega : i ≤ k)
    rw [min_eq_left this]
  have : expMinPois x k = ∑' j : ℕ, min (j : ℝ) (k : ℝ) * pp x j := rfl
  rw [this, hF2.tsum_eq, hmin, pp_partial x k]
  unfold SS
  ring

theorem pp_deriv (j : ℕ) (x : ℝ) :
    HasDerivAt (fun y => pp y (j + 1)) (pp x j - pp x (j + 1)) x := by
  unfold pp
  have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (-Real.exp (-x)) x := by
    simpa using (hasDerivAt_neg x).exp
  have h2 : HasDerivAt (fun y : ℝ => y ^ (j + 1)) (((j + 1 : ℕ) : ℝ) * x ^ j) x := by
    simpa using hasDerivAt_pow (j + 1) x
  have h3 := (h1.mul h2).div_const (((j + 1).factorial : ℕ) : ℝ)
  refine h3.congr_deriv ?_
  rw [Nat.factorial_succ]
  push_cast
  have : ((j.factorial : ℝ)) ≠ 0 := by positivity
  have : ((j : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem pp_deriv0 (x : ℝ) : HasDerivAt (fun y => pp y 0) (-pp x 0) x := by
  unfold pp
  simpa using (hasDerivAt_neg x).exp

theorem SS_deriv (n : ℕ) (x : ℝ) : HasDerivAt (fun y => SS (n + 1) y) (-pp x n) x := by
  induction n with
  | zero => simpa [SS] using pp_deriv0 x
  | succ n ih =>
    have h := ih.add (pp_deriv n x)
    have e : (fun y => SS (n + 1 + 1) y) = fun y => SS (n + 1) y + pp y (n + 1) := by
      funext y; unfold SS; rw [sum_range_succ _ (n + 1)]
    rw [e]
    refine h.congr_deriv ?_
    ring


theorem pp_pos (x : ℝ) (hx : 0 < x) (j : ℕ) : 0 < pp x j := by
  unfold pp; positivity

theorem SS_strictAnti (n : ℕ) : StrictAntiOn (SS (n + 1)) (Set.Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · intro x _; exact (SS_deriv n x).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(SS_deriv n x).deriv]
    have := pp_pos x hx n
    linarith

theorem SS_zero (n : ℕ) : SS (n + 1) 0 = 1 := by
  unfold SS pp
  rw [sum_range_succ']
  simp

theorem SS_tendsto (m : ℕ) : Filter.Tendsto (SS m) Filter.atTop (nhds 0) := by
  unfold SS
  have : ∀ i ∈ range m, Filter.Tendsto (fun x : ℝ => pp x i) Filter.atTop (nhds 0) := by
    intro i _
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero i).div_const (i.factorial : ℝ)
    simp only [zero_div] at h
    refine h.congr (fun x => ?_)
    unfold pp; ring
  simpa using tendsto_finsetSum (range m) this

theorem E_deriv (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => expMinPois y (n + 1)) (SS (n + 1) x) x := by
  have e : (fun y => expMinPois y (n + 1)) =
      fun y => y * SS (n + 1) y + ((n + 1 : ℕ) : ℝ) * (1 - SS (n + 1 + 1) y) := by
    funext y; exact expMin_formula y (n + 1)
  rw [e]
  have h1 := (hasDerivAt_id x).mul (SS_deriv n x)
  have h2 := ((hasDerivAt_const x (1 : ℝ)).sub (SS_deriv (n + 1) x)).const_mul ((n + 1 : ℕ) : ℝ)
  refine (h1.add h2).congr_deriv ?_
  have hrec := pp_rec x n
  simp only [id]
  have : ((n + 1 : ℕ) : ℝ) * pp x (n + 1) = x * pp x n := hrec
  nlinarith [this]

theorem f_deriv (n : ℕ) (τ s : ℝ) (hτ : 0 < τ) :
    HasDerivAt (HiringLP.SimLower.ratioObj (n + 1) τ)
      (1 - 1 / τ + SS (n + 1) (s * ((n + 1 : ℕ) : ℝ)) / τ) s := by
  have hk : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hin : HasDerivAt (fun y : ℝ => y * ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ) s := by
    simpa using (hasDerivAt_id s).mul_const ((n + 1 : ℕ) : ℝ)
  have h1 := (E_deriv n (s * ((n + 1 : ℕ) : ℝ))).comp s hin
  have h2 := h1.div_const (τ * ((n + 1 : ℕ) : ℝ))
  have h3 := (hasDerivAt_id s).sub ((hasDerivAt_id s).div_const τ)
  have h4 := h3.add h2
  have e : HiringLP.SimLower.ratioObj (n + 1) τ =
      (fun y => id y - id y / τ) + fun y => (fun y => expMinPois y (n + 1)) (y * ((n + 1 : ℕ) : ℝ)) /
        (τ * ((n + 1 : ℕ) : ℝ)) := by
    funext y; simp [HiringLP.SimLower.ratioObj]
  rw [e]
  refine h4.congr_deriv ?_
  field_simp

theorem solution (k : ℕ) (hk : 1 ≤ k) (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (∃ s ∈ Set.Icc (0 : ℝ) 1, IsMaxOn (HiringLP.SimLower.ratioObj k τ) (Set.Icc 0 1) s) ∧
    (∃ s ∈ Set.Ici (0 : ℝ), IsMaxOn (HiringLP.SimLower.ratioObj k τ) (Set.Ici 0) s) ∧
    ∀ sα sβ : ℝ, sα ∈ Set.Icc (0 : ℝ) 1 → IsMaxOn (HiringLP.SimLower.ratioObj k τ) (Set.Icc 0 1) sα →
      sβ ∈ Set.Ici (0 : ℝ) → IsMaxOn (HiringLP.SimLower.ratioObj k τ) (Set.Ici 0) sβ →
      sα = min sβ 1 ∧
        τ = 1 - Real.exp (-(sβ * k)) * ∑ i ∈ range k, (sβ * k) ^ i / (i.factorial : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  set f := HiringLP.SimLower.ratioObj (n + 1) τ with hf
  set K : ℝ := ((n + 1 : ℕ) : ℝ) with hK
  have hKpos : 0 < K := by positivity
  -- root
  have hroot : ∃ x : ℝ, 0 < x ∧ SS (n + 1) x = 1 - τ := by
    have hev := (SS_tendsto (n + 1)).eventually (gt_mem_nhds (show (0 : ℝ) < 1 - τ by linarith))
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hev
    have hM' : SS (n + 1) (max M 0) < 1 - τ := hM _ (le_max_left _ _)
    have hcont : ContinuousOn (SS (n + 1)) (Set.Icc 0 (max M 0)) :=
      fun x _ => (SS_deriv n x).continuousAt.continuousWithinAt
    have := intermediate_value_Icc' (le_max_right M 0) hcont
    have hmem : (1 - τ) ∈ Set.Icc (SS (n + 1) (max M 0)) (SS (n + 1) 0) := by
      rw [SS_zero]; exact ⟨hM'.le, by linarith⟩
    obtain ⟨x, hx, hxv⟩ := this hmem
    refine ⟨x, ?_, hxv⟩
    rcases hx.1.eq_or_lt with h | h
    · rw [← h, SS_zero] at hxv; linarith
    · exact h
  obtain ⟨x0, hx0, hSx0⟩ := hroot
  set s0 : ℝ := x0 / K with hs0
  have hs0pos : 0 < s0 := by positivity
  have hs0K : s0 * K = x0 := by rw [hs0]; field_simp
  -- monotonicity
  have hdf : ∀ s, HasDerivAt f (1 - 1 / τ + SS (n + 1) (s * K) / τ) s := fun s => f_deriv n τ s hτ0
  have hinc : StrictMonoOn f (Set.Icc 0 s0) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 s0)
    · exact fun s _ => (hdf s).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hdf s).deriv]
      have hspos : 0 < s := hs.1
      have h1 : SS (n + 1) x0 < SS (n + 1) (s * K) := by
        apply SS_strictAnti n
        · exact Set.mem_Ici.2 (by positivity)
        · exact Set.mem_Ici.2 hx0.le
        · have : s * K < s0 * K := mul_lt_mul_of_pos_right hs.2 hKpos
          rw [hs0K] at this; exact this
      have : 0 < (SS (n + 1) (s * K) - (1 - τ)) / τ := div_pos (by linarith) hτ0
      have e : 1 - 1 / τ + SS (n + 1) (s * K) / τ = (SS (n + 1) (s * K) - (1 - τ)) / τ := by
        field_simp; ring
      rw [e]; exact this
  have hdec : StrictAntiOn f (Set.Ici s0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici s0)
    · exact fun s _ => (hdf s).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hdf s).deriv]
      have hspos : 0 < s := lt_trans hs0pos hs
      have h1 : SS (n + 1) (s * K) < SS (n + 1) x0 := by
        apply SS_strictAnti n
        · exact Set.mem_Ici.2 hx0.le
        · exact Set.mem_Ici.2 (by positivity)
        · have : s0 * K < s * K := mul_lt_mul_of_pos_right hs hKpos
          rw [hs0K] at this; exact this
      have e : 1 - 1 / τ + SS (n + 1) (s * K) / τ = (SS (n + 1) (s * K) - (1 - τ)) / τ := by
        field_simp; ring
      rw [e]
      exact div_neg_of_neg_of_pos (by linarith) hτ0
  have hlt : ∀ s, 0 ≤ s → s ≠ s0 → f s < f s0 := by
    intro s hs hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hinc ⟨hs, h.le⟩ ⟨hs0pos.le, le_rfl⟩ h
    · exact hdec (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h.le) h
  have hmaxβ : ∀ s, 0 ≤ s → f s ≤ f s0 := by
    intro s hs
    rcases eq_or_ne s s0 with h | h
    · rw [h]
    · exact (hlt s hs h).le
  set s1 : ℝ := min s0 1 with hs1
  have hs1pos : 0 < s1 := lt_min hs0pos one_pos
  have hs1le : s1 ≤ s0 := min_le_left _ _
  have hs1eq : ∀ t, s1 < t → t ≤ 1 → s1 = s0 := by
    intro t h1 h2
    by_contra hne
    have : s1 = 1 := by
      rcases min_choice s0 1 with h | h
      · exact absurd h hne
      · exact h
    linarith
  have hmaxα : ∀ t, 0 ≤ t → t ≤ 1 → f t ≤ f s1 := by
    intro t ht0 ht1
    by_cases ht : t ≤ s1
    · exact hinc.monotoneOn ⟨ht0, ht.trans hs1le⟩ ⟨hs1pos.le, hs1le⟩ ht
    · push Not at ht
      have := hs1eq t ht ht1
      rw [this]; exact hmaxβ t ht0
  have hβeq : ∀ sβ, 0 ≤ sβ → (∀ s, 0 ≤ s → f s ≤ f sβ) → sβ = s0 := by
    intro sβ hsβ hmx
    by_contra hne
    have h1 := hlt sβ hsβ hne
    have h2 := hmx s0 hs0pos.le
    linarith
  refine ⟨⟨s1, ⟨hs1pos.le, min_le_right _ _⟩, ?_⟩, ⟨s0, hs0pos.le, ?_⟩, ?_⟩
  · rw [isMaxOn_iff]; intro t ht; exact hmaxα t ht.1 ht.2
  · rw [isMaxOn_iff]; intro t ht; exact hmaxβ t ht
  · intro sα sβ hα hαmax hβ hβmax
    rw [isMaxOn_iff] at hαmax hβmax
    have hsβ : sβ = s0 := hβeq sβ hβ (fun s hs => hβmax s hs)
    have hsα : sα = s1 := by
      by_contra hne
      have h2 := hαmax s1 ⟨hs1pos.le, min_le_right _ _⟩
      rcases lt_or_gt_of_ne hne with h | h
      · have := hinc ⟨hα.1, h.le.trans hs1le⟩ ⟨hs1pos.le, hs1le⟩ h
        linarith
      · have h3 := hs1eq sα h hα.2
        have := hlt sα hα.1 (by rw [← h3]; exact ne_of_gt h)
        rw [← h3] at this
        linarith
    refine ⟨by rw [hsα, hsβ], ?_⟩
    rw [hsβ]
    have : SS (n + 1) x0 = Real.exp (-(s0 * K)) * ∑ i ∈ range (n + 1), (s0 * K) ^ i / (i.factorial : ℝ) := by
      rw [hs0K]
      unfold SS pp
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro i _; ring
    rw [← this, hSx0]; ring
