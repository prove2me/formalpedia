-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.valid_execution_bounded_price_strictness_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:25:52.294274+00:00
-- url     : https://prove2.me/submissions/ef1d43c7-92cc-41d9-ae9d-238f4ba4ff7c

import Mathlib
import Definitions.Def_Q238K023

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_NearestDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

lemma nearestDistance_nonneg {X : Type*} [PseudoMetricSpace X]
    (x : X) (S : Finset X) : 0 ≤ nearestDistance x S := by
  classical
  unfold nearestDistance
  split_ifs with h
  · exact Finset.le_inf' h _ (fun _ _ => dist_nonneg)
  · exact le_rfl

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_StrictnessGap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

lemma sum_linearRow {q : ℕ} (d a : Fin q → ℝ)
    (hd : (∑ j, d j) = 1) (p : Fin q) :
    (∑ j, linearRow d a p j) =
      (q : ℝ) * a p - 1 - prefixMass d p - (p.val : ℝ) * d p := by
  simp only [linearRow, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hd]
  rw [← Finset.sum_filter, Finset.filter_gt_eq_Iio]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Fin.card_Iio, nsmul_eq_mul,
    prefixMass]
  ring

lemma suffix_row_bound {q : ℕ} {lam : ℝ} {d a A : Fin q → ℝ}
    (hs : SuffixConstraints lam d a A) (p : Fin q) :
    (∑ j, if j < p then max (A p - 2 * d j) 0 else max (a p - d j) 0) ≤ lam := by
  have h := hs.2.2.2 p
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j < p
  · simp [hj, not_le.mpr hj]
  · simp [hj, le_of_not_gt hj]

lemma slack_envelope {q : ℕ} {lam : ℝ} {d a A : Fin q → ℝ}
    (hs : SuffixConstraints lam d a A) (p : Fin q) :
    (p.val : ℝ) * (A p - a p + d p) ≤ slack lam d a p := by
  have hpoint : ∀ j : Fin q,
      linearRow d a p j + (if j < p then A p - a p + d p else 0) ≤
        if j < p then max (A p - 2 * d j) 0 else max (a p - d j) 0 := by
    intro j
    by_cases hj : j < p
    · simp only [linearRow, hj, ↓reduceIte]
      linarith [le_max_left (A p - 2 * d j) 0]
    · simp only [linearRow, hj, ↓reduceIte, sub_zero, add_zero]
      exact le_max_left _ _
  have h := (Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hpoint j).trans
    (suffix_row_bound hs p)
  rw [Finset.sum_add_distrib, sum_linearRow d a hs.2.1 p,
    ← Finset.sum_filter, Finset.filter_gt_eq_Iio] at h
  simp only [Finset.sum_const, Fin.card_Iio, nsmul_eq_mul] at h
  dsimp [slack]
  linarith

lemma slack_nonneg {q : ℕ} {lam : ℝ} {d a A : Fin q → ℝ}
    (hs : SuffixConstraints lam d a A) (p : Fin q) : 0 ≤ slack lam d a p := by
  apply le_trans _ (slack_envelope hs p)
  apply mul_nonneg (Nat.cast_nonneg _)
  linarith [hs.2.2.1 p p le_rfl]

lemma slack_truncation {q : ℕ} {lam : ℝ} {d a A : Fin q → ℝ}
    (hs : SuffixConstraints lam d a A) (p : Fin q) :
    (∑ j, max (d j - a p) 0) ≤ slack lam d a p := by
  have hpoint : ∀ j : Fin q,
      linearRow d a p j + max (d j - a p) 0 ≤
        if j < p then max (A p - 2 * d j) 0 else max (a p - d j) 0 := by
    intro j
    by_cases hj : j < p
    · simp only [linearRow, hj, ↓reduceIte]
      rcases le_total (d j - a p) 0 with h | h
      · rw [max_eq_right h]
        linarith [hs.2.2.1 p p le_rfl, le_max_left (A p - 2 * d j) 0]
      · rw [max_eq_left h]
        linarith [hs.1 p, hs.1 j, le_max_right (A p - 2 * d j) 0]
    · simp only [linearRow, hj, ↓reduceIte, sub_zero]
      rcases le_total (d j - a p) 0 with h | h
      · rw [max_eq_right h, add_zero]
        exact le_max_left _ _
      · rw [max_eq_left h]
        linarith [le_max_right (a p - d j) 0]
  have h := (Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hpoint j).trans
    (suffix_row_bound hs p)
  rw [Finset.sum_add_distrib, sum_linearRow d a hs.2.1 p] at h
  dsimp [slack]
  linarith

lemma sum_prefixMass {q : ℕ} (d : Fin q → ℝ) :
    (∑ p, prefixMass d p) = ∑ j, ((q : ℝ) - 1 - (j.val : ℝ)) * d j := by
  simp only [prefixMass, ← Finset.filter_gt_eq_Iio, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]
  simp only [Finset.sum_const, Fin.card_Ioi, nsmul_eq_mul]
  have hj : j.val ≤ q - 1 := Nat.le_sub_one_of_lt j.isLt
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Nat.ne_zero_of_lt j.isLt)
  rw [Nat.cast_sub hj, Nat.cast_sub hq, Nat.cast_one]

lemma sum_slack {q : ℕ} (lam : ℝ) (d a : Fin q → ℝ)
    (hd : (∑ j, d j) = 1) :
    (∑ p, slack lam d a p) = (q : ℝ) * (lam + 2 - ∑ p, a p) - 1 := by
  simp only [slack, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum, sum_prefixMass]
  have hsum : (∑ j, ((q : ℝ) - 1 - (j.val : ℝ)) * d j) +
      (∑ p, (p.val : ℝ) * d p) = (q : ℝ) - 1 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ j, ((q : ℝ) - 1) * d j := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (q : ℝ) - 1 := by rw [← Finset.mul_sum, hd, mul_one]
  linarith

lemma subset_mass_bound {q : ℕ} {lam B : ℝ} {d a A : Fin q → ℝ}
    (hs : SuffixConstraints lam d a A) (haB : (∑ p, a p) ≤ B)
    (I : Finset (Fin q)) :
    (q : ℝ) * (∑ j ∈ I, d j) ≤ (I.card : ℝ) * B + ∑ p, slack lam d a p := by
  have hp : ∀ p : Fin q,
      (∑ j ∈ I, (d j - a p)) ≤ slack lam d a p := by
    intro p
    apply le_trans (Finset.sum_le_sum fun j _ => le_max_left (d j - a p) 0)
    apply le_trans _ (slack_truncation hs p)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intro j _ _
      exact le_max_right _ _)
  have h := Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => hp p
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum] at h
  have hB := mul_le_mul_of_nonneg_left haB (Nat.cast_nonneg I.card)
  linarith

lemma prefix_le_mass {q : ℕ} {d : Fin q → ℝ} (hd : ∀ p, 0 ≤ d p)
    (p : Fin q) (I : Finset (Fin q)) (hI : Finset.Iio p ⊆ I) :
    prefixMass d p ≤ ∑ j ∈ I, d j := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hI (by intro j _ _; exact hd j)

lemma one_sub_prefix_le_mass {q : ℕ} {d : Fin q → ℝ}
    (hd : ∀ p, 0 ≤ d p) (hsum : (∑ p, d p) = 1)
    (p : Fin q) (I : Finset (Fin q)) (hI : Finset.Ici p ⊆ I) :
    1 - prefixMass d p ≤ ∑ j ∈ I, d j := by
  have hpart : prefixMass d p + (∑ j ∈ Finset.Ici p, d j) = 1 := by
    rw [prefixMass, ← Finset.sum_union]
    · have hu : Finset.Iio p ∪ Finset.Ici p = Finset.univ := by
        ext j
        simp only [Finset.mem_union, Finset.mem_Iio, Finset.mem_Ici, Finset.mem_univ,
          iff_true]
        exact lt_or_ge j p
      rwa [hu]
    · exact Finset.disjoint_left.mpr (by
        intro j hj hk
        exact not_le.mpr (Finset.mem_Iio.mp hj) (Finset.mem_Ici.mp hk))
  have hle : (∑ j ∈ Finset.Ici p, d j) ≤ ∑ j ∈ I, d j :=
    Finset.sum_le_sum_of_subset_of_nonneg hI (by intro j _ _; exact hd j)
  linarith

theorem suffix_strictness (q : ℕ) (hq : 0 < q) (T lam : ℝ)
    (hT : 0 < T) (_hlam : 0 ≤ lam) (hlamT : lam ≤ T)
    (d a A : Fin q → ℝ) (_ha : ∀ p, 0 ≤ a p)
    (hs : SuffixConstraints lam d a A) :
    (∑ p, a p) ≤ lam + 2 - strictnessGap T := by
  let B : ℝ := T + 2
  let ρ : ℝ := 1 / (200 * B)
  let c : ℝ := ρ ^ 2 / 100
  have hB : 2 < B := by dsimp [B] <;> linarith
  have hρ : 0 < ρ := by dsimp [ρ] <;> positivity
  have hρB : ρ * B = 1 / 200 := by
    dsimp [ρ]
    field_simp
  have hρsmall : ρ < 1 / 400 := by nlinarith only [hρB, hB, hρ]
  have hc : 0 < c := by dsimp [c] <;> positivity
  have hcρ : c < ρ / 100 := by dsimp [c]; nlinarith only [hρsmall, hρ]
  have hcsmall : c < 1 / 100 := by linarith only [hcρ, hρsmall]
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hEnonneg : 0 ≤ ∑ p, slack lam d a p :=
    Finset.sum_nonneg fun p _ => slack_nonneg hs p
  have hEsum := sum_slack lam d a hs.2.1
  by_contra hn
  have hdef : lam + 2 - ∑ p, a p < c := by
    change ¬ (∑ p, a p) ≤ lam + 2 - c at hn
    linarith
  have hEsmall : (∑ p, slack lam d a p) < (q : ℝ) * c := by
    nlinarith only [hEsum, hEnonneg, mul_lt_mul_of_pos_left hdef hqR]
  have hqc : 1 < (q : ℝ) * c := by
    nlinarith only [hEsum, hEnonneg, mul_lt_mul_of_pos_left hdef hqR]
  have haB : (∑ p, a p) ≤ B := by
    dsimp [B]
    nlinarith only [hEsum, hEnonneg, hqR, hlamT]
  have hsmall : ∀ I : Finset (Fin q), (I.card : ℝ) ≤ 2 * ρ * q →
      (∑ j ∈ I, d j) < 1 / 50 := by
    intro I hI
    have hbound : (q : ℝ) * (∑ j ∈ I, d j) < (q : ℝ) * (1 / 100 + c) := by
      calc
        _ ≤ (I.card : ℝ) * B + ∑ p, slack lam d a p := subset_mass_bound hs haB I
        _ < (2 * ρ * q) * B + (q : ℝ) * c :=
          add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_right hI (by linarith only [hB])) hEsmall
        _ = (q : ℝ) * (1 / 100 + c) := by linear_combination 2 * (q : ℝ) * hρB
    have hmass := (mul_lt_mul_iff_right₀ hqR).mp hbound
    linarith only [hmass, hcsmall]
  let r : ℕ := ⌊ρ * q⌋₊
  have hrle : (r : ℝ) ≤ ρ * q := Nat.floor_le (by positivity)
  have hrlower : ρ * q < (r : ℝ) + 1 := Nat.lt_floor_add_one _
  have hx : 4 < ρ * q := by
    have hm := mul_lt_mul_of_pos_left hcρ hqR
    nlinarith only [hm, hqc]
  have hrhalf : ρ * q / 2 < (r : ℝ) := by linarith only [hrlower, hx]
  have hrR : 0 < (r : ℝ) := by linarith only [hrhalf, hx]
  have hr : 0 < r := by exact_mod_cast hrR
  have hrq : 3 * r < q := by
    have hm := mul_lt_mul_of_pos_right hρsmall hqR
    have hh : (3 : ℝ) * r < q := by linarith only [hm, hrle, hqR]
    exact_mod_cast hh
  have hrlt : r < q := by omega
  have h2rlt : 2 * r < q := by omega
  let lo : Fin q := ⟨r, hrlt⟩
  let mid : Fin q := ⟨2 * r, h2rlt⟩
  let tailStart : Fin q := ⟨q - r, by omega⟩
  let tail : Finset (Fin q) := Finset.Ici tailStart
  let early : Finset (Fin q) := Finset.Ico lo mid
  let head : Finset (Fin q) := Finset.Iio mid
  have htailcard : tail.card = r := by
    simp only [tail, Fin.card_Ici, tailStart]
    omega
  have hearlycard : early.card = r := by
    simp only [early, Fin.card_Ico, lo, mid]
    omega
  have hheadcard : head.card = 2 * r := by simp [head, mid]
  have htailmass : (∑ j ∈ tail, d j) < 1 / 50 := by
    apply hsmall
    rw [htailcard]
    linarith only [hrle, hrR]
  have hheadmass : (∑ j ∈ head, d j) < 1 / 50 := by
    apply hsmall
    rw [hheadcard, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hrle]
  let g : Fin q → ℝ := fun p => slack lam d a p + ((q : ℝ) - p.val) * d p
  have hg : ∀ p, 0 ≤ g p := by
    intro p
    apply add_nonneg (slack_nonneg hs p)
    apply mul_nonneg _ (hs.1 p)
    have hp : (p.val : ℝ) < q := by exact_mod_cast p.isLt
    linarith
  have hidentity : ∀ p, (q : ℝ) * (a p - d p) =
      lam + 1 + prefixMass d p - g p := by
    intro p
    dsimp [g, slack]
    ring
  have hqcsmall : (q : ℝ) * c < (r : ℝ) / 50 := by
    have hm := mul_lt_mul_of_pos_left hcρ hqR
    nlinarith only [hm, hrhalf]
  have htailg : (∑ p ∈ tail, g p) < (r : ℝ) / 10 := by
    have hweighted : (∑ p ∈ tail, ((q : ℝ) - p.val) * d p) ≤
        (r : ℝ) * (∑ p ∈ tail, d p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_right _ (hs.1 p)
      have hp' : q - r ≤ p.val := (show tailStart ≤ p from Finset.mem_Ici.mp hp)
      have hnat : q ≤ p.val + r := by omega
      have hreal : (q : ℝ) ≤ p.val + r := by exact_mod_cast hnat
      linarith
    have hEsub : (∑ p ∈ tail, slack lam d a p) ≤ ∑ p, slack lam d a p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (by intro p _ _; exact slack_nonneg hs p)
    have hmass := mul_lt_mul_of_pos_left htailmass hrR
    simp only [g, Finset.sum_add_distrib]
    linarith only [hweighted, hEsub, hEsmall, hqcsmall, hmass, hrR]
  have htailg' : (∑ p ∈ tail, g p) < ∑ _p ∈ tail, (1 / 10 : ℝ) := by
    simpa [htailcard, div_eq_mul_inv] using htailg
  obtain ⟨s, hstail, hsg⟩ := Finset.exists_lt_of_sum_lt htailg'
  have hsprefix : 49 / 50 < prefixMass d s := by
    have hh := one_sub_prefix_le_mass hs.1 hs.2.1 s tail (by
      intro j hj
      exact Finset.mem_Ici.mpr ((Finset.mem_Ici.mp hstail).trans (Finset.mem_Ici.mp hj)))
    linarith only [hh, htailmass]
  have hslarge : lam + 1.8 < (q : ℝ) * (a s - d s) := by
    rw [hidentity]
    linarith only [hsprefix, hsg]
  have hearly : ∀ p ∈ early, (7 / 10 : ℝ) * r ≤ (q : ℝ) * slack lam d a p := by
    intro p hp
    have hp' := Finset.mem_Ico.mp hp
    have hpr : r ≤ p.val := hp'.1
    have hpmid : p.val < 2 * r := hp'.2
    have hsval : q - r ≤ s.val := (show tailStart ≤ s from Finset.mem_Ici.mp hstail)
    have hps : p ≤ s := by change p.val ≤ s.val; omega
    have hprefix : prefixMass d p < 1 / 50 := by
      apply lt_of_le_of_lt (prefix_le_mass hs.1 p head _) hheadmass
      intro j hj
      exact Finset.mem_Iio.mpr ((Finset.mem_Iio.mp hj).trans hp'.2)
    have hpsmall : (q : ℝ) * (a p - d p) < lam + 1.02 := by
      rw [hidentity]
      linarith only [hprefix, hg p]
    have hdom := mul_le_mul_of_nonneg_left (hs.2.2.1 p s hps) (le_of_lt hqR)
    have hgap : (7 / 10 : ℝ) < (q : ℝ) * (A p - a p + d p) := by linarith only [hdom, hpsmall, hslarge]
    have henv := mul_le_mul_of_nonneg_left (slack_envelope hs p) (le_of_lt hqR)
    have hpR : (r : ℝ) ≤ p.val := by exact_mod_cast hpr
    have hpnonneg : (0 : ℝ) ≤ p.val := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left (le_of_lt hgap) hpnonneg
    nlinarith only [henv, hmul, hpR]
  have hearlysum : (7 / 10 : ℝ) * r * r ≤ (q : ℝ) * ∑ p, slack lam d a p := by
    have hi := Finset.sum_le_sum hearly
    simp only [Finset.sum_const, hearlycard, nsmul_eq_mul, ← Finset.mul_sum] at hi
    have hsub : (∑ p ∈ early, slack lam d a p) ≤ ∑ p, slack lam d a p :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (by intro p _ _; exact slack_nonneg hs p)
    have hmul := mul_le_mul_of_nonneg_left hsub (le_of_lt hqR)
    nlinarith only [hi, hmul]
  have hqqE := mul_lt_mul_of_pos_left hEsmall hqR
  have hsquare : (ρ * q) ^ 2 < 4 * (r : ℝ) ^ 2 := by
    have hm := mul_pos (show 0 < 2 * (r : ℝ) - ρ * q by linarith only [hrhalf])
      (show 0 < 2 * (r : ℝ) + ρ * q by linarith only [hx, hrR])
    nlinarith only [hm]
  have hcc : (q : ℝ) * q * c = (ρ * q) ^ 2 / 100 := by dsimp [c] <;> ring
  nlinarith only [hearlysum, hqqE, hsquare, hcc, sq_nonneg (r : ℝ)]

lemma positivePart_div (x P : ℝ) (hP : 0 < P) :
    max (x / P) 0 = max x 0 / P := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_left (div_nonneg hx hP.le)]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', max_eq_right (div_nonpos_of_nonpos_of_nonneg hx' hP.le), zero_div]

theorem scaled_suffix_strictness (q : ℕ) (hq : 0 < q) (T lam P : ℝ)
    (hT : 0 < T) (hlam : 0 ≤ lam) (hP : 0 < P) (hlamT : lam ≤ T * P)
    (d a A : Fin q → ℝ) (ha : ∀ p, 0 ≤ a p)
    (hd : ∀ p, 0 ≤ d p) (hdP : (∑ p, d p) = P)
    (henv : ∀ p s, p ≤ s → a s - d s ≤ A p)
    (hrow : ∀ p,
      (∑ j ∈ Finset.univ.filter (fun j => p ≤ j), max (a p - d j) 0) +
      (∑ j ∈ Finset.univ.filter (fun j => j < p), max (A p - 2 * d j) 0) ≤ lam) :
    (∑ p, a p) ≤ lam + (2 - strictnessGap T) * P := by
  have hnorm : SuffixConstraints (lam / P) (fun p => d p / P)
      (fun p => a p / P) (fun p => A p / P) := by
    refine ⟨fun p => div_nonneg (hd p) hP.le, ?_, ?_, ?_⟩
    · rw [← Finset.sum_div, hdP, div_self (ne_of_gt hP)]
    · intro p s hps
      rw [← sub_div]
      exact div_le_div_of_nonneg_right (henv p s hps) hP.le
    · intro p
      simp_rw [← mul_div_assoc, ← sub_div, positivePart_div _ _ hP]
      rw [← Finset.sum_div, ← Finset.sum_div, ← add_div]
      exact div_le_div_of_nonneg_right (hrow p) hP.le
  have h := suffix_strictness q hq T (lam / P) hT (div_nonneg hlam hP.le)
    ((div_le_iff₀ hP).mpr hlamT) (fun p => d p / P) (fun p => a p / P)
    (fun p => A p / P) (fun p => div_nonneg (ha p) hP.le) hnorm
  rw [← Finset.sum_div] at h
  have hh := (div_le_iff₀ hP).mp h
  have heq : (lam / P + 2 - strictnessGap T) * P =
      lam + (2 - strictnessGap T) * P := by
    field_simp
    ring
  rwa [heq] at hh

theorem suffix_final_budget_bound (q : ℕ) (hq : 0 < q) (T lam P v : ℝ)
    (hT : 0 < T) (hlam : 0 ≤ lam) (hP : 0 < P) (hlamT : lam ≤ T * P)
    (hv : 0 < v) (hv1 : v ≤ 1) (hvsmall : v ^ 2 ≤ strictnessGap T / (6 * (T + 2)))
    (d a A alpha : Fin q → ℝ) (ha : ∀ p, 0 ≤ a p)
    (hd : ∀ p, 0 ≤ d p) (hdP : (∑ p, d p) = P)
    (henv : ∀ p s, p ≤ s → a s - d s ≤ A p)
    (hrow : ∀ p,
      (∑ j ∈ Finset.univ.filter (fun j => p ≤ j), max (a p - d j) 0) +
      (∑ j ∈ Finset.univ.filter (fun j => j < p), max (A p - 2 * d j) 0) ≤ lam)
    (halpha : ∀ p, alpha p ≤ (1 + v ^ 2) ^ 2 * a p) :
    (∑ p, alpha p) ≤ lam + (2 - strictnessGap T / 2) * P := by
  let K : ℝ := 1 + v ^ 2
  let B : ℝ := T + 2
  let c : ℝ := strictnessGap T
  have hB : 0 < B := by dsimp [B]; linarith only [hT]
  have hc : 0 ≤ c := by dsimp [c, strictnessGap] <;> positivity
  have hK : 0 ≤ K ^ 2 - 1 := by dsimp [K]; nlinarith only [sq_nonneg v]
  have hv2 : v ^ 2 ≤ 1 := by nlinarith only [hv, hv1]
  have hKsmall : K ^ 2 - 1 ≤ 3 * v ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hv2 (sq_nonneg v)
    dsimp [K]
    nlinarith only [hm]
  have hvB : v ^ 2 * (6 * B) ≤ c := (le_div_iff₀ (by positivity : 0 < 6 * B)).mp hvsmall
  have hKB : (K ^ 2 - 1) * B ≤ c / 2 := by
    have hm := mul_le_mul_of_nonneg_right hKsmall hB.le
    nlinarith only [hm, hvB]
  have hs := scaled_suffix_strictness q hq T lam P hT hlam hP hlamT d a A ha hd hdP henv hrow
  have hsB : (∑ p, a p) ≤ B * P := by
    have hm := mul_nonneg hc hP.le
    change (∑ p, a p) ≤ (T + 2) * P
    change (∑ p, a p) ≤ lam + (2 - c) * P at hs
    nlinarith only [hs, hlamT, hm]
  calc
    (∑ p, alpha p) ≤ ∑ p, K ^ 2 * a p := Finset.sum_le_sum fun p _ => halpha p
    _ = K ^ 2 * (∑ p, a p) := (Finset.mul_sum _ _ _).symm
    _ = (∑ p, a p) + (K ^ 2 - 1) * (∑ p, a p) := by ring
    _ ≤ lam + (2 - c) * P + (K ^ 2 - 1) * (B * P) :=
      add_le_add hs (mul_le_mul_of_nonneg_left hsB hK)
    _ = lam + (2 - c) * P + ((K ^ 2 - 1) * B) * P := by ring
    _ ≤ lam + (2 - c) * P + (c / 2) * P :=
      by linarith only [mul_le_mul_of_nonneg_right hKB hP.le]
    _ = lam + (2 - strictnessGap T / 2) * P := by dsimp [c] <;> ring

end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RemovalReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

namespace RemovalReplay

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X]
  {steps : ℕ} {t K lam : ℝ} (R : RemovalReplay D X steps t K lam)

lemma phase_div_le (ht : 0 ≤ t) (htK : t ≤ K) (hK : 0 < K)
    (i : X) (j s : D) (f : X) (hf : f ∈ R.before (R.removal s))
    (b : ℝ) (hb : t * dist (R.location j) f ≤ K * b) :
    R.phase (R.removal s) / K ≤ b + dist i (R.location s) + dist i (R.location j) := by
  have htri : dist (R.location s) f ≤
      dist i (R.location s) + dist i (R.location j) + dist (R.location j) f := by
    calc
      _ ≤ dist (R.location s) i + dist i f := dist_triangle _ _ _
      _ ≤ dist (R.location s) i + (dist i (R.location j) + dist (R.location j) f) :=
        add_le_add_right (dist_triangle _ _ _) _
      _ = _ := by rw [dist_comm (R.location s) i]; ring
  have hmul := mul_le_mul_of_nonneg_left htri ht
  have hds := mul_le_mul_of_nonneg_right htK
    (add_nonneg (dist_nonneg (x := i) (y := R.location s))
      (dist_nonneg (x := i) (y := R.location j)))
  apply (div_le_iff₀ hK).mpr
  nlinarith only [R.active_threshold s f hf, hmul, hds, hb]

lemma earlier_bid_dominates (ht : 0 ≤ t) (htK : t ≤ K) (hK1 : 1 ≤ K)
    (i : X) (j p s : D)
    (hjp : R.removal j ≤ R.removal p) (hps : R.removal p ≤ R.removal s) :
    R.phase (R.removal s) / K - dist i (R.location s) - dist i (R.location j) ≤
      R.boundaryBid (R.removal p) j := by
  classical
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  by_cases hlt : R.removal j < R.removal p
  · obtain ⟨g, hg, _⟩ := R.post_removal j
    have hne : (R.before (R.removal p)).Nonempty :=
      ⟨g, R.after_in_later _ _ hlt hg⟩
    obtain ⟨f, hf, heq⟩ := nearestDistance_attained (R.location j) _ hne
    have hb : 0 ≤ t * nearestDistance (R.location j) (R.before (R.removal p)) :=
      mul_nonneg ht (nearestDistance_nonneg _ _)
    have hconn : t * dist (R.location j) f ≤
        K * (t * nearestDistance (R.location j) (R.before (R.removal p))) := by
      rw [← heq]
      nlinarith only [mul_le_mul_of_nonneg_right hK1 hb]
    have h := R.phase_div_le ht htK hK i j s f (R.before_mono hps hf) _ hconn
    simp only [boundaryBid, hlt, ↓reduceIte]
    linarith only [h]
  · have heq : R.removal j = R.removal p := le_antisymm hjp (le_of_not_gt hlt)
    simp only [boundaryBid, hlt, ↓reduceIte]
    rcases lt_or_eq_of_le hps with hps | hps
    · obtain ⟨f, hf, hb⟩ := R.post_removal j
      have hjs : R.removal j < R.removal s := heq ▸ hps
      have h := R.phase_div_le ht htK hK i j s f (R.after_in_later _ _ hjs hf)
        (R.phase (R.removal j)) hb
      rw [heq] at h
      linarith only [h]
    · have hphase := R.phase_nonneg (R.removal p)
      have hdiv : R.phase (R.removal p) / K ≤ R.phase (R.removal p) := by
        apply (div_le_iff₀ hK).mpr
        nlinarith only [mul_le_mul_of_nonneg_right hK1 hphase]
      rw [← hps]
      linarith only [hdiv, dist_nonneg (x := i) (y := R.location s),
        dist_nonneg (x := i) (y := R.location j)]

lemma selected_no_overbid {q : ℕ} (cluster : Fin q ↪ D) (n : Fin steps)
    (i : X) (hi : i ∈ R.regular) :
    (∑ j, max (R.boundaryBid n (cluster j) - dist i (R.location (cluster j))) 0) ≤ lam := by
  classical
  calc
    _ = ∑ j ∈ Finset.univ.map cluster,
        max (R.boundaryBid n j - dist i (R.location j)) 0 :=
      (Finset.sum_map _ _ _).symm
    _ ≤ ∑ j, max (R.boundaryBid n j - dist i (R.location j)) 0 :=
      Finset.sum_le_univ_sum_of_nonneg fun _ => le_max_right _ _
    _ ≤ lam := R.no_overbid n i hi

end RemovalReplay

lemma le_suffixMaximum {q : ℕ} (a d : Fin q → ℝ) (p s : Fin q) (hps : p ≤ s) :
    a s - d s ≤ suffixMaximum a d p :=
  Finset.le_sup' (fun s => a s - d s) (Finset.mem_Ici.mpr hps)

lemma suffixMaximum_le {q : ℕ} (a d : Fin q → ℝ) (p : Fin q) (b : ℝ)
    (h : ∀ s, p ≤ s → a s - d s ≤ b) : suffixMaximum a d p ≤ b :=
  Finset.sup'_le _ _ (fun s hs => h s (Finset.mem_Ici.mp hs))

theorem replay_bounded_price_strictness
    {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (steps q : ℕ) (hq : 0 < q) (T lam delta v : ℝ)
    (hT : 0 < T) (hlam : 0 ≤ lam) (hdelta : 0 ≤ delta) (hdelta1 : delta < 1)
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hvsmall : v ^ 2 ≤ strictnessGap T / (6 * (T + 2)))
    (R : RemovalReplay D X steps (1 - delta) (1 + v ^ 2) lam)
    (i : X) (hi : i ∈ R.regular) (cluster : Fin q ↪ D)
    (horder : Monotone (fun p => R.removal (cluster p)))
    (hP : 0 < ∑ p, dist i (R.location (cluster p)))
    (hprice : lam ≤ T * (∑ p, dist i (R.location (cluster p)))) :
    (∑ p, R.budget (cluster p)) ≤
      lam + (2 - strictnessGap T / 2) * (∑ p, dist i (R.location (cluster p))) := by
  classical
  let K : ℝ := 1 + v ^ 2
  let t : ℝ := 1 - delta
  let d : Fin q → ℝ := fun p => dist i (R.location (cluster p))
  let a : Fin q → ℝ := fun p => R.phase (R.removal (cluster p)) / K
  let A := suffixMaximum a d
  have hK1 : 1 ≤ K := by dsimp [K]; linarith only [sq_nonneg v]
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have ht : 0 ≤ t := by dsimp [t]; linarith only [hdelta1]
  have htK : t ≤ K := by dsimp [t]; linarith only [hdelta, hK1]
  have ha : ∀ p, 0 ≤ a p := fun p => div_nonneg (R.phase_nonneg _) hK.le
  have henv : ∀ p s, p ≤ s → a s - d s ≤ A p := le_suffixMaximum a d
  have hpast : ∀ p j, j < p → A p - 2 * d j ≤
      R.boundaryBid (R.removal (cluster p)) (cluster j) - d j := by
    intro p j hj
    have hmax : A p ≤ R.boundaryBid (R.removal (cluster p)) (cluster j) + d j := by
      apply suffixMaximum_le
      intro s hs
      have h := R.earlier_bid_dominates ht htK hK1 i (cluster j) (cluster p)
        (cluster s) (horder hj.le) (horder hs)
      change a s - d s - d j ≤ _ at h
      linarith only [h]
    linarith only [hmax]
  have hfuture : ∀ p j, p ≤ j → a p - d j ≤
      R.boundaryBid (R.removal (cluster p)) (cluster j) - d j := by
    intro p j hj
    have hnlt : ¬R.removal (cluster j) < R.removal (cluster p) := not_lt.mpr (horder hj)
    change a p - d j ≤ (if _ then _ else _) - d j
    rw [ite_eq_right hnlt]
    have haphase : a p ≤ R.phase (R.removal (cluster p)) := by
      apply (div_le_iff₀ hK).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hK1 (R.phase_nonneg (R.removal (cluster p)))]
    linarith only [haphase]
  have hrow : ∀ p,
      (∑ j ∈ Finset.univ.filter (fun j => p ≤ j), max (a p - d j) 0) +
      (∑ j ∈ Finset.univ.filter (fun j => j < p), max (A p - 2 * d j) 0) ≤ lam := by
    intro p
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply le_trans _ (R.selected_no_overbid cluster (R.removal (cluster p)) i hi)
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j < p
    · simp only [hj, not_le.mpr hj, ↓reduceIte, zero_add]
      exact max_le_max (hpast p j hj) le_rfl
    · simp only [hj, le_of_not_gt hj, ↓reduceIte, add_zero]
      exact max_le_max (hfuture p j (le_of_not_gt hj)) le_rfl
  apply suffix_final_budget_bound q hq T lam (∑ p, d p) v hT hlam hP hprice hv hv1 hvsmall
    d a A (fun p => R.budget (cluster p)) ha (fun _ => dist_nonneg) rfl henv hrow
  intro p
  have hcap := R.final_cap (cluster p)
  change R.budget (cluster p) ≤ K ^ 2 * (R.phase (R.removal (cluster p)) / K)
  have heq : K ^ 2 * (R.phase (R.removal (cluster p)) / K) =
      K * R.phase (R.removal (cluster p)) := by field_simp
  rwa [heq]

theorem valid_execution_bounded_price_strictness_s238_oai
    {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    {steps q : ℕ} (v lam eta T : ℝ)
    (E : ValidExecution D X steps v lam eta) (cluster : Fin q ↪ D) (i : X)
    (hq : 0 < q) (hi : i ∈ E.regular)
    (hv : 0 < v) (hv1 : v < 1 / 6) (hlam : 0 < lam) (hT : 0 < T)
    (hP : 0 < ∑ j, dist i (E.location (cluster j)))
    (hprice : lam ≤ T * ∑ j, dist i (E.location (cluster j)))
    (hsmall : v ^ 2 ≤ ((1 / (200 * (T + 2))) ^ 2 / 100) / (6 * (T + 2))) :
    (∑ j, (E.state steps).budget (cluster j)) ≤
      lam + (2 - ((1 / (200 * (T + 2))) ^ 2 / 100) / 2) *
        ∑ j, dist i (E.location (cluster j)) := by
  classical
  let R := E.removalReplay hv hv1 hlam
  let σ := Tuple.sort (fun j => R.removal (cluster j))
  let selected : Fin q ↪ D := σ.toEmbedding.trans cluster
  have horder : Monotone (fun j => R.removal (selected j)) :=
    Tuple.monotone_sort (fun j => R.removal (cluster j))
  have hcost : (∑ j, dist i (R.location (selected j))) =
      ∑ j, dist i (E.location (cluster j)) := by
    change (∑ j, (fun k => dist i (E.location (cluster k))) (σ j)) = _
    exact Equiv.sum_comp σ (fun k : Fin q => dist i (E.location (cluster k)))
  have hbudget : (∑ j, R.budget (selected j)) =
      ∑ j, (E.state steps).budget (cluster j) := by
    change (∑ j, (fun k => (E.state steps).budget (cluster k)) (σ j)) = _
    exact Equiv.sum_comp σ (fun k : Fin q => (E.state steps).budget (cluster k))
  have hgap : v ^ 2 ≤ strictnessGap T / (6 * (T + 2)) := hsmall
  have hbound := replay_bounded_price_strictness steps q hq T lam (3 * v) v hT hlam.le
    (by linarith only [hv]) (by linarith only [hv1]) hv (by linarith only [hv1])
    hgap R i hi selected horder (hcost ▸ hP) (hcost ▸ hprice)
  rw [hbudget, hcost] at hbound
  exact hbound

end MetricKMedianRecovery

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.MetricKMedianRecovery.valid_execution_bounded_price_strictness_s238_oai.{u_1, u_2} := @OAI.MetricKMedianRecovery.valid_execution_bounded_price_strictness_s238_oai.{u_1, u_2}
