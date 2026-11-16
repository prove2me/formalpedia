-- Prove2me | solution 1 for MixedORAM.PublicRead.lemma_A_5
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-11-16T04:07:09.709644+00:00
-- url     : https://prove2.me/submissions/63b9e4c0-9d0e-4085-ac12-988615d79507

import Mathlib

namespace MixedORAM.PublicRead

/-- Integer form of the geometric-sum identity used to bound the epoch charges. -/
theorem a5_geom_sum_int (rho i : ℕ) :
    (∑ j ∈ Finset.range i, (rho : ℤ) ^ j) * ((rho : ℤ) - 1) = (rho : ℤ) ^ i - 1 := by
  simpa using geom_sum_mul (rho : ℤ) i

end MixedORAM.PublicRead

namespace MixedORAM.PublicRead

theorem a5_card_bound (ell0 rho : ℕ) (v1 v2 : ℤ) (hvrange : v1 < v2)
    (i : ℕ) (F : Finset ℤ)
    (hF : ∀ e ∈ F,
      e - (ell0 * ∑ j ∈ Finset.range i, rho ^ j) - (ell0 * rho ^ i) + 1 ≤ v1 ∧
      v1 ≤ e - (ell0 * ∑ j ∈ Finset.range i, rho ^ j) ∧
      e - (ell0 * ∑ j ∈ Finset.range i, rho ^ j) + 1 ≤ v2 ∧
      v2 ≤ e) :
    (F.card : ℤ) ≤ min (v2 - v1)
      (min (ell0 * rho ^ i)
        (ell0 * ∑ j ∈ Finset.range i, rho ^ j)) := by
  let s : ℤ := ell0 * ∑ j ∈ Finset.range i, rho ^ j
  let l : ℤ := ell0 * rho ^ i
  let lo : ℤ := max v2 (v1 + s)
  let hi : ℤ := min (v2 + s - 1) (v1 + s + l - 1)
  by_cases hFe : F = ∅
  · simp [hFe]
    have hz : 0 ≤ v2 - v1 := by omega
    have hl : 0 ≤ l := by positivity
    have hs : 0 ≤ s := by positivity
    simpa [s, l] using (le_min hz (le_min hl hs))
  · have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hFe
    obtain ⟨e, he⟩ := hFne
    have heok := hF e he
    have hlohi : lo ≤ hi := by
      dsimp [lo, hi, s, l]
      rcases heok with ⟨h1,h2,h3,h4⟩
      simp only [max_le_iff, le_min_iff]
      constructor <;> constructor <;> omega
    have hwidthz : hi - lo + 1 ≤ v2 - v1 := by
      dsimp [lo, hi, s, l]
      rcases heok with ⟨h1,h2,h3,h4⟩
      omega
    have hwidthl : hi - lo + 1 ≤ (ell0 * rho ^ i : ℕ) := by
      dsimp [lo, hi, s, l]
      rcases heok with ⟨h1,h2,h3,h4⟩
      omega
    have hwidths : hi - lo + 1 ≤ (ell0 * ∑ j ∈ Finset.range i, rho ^ j : ℕ) := by
      dsimp [lo, hi, s, l]
      rcases heok with ⟨h1,h2,h3,h4⟩
      omega
    have hsub : F ⊆ Finset.Icc lo hi := by
      intro x hx
      have hxok := hF x hx
      rcases hxok with ⟨h1,h2,h3,h4⟩
      rw [Finset.mem_Icc]
      constructor
      · dsimp [lo, s]
        exact max_le (by omega) (by omega)
      · dsimp [hi, s, l]
        exact le_min (by omega) (by omega)
    have hc := Finset.card_le_card hsub
    have hci : ((Finset.Icc lo hi).card : ℤ) = hi - lo + 1 := by
      rw [Int.card_Icc]
      omega
    have hz : (F.card : ℤ) ≤ v2 - v1 := by omega
    have hl : (F.card : ℤ) ≤ (ell0 * rho ^ i : ℕ) := by omega
    have hs : (F.card : ℤ) ≤ (ell0 * ∑ j ∈ Finset.range i, rho ^ j : ℕ) := by omega
    simpa [s, l] using (min_le_min hz (min_le_min hl hs))

end MixedORAM.PublicRead

namespace MixedORAM.PublicRead

theorem a5_growth_bound (ell0 rho : ℕ) (v1 v2 : ℤ) (i : ℕ)
    (h : ∃ e : ℤ,
      e - (ell0 * ∑ j ∈ Finset.range i, rho ^ j) - (ell0 * rho ^ i) + 1 ≤ v1 ∧
      v1 ≤ e - (ell0 * ∑ j ∈ Finset.range i, rho ^ j) ∧
      e - (ell0 * ∑ j ∈ Finset.range i, rho ^ j) + 1 ≤ v2 ∧
      v2 ≤ e) :
    v2 - v1 ≤ (ell0 * rho ^ i) +
      (ell0 * ∑ j ∈ Finset.range i, rho ^ j) := by
  rcases h with ⟨e, h1, h2, h3, h4⟩
  omega

end MixedORAM.PublicRead

namespace MixedORAM.PublicRead

theorem a5_first_two (ell0 rho : ℕ) (hrho : 2 ≤ rho) (v1 v2 : ℤ) (hvrange : v1 < v2) :
    let z : ℤ := v2 - v1
    let ell : ℕ → ℕ := fun i => ell0 * rho ^ i
    let s : ℕ → ℕ := fun i => ell0 * ∑ j ∈ Finset.range i, rho ^ j
    let ok : ℕ → ℤ → Prop := fun i e =>
      e - s i - ell i + 1 ≤ v1 ∧ v1 ≤ e - s i ∧ e - s i + 1 ≤ v2 ∧ v2 ≤ e
    (∀ (i : ℕ) (F : Finset ℤ), (∀ e ∈ F, ok i e) →
      (F.card : ℤ) ≤ min z (min (ell i : ℤ) (s i : ℤ))) ∧
    (∀ (i : ℕ) (e : ℤ), ok i e → z ≤ (ell i : ℤ) + (s i : ℤ)) := by
  dsimp only
  constructor
  · intro i F hF
    exact a5_card_bound ell0 rho v1 v2 hvrange i F hF
  · intro i e he
    exact a5_growth_bound ell0 rho v1 v2 i ⟨e, he.1, he.2.1, he.2.2.1, he.2.2.2⟩

end MixedORAM.PublicRead

namespace MixedORAM.PublicRead

theorem a5_s_geometric_relation (ell0 rho i : ℕ) :
    ((ell0 * (∑ j ∈ Finset.range i, rho ^ j) : ℕ) : ℤ) * ((rho : ℤ) - 1) =
      ((ell0 * rho ^ i : ℕ) : ℤ) - ell0 := by
  simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_pow, Nat.cast_ofNat]
  rw [mul_assoc, geom_sum_mul]
  ring

end MixedORAM.PublicRead

namespace MixedORAM.PublicRead

theorem a5_span_ratio_bound (ell0 rho i : ℕ) (hrho : 2 ≤ rho) :
    (ell0 * (∑ j ∈ Finset.range i, rho ^ j) : ℝ) * ((rho : ℝ) - 1) ≤
      (ell0 * rho ^ i : ℕ) := by
  have hInt := a5_s_geometric_relation ell0 rho i
  have hReal :
      (ell0 * (∑ j ∈ Finset.range i, rho ^ j) : ℝ) * ((rho : ℝ) - 1) =
        (ell0 * rho ^ i : ℕ) - ell0 := by
    exact_mod_cast hInt
  rw [hReal]
  have h0 : (0 : ℝ) ≤ ell0 := by positivity
  linarith

end MixedORAM.PublicRead

namespace MixedORAM.PublicRead

theorem a5_span_succ (ell0 rho i : ℕ) :
    ell0 * (∑ j ∈ Finset.range (i + 1), rho ^ j) =
      ell0 * (∑ j ∈ Finset.range i, rho ^ j) + ell0 * rho ^ i := by
  rw [Finset.sum_range_succ]
  simp [Nat.mul_add]

theorem a5_epoch_succ (ell0 rho i : ℕ) :
    ell0 * rho ^ (i + 1) = rho * (ell0 * rho ^ i) := by
  rw [pow_succ]
  ring

end MixedORAM.PublicRead

namespace MixedORAM.PublicRead

theorem a5_active_next_span (ell0 rho i z : ℕ)
    (hz : z ≤ ell0 * rho ^ i + ell0 * (∑ j ∈ Finset.range i, rho ^ j)) :
    z ≤ ell0 * (∑ j ∈ Finset.range (i + 1), rho ^ j) := by
  rw [a5_span_succ]
  omega

end MixedORAM.PublicRead

namespace MixedORAM.PublicRead

theorem a5_term_ratio_bound {z l s rho : ℝ} (hrho : 2 ≤ rho) (hl : 0 < l)
    (hs : s * (rho - 1) ≤ l) : min z (min l s) / l ≤ 1 / (rho - 1) := by
  have hr : 0 < rho - 1 := by linarith
  have hmin : min z (min l s) ≤ s := (min_le_right z _).trans (min_le_right l s)
  calc
    min z (min l s) / l ≤ s / l := div_le_div_of_nonneg_right hmin (le_of_lt hl)
    _ ≤ 1 / (rho - 1) := (div_le_div_iff₀ hl hr).2 (by nlinarith)

end MixedORAM.PublicRead

namespace MixedORAM.PublicRead

theorem a5_small_epoch_no_active (ell0 rho z i : ℕ) (hrho : 2 ≤ rho)
    (hz : 0 < z) (hsmall : (ell0 * rho ^ i : ℝ) < (z : ℝ) / 2) :
    ¬ z ≤ ell0 * rho ^ i + ell0 * (∑ j ∈ Finset.range i, rho ^ j) := by
  let ell : ℕ := ell0 * rho ^ i
  let s : ℕ := ell0 * ∑ j ∈ Finset.range i, rho ^ j
  have hrhoR : (1 : ℝ) ≤ (rho : ℝ) - 1 := by
    have hrhoR' : (2 : ℝ) ≤ (rho : ℝ) := by exact_mod_cast hrho
    linarith
  have hsrel : (s : ℝ) * ((rho : ℝ) - 1) ≤ (ell : ℝ) := by
    simpa [s, ell] using a5_span_ratio_bound ell0 rho i hrho
  have hsle : (s : ℝ) ≤ (ell : ℝ) := by
    have hs0 : (0 : ℝ) ≤ (s : ℝ) := by positivity
    nlinarith
  have hsmall' : (ell : ℝ) < (z : ℝ) / 2 := by simpa [ell] using hsmall
  intro hactive
  have hactive' : (z : ℝ) ≤ (ell : ℝ) + (s : ℝ) := by
    exact_mod_cast hactive
  have hz' : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  have : (z : ℝ) < (z : ℝ) := by nlinarith
  exact (lt_irrefl _ this)

end MixedORAM.PublicRead

namespace MixedORAM.PublicRead

/-- Geometric growth leaves at most three epochs in the middle-size window
    `[z/2, ρz]`, uniformly in the prefix length. -/
theorem a5_middle_epoch_count (ell0 rho K : ℕ) (z : ℤ) (hrho : 2 ≤ rho)
    (hz : 0 < z) :
    ((Finset.range K).filter (fun i =>
      (z : ℝ) / 2 ≤ (ell0 : ℝ) * (rho : ℝ) ^ i ∧
      (ell0 : ℝ) * (rho : ℝ) ^ i ≤ (rho : ℝ) * z)).card ≤ 3 := by
  let E := (Finset.range K).filter (fun i =>
    (z : ℝ) / 2 ≤ (ell0 : ℝ) * (rho : ℝ) ^ i ∧
    (ell0 : ℝ) * (rho : ℝ) ^ i ≤ (rho : ℝ) * z)
  by_cases hE : E = ∅
  · simp [E, hE]
  · have hEn : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hE
    let i0 := E.min' hEn
    have hi0 : i0 ∈ E := by simpa [i0] using Finset.min'_mem E hEn
    have hsubset : E ⊆ Finset.Icc i0 (i0 + 2) := by
      intro i hi
      rw [Finset.mem_Icc]
      constructor
      · exact Finset.min'_le E i hi
      · by_contra hn
        have hgap : i0 + 3 ≤ i := by omega
        have ha : (1 : ℝ) ≤ (rho : ℝ) := by exact_mod_cast (show 1 ≤ rho by omega)
        have hpow : (rho : ℝ) ^ (i0 + 3) ≤ (rho : ℝ) ^ i :=
          pow_le_pow_right₀ ha hgap
        have hscale :
            ((ell0 : ℝ) * (rho : ℝ) ^ i0) * (rho : ℝ) ^ 3 ≤
              (ell0 : ℝ) * (rho : ℝ) ^ i := by
          calc
            _ = (ell0 : ℝ) * (rho : ℝ) ^ (i0 + 3) := by rw [pow_add]; ring
            _ ≤ (ell0 : ℝ) * (rho : ℝ) ^ i := mul_le_mul_of_nonneg_left hpow (by positivity)
        have hi0mem : (z : ℝ) / 2 ≤ (ell0 : ℝ) * (rho : ℝ) ^ i0 := (Finset.mem_filter.mp hi0).2.1
        have himem : (ell0 : ℝ) * (rho : ℝ) ^ i ≤ (rho : ℝ) * z := (Finset.mem_filter.mp hi).2.2
        have hrhoR : (2 : ℝ) ≤ (rho : ℝ) := by exact_mod_cast hrho
        have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
        have hrhoSq : (4 : ℝ) ≤ (rho : ℝ) ^ 2 := by nlinarith [sq_nonneg ((rho : ℝ) - 2)]
        have hpos : (0 : ℝ) ≤ (rho : ℝ) := by linarith
        have hfour : 4 * (rho : ℝ) ≤ (rho : ℝ) ^ 3 := by
          have := mul_le_mul_of_nonneg_left hrhoSq hpos
          nlinarith
        have hcontr : (rho : ℝ) * z < ((z : ℝ) / 2) * (rho : ℝ) ^ 3 := by nlinarith [hfour, hzR]
        nlinarith
    have hcard : (Finset.Icc i0 (i0 + 2)).card = 3 := by simp; omega
    calc
      E.card ≤ (Finset.Icc i0 (i0 + 2)).card := Finset.card_le_card hsubset
      _ = 3 := hcard

end MixedORAM.PublicRead

namespace MixedORAM.PublicRead

/-- The normalized per-edge charge at epoch `i`. -/
noncomputable def a5_charge (ell0 rho : ℕ) (z : ℤ) (i : ℕ) : ℝ :=
  ((min z (min (ell0 * rho ^ i : ℤ)
    (ell0 * (∑ j ∈ Finset.range i, rho ^ j) : ℤ)) : ℤ) : ℝ) /
    (ell0 * rho ^ i : ℝ)

/-- The middle-size epochs contribute at most a universal `6 / ρ`. -/
theorem a5_middle_epoch_charge (ell0 rho K : ℕ) (z : ℤ)
    (hrho : 2 ≤ rho) (hz : 0 < z) :
    (∑ i ∈ (Finset.range K).filter (fun i =>
        (z : ℝ) / 2 ≤ (ell0 : ℝ) * (rho : ℝ) ^ i ∧
        (ell0 : ℝ) * (rho : ℝ) ^ i ≤ (rho : ℝ) * z),
      a5_charge ell0 rho z i) ≤ 6 / (rho : ℝ) := by
  let E := (Finset.range K).filter (fun i =>
    (z : ℝ) / 2 ≤ (ell0 : ℝ) * (rho : ℝ) ^ i ∧
    (ell0 : ℝ) * (rho : ℝ) ^ i ≤ (rho : ℝ) * z)
  have hcard : E.card ≤ 3 := by
    simpa [E] using a5_middle_epoch_count ell0 rho K z hrho hz
  have hrhoR : (2 : ℝ) ≤ (rho : ℝ) := by exact_mod_cast hrho
  have hrhoPos : (0 : ℝ) < (rho : ℝ) := by linarith
  have hdenPos : (0 : ℝ) < (rho : ℝ) - 1 := by linarith
  have hsum := Finset.sum_le_card_nsmul E (fun i => a5_charge ell0 rho z i)
      (1 / ((rho : ℝ) - 1)) ?_
  have hlast : (E.card : ℝ) * (1 / ((rho : ℝ) - 1)) ≤ 3 * (1 / ((rho : ℝ) - 1)) := by
    have hc : (E.card : ℝ) ≤ 3 := by exact_mod_cast hcard
    exact mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ 1 / ((rho : ℝ) - 1))
  have hconst : 3 / ((rho : ℝ) - 1) ≤ 6 / (rho : ℝ) :=
    (div_le_div_iff₀ hdenPos hrhoPos).2 (by nlinarith)
  calc
    _ ≤ (E.card : ℝ) * (1 / ((rho : ℝ) - 1)) := by simpa [E] using hsum
    _ ≤ 3 * (1 / ((rho : ℝ) - 1)) := hlast
    _ = 3 / ((rho : ℝ) - 1) := by ring
    _ ≤ 6 / (rho : ℝ) := hconst
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    let ell : ℕ := ell0 * rho ^ i
    let s : ℕ := ell0 * ∑ j ∈ Finset.range i, rho ^ j
    have hellpos : (0 : ℝ) < (ell : ℝ) := by
      have hlow := hi'.1
      have hlow' : (z : ℝ) / 2 ≤ (ell : ℝ) := by simpa [ell] using hlow
      have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
      linarith
    have hspan : (s : ℝ) * ((rho : ℝ) - 1) ≤ (ell : ℝ) := by
      simpa [s, ell] using a5_span_ratio_bound ell0 rho i hrho
    simpa [a5_charge, ell, s] using
      a5_term_ratio_bound (z := (z : ℝ)) (l := (ell : ℝ)) (s := (s : ℝ))
        (rho := (rho : ℝ)) hrhoR hellpos hspan

end MixedORAM.PublicRead

namespace MixedORAM.PublicRead

/-- A geometric tail starting at the first large epoch is bounded uniformly. -/
theorem a5_inverse_geometric_tail (rho m n : ℕ) (hrho : 2 ≤ rho) :
    ∑ i ∈ Finset.Ico m n, (1 / (rho : ℝ)) ^ (i - m + 1) ≤ 2 / (rho : ℝ) := by
  let q : ℝ := 1 / (rho : ℝ)
  have hrhoR : (2 : ℝ) ≤ (rho : ℝ) := by exact_mod_cast hrho
  have hrhoPos : (0 : ℝ) < (rho : ℝ) := by linarith
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hq0 : 0 ≤ q := le_of_lt hqpos
  have hq1 : q < 1 := by dsimp [q]; rw [div_lt_one hrhoPos]; norm_num; linarith
  have hgeom : (∑ j ∈ Finset.range (n - m), q ^ j) ≤ 1 / (1 - q) := by
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n - m) hq0 hq1
    simpa using h
  have hrewrite :
      (∑ i ∈ Finset.Ico m n, q ^ (i - m + 1)) =
        q * ∑ j ∈ Finset.range (n - m), q ^ j := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp_rw [Nat.add_sub_cancel_left, pow_succ]
    rw [← Finset.sum_mul]
    ring
  calc
    _ = q * ∑ j ∈ Finset.range (n - m), q ^ j := by simpa [q] using hrewrite
    _ ≤ q * (1 / (1 - q)) := mul_le_mul_of_nonneg_left hgeom hq0
    _ = q / (1 - q) := by ring
    _ = (1 / (rho : ℝ)) / (1 - 1 / (rho : ℝ)) := by rfl
    _ ≤ 2 / (rho : ℝ) := by
      have hdenPos : (0 : ℝ) < (rho : ℝ) - 1 := by linarith
      have hratio : 1 / ((rho : ℝ) - 1) ≤ 2 / (rho : ℝ) :=
        (div_le_div_iff₀ hdenPos hrhoPos).2 (by nlinarith)
      have hEq : (1 / (rho : ℝ)) / (1 - 1 / (rho : ℝ)) = 1 / ((rho : ℝ) - 1) := by
        field_simp
      rw [hEq]
      exact hratio

end MixedORAM.PublicRead

namespace MixedORAM.PublicRead

/-- The large-size epochs contribute at most the geometric tail `2 / ρ`. -/
theorem a5_large_epoch_charge (ell0 rho K : ℕ) (z : ℤ)
    (hrho : 2 ≤ rho) (hz : 0 < z) :
    (∑ i ∈ (Finset.range K).filter (fun i =>
        (rho : ℝ) * z < (ell0 : ℝ) * (rho : ℝ) ^ i),
      a5_charge ell0 rho z i) ≤ 2 / (rho : ℝ) := by
  let E := (Finset.range K).filter (fun i =>
    (rho : ℝ) * z < (ell0 : ℝ) * (rho : ℝ) ^ i)
  let q : ℝ := 1 / (rho : ℝ)
  by_cases hE : E = ∅
  · simp [E, hE]
    positivity
  · have hEn : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hE
    let i0 := E.min' hEn
    have hi0 : i0 ∈ E := by simpa [i0] using Finset.min'_mem E hEn
    have hsub : E ⊆ Finset.Ico i0 K := by
      intro i hi
      rw [Finset.mem_Ico]
      constructor
      · exact Finset.min'_le E i hi
      · exact Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hterm : ∀ i ∈ E, a5_charge ell0 rho z i ≤ q ^ (i - i0 + 1) := by
      intro i hi
      have hi0le : i0 ≤ i := Finset.min'_le E i hi
      have hbase : (rho : ℝ) * z < (ell0 : ℝ) * (rho : ℝ) ^ i0 :=
        (Finset.mem_filter.mp hi0).2
      have hlarge : (rho : ℝ) * z < (ell0 : ℝ) * (rho : ℝ) ^ i :=
        (Finset.mem_filter.mp hi).2
      let ell0i : ℝ := (ell0 : ℝ) * (rho : ℝ) ^ i0
      let elli : ℝ := (ell0 : ℝ) * (rho : ℝ) ^ i
      let k : ℕ := i - i0
      have hrhoPos : (0 : ℝ) < (rho : ℝ) := by exact_mod_cast (show 0 < rho by omega)
      have hellpos : (0 : ℝ) < elli := by
        have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
        have hprodpos : (0 : ℝ) < (rho : ℝ) * z := mul_pos hrhoPos hzR
        exact lt_trans hprodpos (by simpa [elli] using hlarge)
      have hpow : (rho : ℝ) ^ i0 * (rho : ℝ) ^ k = (rho : ℝ) ^ i := by
        have hk : i0 + k = i := by simp [k, Nat.add_sub_of_le hi0le]
        rw [← hk, pow_add]
      have hscale : (rho : ℝ) * z * (rho : ℝ) ^ k < elli := by
        calc
          _ < ell0i * (rho : ℝ) ^ k := mul_lt_mul_of_pos_right hbase (pow_pos hrhoPos k)
          _ = elli := by dsimp [ell0i, elli]; rw [← hpow]; ring
      have hprod : (rho : ℝ) * (rho : ℝ) ^ k = (rho : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
      have hdiv : (z : ℝ) / elli < 1 / (rho : ℝ) ^ (k + 1) :=
        (div_lt_div_iff₀ hellpos (pow_pos hrhoPos (k + 1))).2 (by rw [mul_comm] at hscale; nlinarith [hscale, hprod])
      have hqpow : q ^ (k + 1) = 1 / (rho : ℝ) ^ (k + 1) := by simp [q, div_pow]
      have hnum : ((min z (min (ell0 * rho ^ i : ℤ)
          (ell0 * (∑ j ∈ Finset.range i, rho ^ j) : ℤ)) : ℤ) : ℝ) ≤ (z : ℝ) := by
        exact_mod_cast (min_le_left z _)
      have hcharge : a5_charge ell0 rho z i ≤ (z : ℝ) / elli := by
        dsimp [a5_charge, elli]
        exact div_le_div_of_nonneg_right hnum (le_of_lt hellpos)
      dsimp [q, k]
      rw [hqpow]
      exact le_of_lt (hcharge.trans_lt hdiv)
    have hsum1 :
        (∑ i ∈ E, a5_charge ell0 rho z i) ≤ ∑ i ∈ E, q ^ (i - i0 + 1) :=
      Finset.sum_le_sum hterm
    have hsum2 : (∑ i ∈ E, q ^ (i - i0 + 1)) ≤
        ∑ i ∈ Finset.Ico i0 K, q ^ (i - i0 + 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro i hi hnot; positivity)
    calc
      _ = ∑ i ∈ E, a5_charge ell0 rho z i := by simp [E]
      _ ≤ ∑ i ∈ E, q ^ (i - i0 + 1) := hsum1
      _ ≤ ∑ i ∈ Finset.Ico i0 K, q ^ (i - i0 + 1) := hsum2
      _ ≤ 2 / (rho : ℝ) := by simpa [q] using a5_inverse_geometric_tail rho i0 K hrho

end MixedORAM.PublicRead

namespace MixedORAM.PublicRead

theorem a5_total_charge (ell0 rho K : ℕ) (z : ℤ)
    (hrho : 2 ≤ rho) (hz : 0 < z) :
    (∑ i ∈ (Finset.range K).filter (fun i =>
      z ≤ (ell0 * rho ^ i : ℕ) + ell0 * (∑ j ∈ Finset.range i, rho ^ j)),
      a5_charge ell0 rho z i) ≤ 8 / (rho : ℝ) := by
  let zN : ℕ := z.toNat
  have hzn : (zN : ℤ) = z := Int.toNat_of_nonneg (le_of_lt hz)
  have hzN : 0 < zN := by
    have : (0 : ℤ) < (zN : ℤ) := by simpa [hzn] using hz
    omega
  let A := (Finset.range K).filter (fun i =>
    z ≤ (ell0 * rho ^ i : ℕ) + ell0 * (∑ j ∈ Finset.range i, rho ^ j))
  let M := (Finset.range K).filter (fun i =>
    (z : ℝ) / 2 ≤ (ell0 : ℝ) * (rho : ℝ) ^ i ∧
    (ell0 : ℝ) * (rho : ℝ) ^ i ≤ (rho : ℝ) * z)
  let L := (Finset.range K).filter (fun i =>
    (rho : ℝ) * z < (ell0 : ℝ) * (rho : ℝ) ^ i)
  have hsub : A ⊆ M ∪ L := by
    intro i hi
    have hirange : i ∈ Finset.range K := (Finset.mem_filter.mp hi).1
    have hactive := (Finset.mem_filter.mp hi).2
    have hsmallActive : zN ≤ ell0 * rho ^ i + ell0 * ∑ j ∈ Finset.range i, rho ^ j := by
      have hzcast : (zN : ℤ) = z := hzn
      have hcast : (zN : ℤ) ≤ (ell0 * rho ^ i : ℕ) +
          (ell0 * ∑ j ∈ Finset.range i, rho ^ j : ℕ) := by
        simpa [hzcast] using hactive
      exact_mod_cast hcast
    by_cases hmidlo : (z : ℝ) / 2 ≤ (ell0 : ℝ) * (rho : ℝ) ^ i
    · by_cases hmidhi : (ell0 : ℝ) * (rho : ℝ) ^ i ≤ (rho : ℝ) * z
      · apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨hirange, ⟨hmidlo, hmidhi⟩⟩
      · apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        refine ⟨hirange, ?_⟩
        exact lt_of_not_ge hmidhi
    · have hsmall : (ell0 : ℝ) * (rho : ℝ) ^ i < (zN : ℝ) / 2 := by
        have hzreal : (zN : ℝ) = (z : ℝ) := by exact_mod_cast hzn
        simpa [hzreal] using (lt_of_not_ge hmidlo)
      have hfalse := a5_small_epoch_no_active ell0 rho zN i hrho hzN hsmall hsmallActive
      exact False.elim hfalse
  have hdisj : Disjoint M L := by
    rw [Finset.disjoint_left]
    intro i hiM hiL
    have hupper := (Finset.mem_filter.mp hiM).2.2
    have hlower := (Finset.mem_filter.mp hiL).2
    exact (lt_irrefl _ (lt_of_lt_of_le hlower hupper))
  have hnonneg : ∀ i ∈ M ∪ L, i ∉ A → 0 ≤ a5_charge ell0 rho z i := by
    intro i _ _
    have hnum : (0 : ℤ) ≤ min z (min (ell0 * rho ^ i : ℤ)
        (ell0 * (∑ j ∈ Finset.range i, rho ^ j) : ℤ)) := by
      apply le_min
      · exact le_of_lt hz
      · apply le_min <;> positivity
    have hnumR : (0 : ℝ) ≤ ((min z (min (ell0 * rho ^ i : ℤ)
        (ell0 * (∑ j ∈ Finset.range i, rho ^ j) : ℤ)) : ℤ) : ℝ) := by
      exact_mod_cast hnum
    apply div_nonneg hnumR
    positivity
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  calc
    _ = ∑ i ∈ A, a5_charge ell0 rho z i := by simp [A]
    _ ≤ ∑ i ∈ M ∪ L, a5_charge ell0 rho z i := hsum
    _ = (∑ i ∈ M, a5_charge ell0 rho z i) +
        (∑ i ∈ L, a5_charge ell0 rho z i) := by rw [Finset.sum_union hdisj]
    _ ≤ 6 / (rho : ℝ) + 2 / (rho : ℝ) :=
      add_le_add (a5_middle_epoch_charge ell0 rho K z hrho hz)
        (a5_large_epoch_charge ell0 rho K z hrho hz)
    _ = 8 / (rho : ℝ) := by ring

end MixedORAM.PublicRead

namespace MixedORAM.PublicRead

theorem a5_complete (ell0 rho : ℕ) (hrho : 2 ≤ rho) (v1 v2 : ℤ)
    (hvrange : v1 < v2) :
    let z : ℤ := v2 - v1
    let ell : ℕ → ℕ := fun i => ell0 * rho ^ i
    let s : ℕ → ℕ := fun i => ell0 * ∑ j ∈ Finset.range i, rho ^ j
    let ok : ℕ → ℤ → Prop := fun i e =>
      e - s i - ell i + 1 ≤ v1 ∧ v1 ≤ e - s i ∧
      e - s i + 1 ≤ v2 ∧ v2 ≤ e
    (∀ (i : ℕ) (F : Finset ℤ), (∀ e ∈ F, ok i e) →
      (F.card : ℤ) ≤ min z (min (ell i : ℤ) (s i : ℤ))) ∧
    (∀ (i : ℕ) (e : ℤ), ok i e → z ≤ (ell i : ℤ) + (s i : ℤ)) ∧
    ∀ K : ℕ, ∑ i ∈ (Finset.range K).filter (fun i => z ≤ (ell i : ℤ) + (s i : ℤ)),
      ((min z (min (ell i : ℤ) (s i : ℤ)) : ℤ) : ℝ) / (ell i : ℝ) ≤ 8 / (rho : ℝ) := by
  dsimp only
  have h12 := a5_first_two ell0 rho hrho v1 v2 hvrange
  have hz : 0 < v2 - v1 := by omega
  refine ⟨h12.1, h12.2, ?_⟩
  intro K
  simpa [a5_charge] using a5_total_charge ell0 rho K (v2 - v1) hrho hz

end MixedORAM.PublicRead

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (ℓ₀ ρ : ℕ), 2 ≤ ρ → ∀ v₁ v₂ : ℤ, v₁ < v₂ →
      let z : ℤ := v₂ - v₁
      let ℓ : ℕ → ℕ := fun i => ℓ₀ * ρ ^ i
      let s : ℕ → ℕ := fun i => ℓ₀ * ∑ j ∈ Finset.range i, ρ ^ j
      let ok : ℕ → ℤ → Prop := fun i e =>
        e - s i - ℓ i + 1 ≤ v₁ ∧ v₁ ≤ e - s i ∧ e - s i + 1 ≤ v₂ ∧ v₂ ≤ e
      (∀ (i : ℕ) (F : Finset ℤ), (∀ e ∈ F, ok i e) →
          (F.card : ℤ) ≤ min z (min (ℓ i : ℤ) (s i : ℤ))) ∧
        (∀ (i : ℕ) (e : ℤ), ok i e → z ≤ (ℓ i : ℤ) + s i) ∧
        ∀ K : ℕ, ∑ i ∈ (Finset.range K).filter (fun i => z ≤ (ℓ i : ℤ) + s i),
            ((min z (min (ℓ i : ℤ) (s i : ℤ)) : ℤ) : ℝ) / (ℓ i : ℝ) ≤ C / ρ := by
  refine ⟨8, by norm_num, ?_⟩
  intro ell0 rho hrho v1 v2 hv
  exact MixedORAM.PublicRead.a5_complete ell0 rho hrho v1 v2 hv

