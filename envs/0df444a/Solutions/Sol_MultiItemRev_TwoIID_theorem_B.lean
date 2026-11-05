-- Prove2me | solution 1 for MultiItemRev.TwoIID.theorem_B
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:49:14.261223+00:00
-- url     : https://prove2.me/submissions/9563c3c7-8284-476a-92cd-26484ec72e38

import Mathlib
import Definitions.Def_MultiItemRev_TwoIID_Model
import Theorems.Thm_MultiItemRev_TwoIID_proposition_6_iii
import Theorems.Thm_MultiItemRev_TwoIID_symmetrization
import Theorems.Thm_MultiItemRev_TwoIID_display_12
import Theorems.Thm_MultiItemRev_TwoIID_rhs12_le

open MeasureTheory
open scoped NNReal ENNReal

namespace TwoIIDReduction

theorem envelope_integral_le (f g : ℝ → ℝ) (hg : Monotone g) (hg1 : ∀ t, g t ≤ 1)
    (hsub : ∀ a b, 0 ≤ a → 0 ≤ b → f a + g a * (b - a) ≤ f b) (u : ℝ) (hu : 0 ≤ u) :
    ∫ t in (0 : ℝ)..u, g t ≤ f u - f 0 := by
  have g0 : ∀ t, 0 ≤ t → g 0 ≤ g t := fun t ht => hg ht
  -- for every n ≥ 1 we have ∫ ≤ f u - f 0 + (u / n) * (1 - g 0)
  have key : ∀ n : ℕ, 0 < n → ∫ t in (0 : ℝ)..u, g t ≤ f u - f 0 + (u / n) * (1 - g 0) := by
    intro n hn
    set h : ℝ := u / n with hh
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hh0 : 0 ≤ h := div_nonneg hu hnpos.le
    have hnh : (n : ℝ) * h = u := by rw [hh]; field_simp
    have hint : ∀ i : ℕ, IntervalIntegrable g volume (i * h) ((i + 1 : ℕ) * h) :=
      fun i => hg.intervalIntegrable
    have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (a := fun i : ℕ => (i : ℝ) * h) (n := n) (fun i _ => by simpa using hint i)
    simp only [Nat.cast_zero, zero_mul] at hsum
    rw [hnh] at hsum
    rw [← hsum]
    -- each piece
    have piece : ∀ i : ℕ, ∫ t in ((i : ℝ) * h)..((i + 1 : ℕ) * h), g t ≤
        f ((i + 2 : ℕ) * h) - f ((i + 1 : ℕ) * h) := by
      intro i
      have hle : (i : ℝ) * h ≤ (i + 1 : ℕ) * h := by
        push_cast; nlinarith
      have h1 : ∫ t in ((i : ℝ) * h)..((i + 1 : ℕ) * h), g t ≤
          ∫ t in ((i : ℝ) * h)..((i + 1 : ℕ) * h), g ((i + 1 : ℕ) * h) := by
        apply intervalIntegral.integral_mono_on hle (hint i) intervalIntegrable_const
        intro t ht
        exact hg ht.2
      rw [intervalIntegral.integral_const, smul_eq_mul] at h1
      have h2 := hsub ((i + 1 : ℕ) * h) ((i + 2 : ℕ) * h) (by positivity) (by positivity)
      have : ((i + 1 : ℕ) * h - i * h : ℝ) = (i + 2 : ℕ) * h - (i + 1 : ℕ) * h := by
        push_cast; ring
      rw [this] at h1
      nlinarith
    calc ∑ i ∈ Finset.range n, ∫ t in ((i : ℝ) * h)..((i + 1 : ℕ) * h), g t
        ≤ ∑ i ∈ Finset.range n, (f ((i + 2 : ℕ) * h) - f ((i + 1 : ℕ) * h)) := by
          apply Finset.sum_le_sum; intro i _; exact piece i
      _ = f ((n + 1 : ℕ) * h) - f h := by
          have := Finset.sum_range_sub (fun i : ℕ => f ((i + 1 : ℕ) * h)) n
          simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, one_mul] at this ⊢
          rw [← this]
          apply Finset.sum_congr rfl; intro i _; push_cast; ring_nf
      _ ≤ f u - f 0 + h * (1 - g 0) := by
          have e1 : ((n + 1 : ℕ) : ℝ) * h = u + h := by push_cast; linarith
          rw [e1]
          -- f (u + h) ≤ f u + h * g (u + h) ≤ f u + h
          have a1 := hsub (u + h) u (by linarith) hu
          have a2 := hsub 0 h le_rfl hh0
          have a3 := hg1 (u + h)
          have a4 := g0 (u + h) (by linarith)
          nlinarith
  -- conclude
  have hg01 : 0 ≤ 1 - g 0 := by linarith [hg1 0]
  by_contra hcon
  push_neg at hcon
  set D := (∫ t in (0 : ℝ)..u, g t) - (f u - f 0) with hD
  have hDpos : 0 < D := by rw [hD]; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (u * (1 - g 0) / D)
  have hn0 : 0 < n := by
    have : 0 ≤ u * (1 - g 0) / D := div_nonneg (mul_nonneg hu hg01) hDpos.le
    exact_mod_cast lt_of_le_of_lt this hn
  have := key n hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have : u * (1 - g 0) < n * D := by
    rw [div_lt_iff₀ hDpos] at hn; linarith
  have e : u / n * (1 - g 0) = u * (1 - g 0) / n := by ring
  have : u * (1 - g 0) / n < D := by rw [div_lt_iff₀ hnpos]; linarith
  linarith

open MultiItemRev.Decomp in
/-- For an admissible symmetric two-good mechanism, `∫_0^u φ ≤ b(u,u)/2` where
`φ(t) = q₁(t,t)`. -/
theorem diag_integral_le (M : Mechanism (Fin 2)) (hM : MultiItemRev.TwoIID.IsAdmissible M)
    (hSym : MultiItemRev.TwoIID.IsSymmetric M) (u : ℝ≥0) :
    ∫ t in (0 : ℝ)..(u : ℝ), M.q (MultiItemRev.TwoIID.diag t.toNNReal) 0 ≤
      buyerPayoff M (MultiItemRev.TwoIID.diag u) / 2 := by
  obtain ⟨hF, hIC, hIR, -⟩ := hM
  set φ : ℝ≥0 → ℝ := fun t => M.q (MultiItemRev.TwoIID.diag t) 0 with hφ
  set Φ : ℝ≥0 → ℝ := fun t => buyerPayoff M (MultiItemRev.TwoIID.diag t) with hΦ
  have hq1 : ∀ t, M.q (MultiItemRev.TwoIID.diag t) 1 = φ t := by
    intro t
    have := (hSym (MultiItemRev.TwoIID.diag t)).1
    exact this.symm
  -- subgradient inequality
  have hsub : ∀ a b : ℝ≥0, Φ a + 2 * φ a * ((b : ℝ) - a) ≤ Φ b := by
    intro a b
    have h := hIC (MultiItemRev.TwoIID.diag b) (MultiItemRev.TwoIID.diag a)
    simp only [Fin.sum_univ_two, buyerPayoff] at h
    simp only [hΦ, hφ, buyerPayoff, Fin.sum_univ_two]
    have e1 := hq1 a
    simp only [hφ] at e1
    simp only [MultiItemRev.TwoIID.diag] at h e1 ⊢
    rw [e1] at h ⊢
    nlinarith
  have hmono : Monotone φ := by
    intro a b hab
    have h1 := hsub a b
    have h2 := hsub b a
    have hab' : (a : ℝ) ≤ b := hab
    rcases eq_or_lt_of_le hab' with h | h
    · have : a = b := by exact_mod_cast h
      rw [this]
    · nlinarith
  have hΦ0 : 0 ≤ Φ 0 := hIR _
  have key := envelope_integral_le (fun s => Φ s.toNNReal / 2) (fun s => φ s.toNNReal)
    (fun a b hab => hmono (Real.toNNReal_le_toNNReal hab))
    (fun t => (hF _ 0).2)
    (by
      intro a b ha hb
      have := hsub a.toNNReal b.toNNReal
      rw [Real.coe_toNNReal _ ha, Real.coe_toNNReal _ hb] at this
      linarith)
    (u : ℝ) u.2
  simp only [Real.toNNReal_coe, Real.toNNReal_zero] at key
  have : ∫ t in (0 : ℝ)..(u : ℝ), M.q (MultiItemRev.TwoIID.diag t.toNNReal) 0 =
      ∫ t in (0 : ℝ)..(u : ℝ), φ t.toNNReal := rfl
  rw [this]
  have hΦ0' : 0 ≤ Φ 0 := hΦ0
  simp only [hΦ] at key hΦ0' ⊢
  linarith

end TwoIIDReduction

open MultiItemRev.Decomp in
theorem solution (ν : Measure ℝ≥0) [IsProbabilityMeasure ν] :
    MultiItemRev.TwoIID.Rev (Measure.pi (fun _ : Fin 2 => ν)) ≤
      ENNReal.ofReal ((Real.exp 1 + 1) / Real.exp 1) *
        (MultiItemRev.Decomp.Rev1 ν + MultiItemRev.Decomp.Rev1 ν) := by
  by_cases hr : Rev1 ν = ⊤
  · rw [hr, top_add, ENNReal.mul_top]
    · exact le_top
    · rw [Ne, ENNReal.ofReal_eq_zero, not_le]
      positivity
  rw [MultiItemRev.TwoIID.proposition_6_iii]
  refine iSup₂_le fun M hM => ?_
  obtain ⟨h1, h2, hsym, hrev⟩ := MultiItemRev.TwoIID.symmetrization ν M hM
  rw [← hrev]
  set M' := MultiItemRev.TwoIID.symmetrize M with hM'
  have hd := MultiItemRev.TwoIID.display_12 ν M' ⟨h1, h2⟩ hsym hr
  set φ : ℝ≥0 → ℝ := fun t => M'.q (MultiItemRev.TwoIID.diag t) 0 with hφ
  -- φ is monotone and in [0,1]
  have hφ01 : ∀ t, 0 ≤ φ t ∧ φ t ≤ 1 := fun t => h1.1 _ 0
  have hφmono : Monotone φ := by
    intro a b hab
    obtain ⟨-, hIC, -, -⟩ := h1
    have q1 : ∀ t, M'.q (MultiItemRev.TwoIID.diag t) 1 = φ t := fun t =>
      ((hsym (MultiItemRev.TwoIID.diag t)).1).symm
    have ha := hIC (MultiItemRev.TwoIID.diag b) (MultiItemRev.TwoIID.diag a)
    have hb := hIC (MultiItemRev.TwoIID.diag a) (MultiItemRev.TwoIID.diag b)
    have qa := q1 a
    have qb := q1 b
    simp only [hφ] at qa qb ⊢
    simp only [Fin.sum_univ_two, buyerPayoff, MultiItemRev.TwoIID.diag] at ha hb qa qb ⊢
    rw [qa] at ha hb
    rw [qb] at ha hb
    have hab' : (a : ℝ) ≤ b := hab
    rcases eq_or_lt_of_le hab' with h | h
    · have : a = b := by exact_mod_cast h
      rw [this]
    · nlinarith
  have hrhs := MultiItemRev.TwoIID.rhs12_le ν hr φ hφmono hφ01
  simp only at hd hrhs
  -- compare the two lintegrals
  have hL : (∫⁻ x, ENNReal.ofReal
          (((min (x 0) (x 1) : ℝ≥0) : ℝ) * M'.q (MultiItemRev.TwoIID.diag (x 0)) 0 -
            buyerPayoff M' (MultiItemRev.TwoIID.diag (min (x 0) (x 1))) / 2)
          ∂(Measure.pi (fun _ : Fin 2 => ν))) ≤
      ∫⁻ x, ENNReal.ofReal
        (((min (x 0) (x 1) : ℝ≥0) : ℝ) * φ (x 0) -
          ∫ t in (0 : ℝ)..(((min (x 0) (x 1) : ℝ≥0) : ℝ)), φ t.toNNReal)
          ∂(Measure.pi (fun _ : Fin 2 => ν)) := by
    apply lintegral_mono
    intro x
    apply ENNReal.ofReal_le_ofReal
    have := TwoIIDReduction.diag_integral_le M' h1 hsym (min (x 0) (x 1))
    simp only [hφ]
    linarith
  set r := (Rev1 ν).toReal with hrdef
  set A : EReal := ((2 * r - 2 * r * ∫ t, φ t ∂ν : ℝ) : EReal) with hA
  have hstep : MultiItemRev.TwoIID.expRevenue (Measure.pi (fun _ : Fin 2 => ν)) M' ≤
      ((2 * r * (1 + 1 / Real.exp 1) : ℝ) : EReal) := by
    refine le_trans hd (le_trans ?_ hrhs)
    gcongr
    · exact_mod_cast hL
  calc (MultiItemRev.TwoIID.expRevenue (Measure.pi (fun _ : Fin 2 => ν)) M').toENNReal
      ≤ (((2 * r * (1 + 1 / Real.exp 1) : ℝ) : EReal)).toENNReal :=
        EReal.toENNReal_le_toENNReal hstep
    _ = ENNReal.ofReal ((Real.exp 1 + 1) / Real.exp 1) * (Rev1 ν + Rev1 ν) := by
        rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
        have hR : Rev1 ν = ENNReal.ofReal r := (ENNReal.ofReal_toReal hr).symm
        rw [hR, ← ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have he : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
        field_simp
        ring
