-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_bounded_implies_mass_at_most_one_if_comparison_and_drift
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:18:03.086216+00:00
-- url     : https://prove2.me/submissions/3e1c005e-773a-49ca-96fe-a92621a34768

import Theorems.Thm_KSATSingleFlip_Connect_soft_field_iterates_well_defined
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_mass_potential_comparison
import Theorems.Thm_KSATSingleFlip_Connect_soft_field_monotone_iterates_if_order_preserved
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect
open scoped ENNReal

private theorem large_growth (m h γ : ℝ) (hm : 8 ≤ m) (hh : c0*m ≤ h) (hγ : γ ≤ 1) :
    m + 1 ≤ Real.exp (-γ)*Real.exp h := by
  have hr : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hr2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hc : (4/5:ℝ) ≤ c0 := by unfold c0; nlinarith
  have hh' : (4/5:ℝ)*m ≤ h := by nlinarith [mul_nonneg (sub_nonneg.mpr hc) (show 0 ≤ m by linarith)]
  have hx : 0 ≤ -γ+h := by linarith
  have he := Real.add_one_le_exp ((-γ+h)/2)
  have he0 : 0 ≤ Real.exp ((-γ+h)/2) := le_of_lt (Real.exp_pos _)
  have heq : Real.exp (-γ+h) = (Real.exp ((-γ+h)/2))^2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hs : (1+(-γ+h)/2)^2 ≤ Real.exp (-γ+h) := by rw [heq]; nlinarith
  have ht : (1/2+(2/5:ℝ)*m)^2 ≤ (1+(-γ+h)/2)^2 := by
    have ha : 0 ≤ (1/2+(2/5:ℝ)*m) := by linarith
    have hb : (1/2+(2/5:ℝ)*m) ≤ 1+(-γ+h)/2 := by linarith
    nlinarith
  have hscalar : m+1 ≤ (1/2+(2/5:ℝ)*m)^2 := by nlinarith [sq_nonneg (m-8)]
  rw [← Real.exp_add]
  exact hscalar.trans (ht.trans hs)

theorem solution
    (hpres : ∀ (β : ℝ) (ν' ν : Measure ℝ), 0 ≤ β →
      Measure.map (fun z : ℝ => -z) ν' = ν' →
      Measure.map (fun z : ℝ => -z) ν = ν →
      (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν') ≠ ∞ →
      (∫⁻ z, ENNReal.ofReal (Real.cosh z) ∂ν) ≠ ∞ →
      softFieldLE ν' ν → softFieldLE (Rbeta β ν') (Rbeta β ν))
    (hdrift : ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 < 1/10 ∧ ∀ (γ ε : ℝ) (r : ℕ),
      γ ≤ 1 → 0 < ε → ε ≤ ε0 → 1 ≤ r →
      (massM (nuIter γ r)).toReal ≤ 16 →
      1 + ε ≤ (massM (nuIter γ (r+1))).toReal →
      ε^2/7 ≤ hPot (nuIter γ (r+1)) - hPot (nuIter γ r)) :
    ∀ γ : ℝ, (⨆ r : ℕ, mIter γ r) < ∞ → ∀ r : ℕ, mIter γ r ≤ 1 := by
  intro γ hbound
  let m : ℕ → ℝ := fun r => (massM (nuIter γ r)).toReal
  let h : ℕ → ℝ := fun r => hPot (nuIter γ r)
  have hrec : ∀ r, m (r+1) = Real.exp (-γ)*Real.exp (h r) := by
    intro r
    exact (soft_field_iterates_well_defined γ r).2.2.2.1
  have hpot : ∀ r, c0*m r ≤ h r ∧ h r ≤ m r := by
    intro r
    letI : IsFiniteMeasure (nuIter γ r) := (soft_field_iterates_well_defined γ r).1
    exact soft_field_mass_potential_comparison _
  have hmass0 : m 0 = 0 := by simp [m,nuIter,massM]
  have hn : ∀ r, 0 ≤ m r := fun _ => ENNReal.toReal_nonneg
  have hmonoH : Monotone h := by
    apply monotone_nat_of_le_succ
    intro r
    exact (soft_field_monotone_iterates_if_order_preserved hpres γ r).2.1
  have hmonoM : Monotone m := by
    apply monotone_nat_of_le_succ
    intro r
    cases r with
    | zero => rw [hmass0]; exact hn 1
    | succ r =>
      rw [hrec r, hrec (r+1)]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
      exact Real.exp_le_exp.mpr (hmonoH (by omega))
  have hrealBound : ∀ r, m r ≤ ((⨆ r : ℕ, mIter γ r).toReal) := by
    intro r
    exact ENNReal.toReal_mono (ne_top_of_lt hbound) (le_iSup (mIter γ) r)
  have hone : ∀ r, m r ≤ 1 := by
    by_cases hγ : 1 ≤ γ
    · intro r
      induction r with
      | zero => rw [hmass0]; norm_num
      | succ r ih =>
        rw [hrec r, ← Real.exp_add]
        apply Real.exp_le_one_iff.mpr
        have hp := (hpot r).2
        linarith
    · have hγ' : γ ≤ 1 := le_of_lt (lt_of_not_ge hγ)
      have hsmall : ∀ r, m r < 8 := by
        intro r
        by_contra hh
        have hr : 8 ≤ m r := le_of_not_gt hh
        have hg : ∀ n : ℕ, 8+(n:ℝ) ≤ m (r+n) := by
          intro n
          induction n with
          | zero => simpa using hr
          | succ n ih =>
            have hn8 : 8 ≤ m (r+n) := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
            have ht := large_growth (m (r+n)) (h (r+n)) γ hn8 (hpot (r+n)).1 hγ'
            have he := hrec (r+n)
            have he' : r + n + 1 = r + n.succ := by omega
            rw [he'] at he
            rw [he]
            push_cast
            linarith
        obtain ⟨n,hn⟩ := exists_nat_gt (((⨆ r : ℕ, mIter γ r).toReal))
        have hl := hg n
        have hu := hrealBound (r+n)
        linarith
      intro s
      by_contra hs
      have hs' : 1 < m s := lt_of_not_ge hs
      obtain ⟨ε0,hε0,_,hdr⟩ := hdrift
      let ε : ℝ := min ε0 (m s-1)/2
      have hε : 0 < ε := by dsimp [ε]; positivity
      have hε0' : ε ≤ ε0 := by dsimp [ε]; have := min_le_left ε0 (m s-1); linarith
      have hεs : 1+ε ≤ m s := by dsimp [ε]; have := min_le_right ε0 (m s-1); linarith
      let δ : ℝ := ε^2/7
      have hδ : 0 < δ := by dsimp [δ]; positivity
      have hg : ∀ n : ℕ, h (s+1)+(n:ℝ)*δ ≤ h (s+1+n) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          have hr : 1 ≤ s+1+n := by omega
          have hmr : m (s+1+n) ≤ 16 := le_of_lt ((hsmall (s+1+n)).trans_le (by norm_num))
          have hmn : 1+ε ≤ m ((s+1+n)+1) := hεs.trans (hmonoM (by omega))
          have ht := hdr γ ε (s+1+n) hγ' hε hε0' hr hmr hmn
          change δ ≤ h ((s+1+n)+1) - h (s+1+n) at ht
          have he : (s+1+n)+1 = s+1+n.succ := by omega
          rw [he] at ht
          push_cast
          linarith
      obtain ⟨n,hn⟩ := exists_nat_gt ((8-h (s+1))/δ)
      have hn' := (div_lt_iff₀ hδ).mp hn
      have hl := hg n
      have hu := (hpot (s+1+n)).2
      have hm := hsmall (s+1+n)
      nlinarith
  intro r
  letI : IsFiniteMeasure (nuIter γ r) := (soft_field_iterates_well_defined γ r).1
  have hf : massM (nuIter γ r) ≠ ∞ := measure_ne_top (nuIter γ r) Set.univ
  change massM (nuIter γ r) ≤ 1
  apply (ENNReal.toReal_le_toReal hf ENNReal.one_ne_top).mp
  simpa [m] using hone r
