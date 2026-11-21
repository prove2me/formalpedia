-- Prove2me | solution 1 for MasulloAudit.one_sided_regular_windows_iff_RH
-- status  : ACCEPTED   (prove)
-- author  : @lll
-- created : 2026-11-21T01:00:39.716702+00:00
-- url     : https://prove2.me/submissions/d368b38f-2e55-4372-9f55-0bc994e844fd

import Theorems.Thm_MasulloRH_trace_formula_rational_full_strip
import Theorems.Thm_MasulloRH_regularized_mellin_limit
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_MasulloRH_regularized_spectral_domination_any_window
import Theorems.Thm_MasulloRH_regularized_test_admissible
import Theorems.Thm_MasulloRH_single_resolvent_test
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open MeasureTheory Set Filter MasulloRH
open scoped Topology

/-- The regularized cutoff spectral sums converge to the resolvent sum
(dominated convergence, as in `Alpha0_Sol`). -/
private theorem os_spectralLimit (α : ℝ) (hα : 0 < α)
    (s : ℂ) (hs : (3 / 2 : ℝ) < s.re) :
    Tendsto (fun n : ℕ => cutoffSpectral α n s) atTop
      (𝓝 (regularizedSpectral α s)) := by
  obtain ⟨C, hC, hbound⟩ := regularized_spectral_domination_any_window α s hs
  apply tendsto_tsum_of_dominated_convergence
    ((weighted_zero_summability α hα).mul_left C)
  · intro ρ
    have hr : (ρ : ℂ).re < 1 := ρ.property.2.2.1
    have hwr : ((ρ : ℂ) - 1 / 2).re = (ρ : ℂ).re - 1 / 2 := by simp
    have hm := regularized_mellin_limit s ((ρ : ℂ) - 1 / 2)
      (by rw [hwr]; linarith) (by rw [hwr]; linarith)
    convert hm.const_mul (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) using 1 <;>
      simp only [zetaTraceTerm, zeroResolventTerm] <;> congr 3 <;> ring
  · exact .of_forall hbound

/-- When every zero of the full strip lies in the window, the window is the full strip. -/
private def os_equiv (α : ℝ)
    (h : ∀ ρ : ZetaZerosInTraceStrip (1 / 2), |(ρ : ℂ).re - 1 / 2| < α) :
    ZetaZerosInTraceStrip α ≃ ZetaZerosInTraceStrip (1 / 2) where
  toFun ρ := ⟨ρ.1, ρ.2.1, ρ.2.2.1, ρ.2.2.2.1,
    abs_sub_lt_iff.2 ⟨by linarith [ρ.2.2.2.1], by linarith [ρ.2.2.1]⟩⟩
  invFun ρ := ⟨ρ.1, ρ.2.1, ρ.2.2.1, ρ.2.2.2.1, h ρ⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The regularized tests are one-sided: they vanish below `exp (1/(n+1)) > 1`. -/
private theorem os_tsupport (n : ℕ) (s : ℂ) :
    tsupport (regularizedTraceTest n s) ⊆ Ioi 1 := by
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hsub : tsupport (regularizedTraceTest n s) ⊆ Ici (Real.exp (1 / ((n : ℝ) + 1))) := by
    apply closure_minimal _ isClosed_Ici
    intro t ht
    by_contra hlt
    simp only [mem_Ici, not_le] at hlt
    apply ht
    unfold regularizedTraceTest
    split_ifs with h1
    · have hlog : Real.log t < 1 / ((n : ℝ) + 1) := by
        rw [Real.log_lt_iff_lt_exp (by linarith)]; exact hlt
      have hle : ((n : ℝ) + 1) * Real.log t - 1 ≤ 0 := by
        have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have := (lt_div_iff₀' hn).1 hlog
        linarith
      simp [traceLogCutoff, h1, Real.smoothTransition.zero_of_nonpos hle]
    · rfl
  exact fun t ht => lt_of_lt_of_le (Real.one_lt_exp_iff.2 hpos) (hsub ht)

/-- A zeta zero that is not trivial and not `s = 1` has positive real part
(functional equation `riemannZeta_one_sub` applied at `1 - s`). -/
private lemma rr_re_pos_of_nontrivial_zero {s : ℂ} (hz : riemannZeta s = 0)
    (htriv : ¬∃ n : ℕ, s = -2 * (n + 1)) : 0 < s.re := by
  by_contra hle
  push Not at hle
  have hs0 : s ≠ 0 := by rintro rfl; rw [riemannZeta_zero] at hz; norm_num at hz
  have hre1 : 1 ≤ (1 - s).re := by simp; linarith
  have hn : ∀ n : ℕ, (1 - s) ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have h1 : (1 - s) ≠ 1 := by intro h; apply hs0; linear_combination -h
  have hFE := riemannZeta_one_sub hn h1
  rw [sub_sub_cancel, hz] at hFE
  have hζ : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hre1
  have hΓ : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero hn
  have hpow : (2 * (Real.pi : ℂ)) ^ (-(1 - s)) ≠ 0 := by
    intro h
    rw [Complex.cpow_eq_zero_iff] at h
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) h.1
  have hcos : Complex.cos (Real.pi * (1 - s) / 2) = 0 := by
    rcases mul_eq_zero.mp hFE.symm with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · norm_num at h
          · exact absurd h hpow
        · exact absurd h hΓ
      · exact h
    · exact absurd h hζ
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsk : s = -2 * (k : ℂ) := by
    have : (Real.pi : ℂ) * ((1 - s) - (2 * k + 1)) = 0 := by linear_combination 2 * hk
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hpi
    · linear_combination -h
  have hkre : s.re = -2 * k := by rw [hsk]; simp
  have hk0 : 0 ≤ k := by
    by_contra h; push Not at h
    have : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    linarith
  rcases (show k = 0 ∨ 1 ≤ k by omega) with h | h
  · subst h; apply hs0; simpa using hsk
  · apply htriv
    refine ⟨(k - 1).toNat, ?_⟩
    have : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
    rw [hsk]
    have hc : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
      have := congrArg (fun z : ℤ => (z : ℂ)) this
      push_cast at this ⊢
      exact_mod_cast this
    rw [hc]; ring


/-- (⇒) half of the one-sided fixed-window iff, using only the bare window equation. -/
private theorem rr_forward (α : ℝ) (hα : 0 < α)
    (H : ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ → tsupport φ ⊆ Ioi 1 →
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) :
    ∀ ρ : ZetaZerosInTraceStrip (1 / 2), |(ρ : ℂ).re - 1 / 2| < α := by
  have hsum : ∀ φ : ℝ → ℂ, IsRationalTraceTest φ ∧ tsupport φ ⊆ Ioi 1 →
      (∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) =
        ∑' ρ : ZetaZerosInTraceStrip (1 / 2), zetaTraceTerm φ (1 / 2) ρ := by
    intro φ hφ
    have h0 := H φ hφ.1 hφ.2
    have h1 := (trace_formula_rational_full_strip φ hφ.1).2.2.2
    have := h1.symm.trans h0
    linear_combination this
  have hcut : ∀ n : ℕ, cutoffSpectral α n 3 = cutoffSpectral (1 / 2) n 3 := fun n =>
    hsum _ ⟨regularized_test_admissible n 3, os_tsupport n 3⟩
  have hlα := os_spectralLimit α hα 3 (by norm_num)
  have hlh := os_spectralLimit (1 / 2) (by norm_num) 3 (by norm_num)
  simp only [hcut] at hlα
  have hspec : regularizedSpectral α 3 = regularizedSpectral (1 / 2) 3 :=
    tendsto_nhds_unique hlα hlh
  have hle : (regularizedTraceRHS (1 / 2) 3).re ≤ (regularizedTraceRHS α 3).re := by
    simp only [regularizedTraceRHS, hspec, le_refl]
  exact (single_resolvent_test α).1 hle

/-- The zeros of `ζ` away from `s = 1` form a countable set. -/
private theorem rr_zeros_countable :
    ({s : ℂ | riemannZeta s = 0} ∩ {1}ᶜ).Countable := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have han : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd
      (fun s hs => (differentiableAt_riemannZeta hs).differentiableWithinAt) hU
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) 1).isPreconnected
  rcases han.eqOn_zero_or_eventually_ne_zero_of_preconnected hconn with h | h
  · exfalso
    have h2 := h (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
    exact riemannZeta_ne_zero_of_one_le_re (by norm_num : (1 : ℝ) ≤ (2 : ℂ).re) h2
  · apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
      (isDiscrete_of_codiscreteWithin _)
    exact h

/-- Under RH, the bare one-sided identity holds at every regular width. -/
private theorem rr_backward (hRH : RiemannHypothesis) (β : ℝ) (hβ : 0 < β)
    (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip β, zetaTraceTerm φ β ρ := by
  have h : ∀ ρ : ZetaZerosInTraceStrip (1 / 2), |(ρ : ℂ).re - 1 / 2| < β := by
    intro ρ
    have hre : (ρ : ℂ).re = 1 / 2 := by
      apply hRH _ ρ.2.1
      · rintro ⟨n, hn⟩
        have := congrArg Complex.re hn
        simp at this
        have h0 := ρ.2.2.1
        have : (0 : ℝ) ≤ n := n.cast_nonneg
        linarith
      · intro h1
        have := ρ.2.2.2.1
        rw [h1] at this
        simp at this
    rw [hre, sub_self, abs_zero]; exact hβ
  obtain ⟨-, -, -, hEq⟩ := trace_formula_rational_full_strip φ hφ
  have hcomp : zetaTraceTerm φ β = zetaTraceTerm φ (1 / 2) ∘ os_equiv β h := rfl
  rw [hEq, hcomp]
  congr 1
  exact ((os_equiv β h).tsum_eq (zetaTraceTerm φ (1 / 2))).symm

theorem solution :
    (∀ (β : ℝ), 0 < β → (∀ ρ : ZetaZerosInTraceStrip (1/2), |ρ.val.re - 1/2| ≠ β) →
      ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ → tsupport φ ⊆ Ioi 1 →
        (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
            (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
          mellin φ (1/2) + mellin φ (-1/2) -
            ∑' ρ : ZetaZerosInTraceStrip β, zetaTraceTerm φ β ρ) ↔
    RiemannHypothesis := by
  constructor
  · intro H s hz htriv hs1
    have hpos := rr_re_pos_of_nontrivial_zero hz htriv
    have hlt1 : s.re < 1 := by
      by_contra h; push Not at h; exact riemannZeta_ne_zero_of_one_le_re h hz
    by_contra hne
    set d := |s.re - 1 / 2| with hd
    have hdpos : 0 < d := abs_pos.2 (sub_ne_zero.2 hne)
    let ρ₀ : ZetaZerosInTraceStrip (1 / 2) :=
      ⟨s, hz, hpos, hlt1, abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩⟩
    set R : Set ℝ := (fun z : ℂ => |z.re - 1 / 2|) '' ({s : ℂ | riemannZeta s = 0} ∩ {1}ᶜ)
    have hR : R.Countable := rr_zeros_countable.image _
    have hI : ¬ (Ioo 0 d).Countable := by
      rw [Cardinal.Real.Ioo_countable_iff]; linarith
    obtain ⟨β, hβI, hβR⟩ : ∃ β, β ∈ Ioo 0 d ∧ β ∉ R := by
      by_contra hc
      push Not at hc
      exact hI (hR.mono hc)
    have hreg : ∀ ρ : ZetaZerosInTraceStrip (1 / 2), |ρ.val.re - 1 / 2| ≠ β := by
      intro ρ hρ
      apply hβR
      refine ⟨ρ.val, ⟨ρ.2.1, ?_⟩, hρ⟩
      intro h1
      have := ρ.2.2.2.1
      rw [Set.mem_singleton_iff.1 h1] at this
      simp at this
    have := rr_forward β hβI.1 (H β hβI.1 hreg) ρ₀
    exact absurd this (by simp only [ρ₀]; exact not_lt.2 hβI.2.le)
  · intro hRH β hβ _ φ hφ _
    exact rr_backward hRH β hβ φ hφ

