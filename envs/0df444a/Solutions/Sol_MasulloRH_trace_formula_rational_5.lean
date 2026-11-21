-- Prove2me | solution 5 for MasulloRH.trace_formula_rational
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @lll
-- created : 2026-11-21T00:48:42.074569+00:00
-- url     : https://prove2.me/submissions/38549aad-4757-4bf3-b80f-092ab546cda9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloAudit_trace_formula_rational_source_form
import Theorems.Thm_MasulloAudit_geometric_side_eq_formal_lhs
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

open MeasureTheory Set MasulloRH
open scoped Topology

namespace LinkTfrSourceForm

/-- The combined real-place integrand is integrable on `(1, ∞)`: it vanishes for large `t`, and
near `1` the zero `ϕ(1) = 0` cancels the simple pole of `√t/(t²-1)` (Lipschitz bound). -/

theorem integrableOn_realTraceIntegrand' (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) := by
  obtain ⟨hsm, hcs, hts, h1⟩ := hφ
  have hK : IsCompact (tsupport φ) := hcs
  -- bounds a, b of the support
  obtain ⟨a, ha0, hab⟩ : ∃ a > 0, ∀ x ∈ tsupport φ, a ≤ x := by
    rcases (tsupport φ).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn h continuous_id.continuousOn
      exact ⟨x0, hts hx0, fun x hx => hmin hx⟩
  obtain ⟨b, hb⟩ : ∃ b, ∀ x ∈ tsupport φ, x ≤ b := hK.bddAbove
  set R : ℝ := max (max b (1 / a)) 2 with hR
  have hR2 : 2 ≤ R := le_max_right _ _
  have hRb : b ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hRa : 1 / a ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hzero : ∀ x, φ x ≠ 0 → x ∈ tsupport φ := fun x hx => subset_tsupport _ hx
  -- vanishing beyond R
  have hvan : ∀ t, R < t → realTraceIntegrand φ t = 0 := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have e1 : φ t = 0 := by
      by_contra h; have := hb t (hzero t h); linarith
    have e2 : φ t⁻¹ = 0 := by
      by_contra h
      have := hab _ (hzero _ h)
      have hlt : t⁻¹ < a := by
        rw [inv_lt_comm₀ ht0 ha0]; rw [one_div] at hRa; linarith
      linarith
    simp [realTraceIntegrand, e1, e2]
  -- g = φ + φ ∘ inv is Lipschitz on [1, R]
  set g : ℝ → ℂ := fun t => φ t + φ t⁻¹ with hg
  have hgc : ContDiffOn ℝ 1 g (Icc 1 R) := by
    have h1' : ContDiff ℝ 1 φ := hsm.of_le (by exact_mod_cast le_top)
    refine h1'.contDiffOn.add ?_
    refine h1'.comp_contDiffOn ?_
    exact (contDiffOn_inv ℝ).mono (fun x hx => by
      simp only [mem_compl_iff, mem_singleton_iff]; linarith [hx.1])
  obtain ⟨L, hL⟩ := hgc.exists_lipschitzOnWith one_ne_zero (convex_Icc 1 R) isCompact_Icc
  have hg1 : g 1 = 0 := by simp [hg, h1]
  have hbound : ∀ t ∈ Ioc (1:ℝ) R, ‖realTraceIntegrand φ t‖ ≤ L := by
    intro t ht
    have hdist := hL.dist_le_mul t ⟨ht.1.le, ht.2⟩ 1 ⟨le_rfl, by linarith⟩
    rw [dist_eq_norm, hg1, sub_zero, Real.dist_eq, abs_of_pos (by linarith [ht.1])] at hdist
    have ht1 : 0 < t - 1 := by linarith [ht.1]
    have hden : 0 < t ^ 2 - 1 := by nlinarith [ht.1]
    have hsq : Real.sqrt t ≤ t + 1 := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith [ht.1]
    rw [realTraceIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hden.le)]
    calc ‖g t‖ * (Real.sqrt t / (t ^ 2 - 1))
        ≤ (L * (t - 1)) * (Real.sqrt t / (t ^ 2 - 1)) :=
          mul_le_mul_of_nonneg_right hdist (div_nonneg (Real.sqrt_nonneg _) hden.le)
      _ = L * ((t - 1) * Real.sqrt t / (t ^ 2 - 1)) := by ring
      _ ≤ L * 1 := by
          apply mul_le_mul_of_nonneg_left _ L.2
          rw [div_le_one hden]
          nlinarith [Real.sqrt_nonneg t]
      _ = L := mul_one _
  have hmeas : AEStronglyMeasurable (realTraceIntegrand φ) (volume.restrict (Ioi 1)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro t ht
    have ht0 : (t:ℝ) ≠ 0 := by have := ht.out; linarith
    have hne : t ^ 2 - 1 ≠ 0 := by have := ht.out; nlinarith
    apply ContinuousAt.continuousWithinAt
    unfold realTraceIntegrand
    refine ContinuousAt.mul ?_ ?_
    · exact (hsm.continuous.continuousAt).add
        ((hsm.continuous.continuousAt).comp (continuousAt_inv₀ ht0))
    · refine Complex.continuous_ofReal.continuousAt.comp ?_
      exact (Real.continuous_sqrt.continuousAt).div (by fun_prop) hne
  have hsub : Ioi (1:ℝ) ⊆ Ioc 1 R ∪ Ioi R := fun t ht => by
    rcases le_or_gt t R with h | h
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr h
  refine IntegrableOn.mono_set (IntegrableOn.union ?_ ?_) hsub
  · refine ⟨hmeas.mono_set Ioc_subset_Ioi_self,
      .restrict_of_bounded (C := (L:ℝ)) measure_Ioc_lt_top ?_⟩
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall hbound
  · exact (integrableOn_zero).congr_fun (fun t ht => (hvan t ht).symm) measurableSet_Ioi

end LinkTfrSourceForm

open LinkTfrSourceForm in
theorem solution (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ)
    (hφ : IsRationalTraceTest φ) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧
    Summable (zetaTraceTerm φ α) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by
  have : ∀ p : Nat.Primes, Fact (p : ℕ).Prime := fun p => ⟨p.2⟩
  let inst : ∀ p : Nat.Primes, MeasurableSpace ℚ_[p] := fun p => borel ℚ_[p]
  have hB : ∀ p : Nat.Primes, BorelSpace ℚ_[p] := fun p => ⟨rfl⟩
  let μ : ∀ p : Nat.Primes, Measure ℚ_[p] := fun p => Measure.addHaar
  have hμ : ∀ p : Nat.Primes, (μ p).IsAddHaarMeasure := fun p => by
    dsimp only [μ]; infer_instance
  obtain ⟨-, -, -, -, hpp, hgeom⟩ :=
    MasulloAudit.geometric_side_eq_formal_lhs φ hφ inst μ
  obtain ⟨-, -, -, hz, hsrc⟩ :=
    MasulloAudit.trace_formula_rational_source_form α hα φ hφ inst μ
  refine ⟨integrableOn_realTraceIntegrand' φ hφ, hpp, hz, ?_⟩
  rw [← hgeom]
  exact hsrc
