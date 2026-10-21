-- Prove2me | solution 1 for HedgeInv.Value.covariance_inequality
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:32:46.167862+00:00
-- url     : https://prove2.me/submissions/2af76c33-8305-41ac-93ee-ba08ebfbdaa9

import Mathlib
import Definitions.Def_HedgeInv_Value_Model
set_option autoImplicit false
open MeasureTheory

theorem HGV_threshold (ν : Measure ℝ) [IsProbabilityMeasure ν] (g : ℝ → ℝ) (hg : Antitone g)
    (hint : Integrable g ν) (h0 : ∫ s, g s ∂ν = 0) :
    ∃ t : ℝ, ∀ᵐ s ∂ν, (s < t → 0 ≤ g s) ∧ (t < s → g s ≤ 0) := by
  set A : Set ℝ := {s | 0 < g s} with hA
  by_cases hAe : A = ∅
  · refine ⟨0, ?_⟩
    have hneg : ∀ s, g s ≤ 0 := fun s => by
      by_contra h; push_neg at h
      have : s ∈ A := h
      rw [hAe] at this; exact this
    have : (fun s => -g s) =ᵐ[ν] 0 := by
      have h1 := (integral_eq_zero_iff_of_nonneg (μ := ν) (f := fun s => -g s)
        (fun s => by simpa using hneg s) hint.neg).1 (by simp [integral_neg, h0])
      exact h1
    filter_upwards [this] with s hs
    have : g s = 0 := by simpa using hs
    exact ⟨fun _ => this.ge, fun _ => this.le⟩
  · have hne : A.Nonempty := Set.nonempty_iff_ne_empty.2 hAe
    have hbdd : BddAbove A := by
      by_contra hb
      have hpos : ∀ s, 0 < g s := by
        intro s
        rw [not_bddAbove_iff] at hb
        obtain ⟨s', hs', hlt⟩ := hb s
        exact lt_of_lt_of_le hs' (hg hlt.le)
      have : 0 < ∫ s, g s ∂ν := by
        rw [integral_pos_iff_support_of_nonneg (fun s => (hpos s).le) hint]
        have : Function.support g = Set.univ := by
          ext s; simp [(hpos s).ne']
        rw [this]; simp
      linarith
    refine ⟨sSup A, Filter.Eventually.of_forall fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
    · obtain ⟨s', hs', hlt⟩ := exists_lt_of_lt_csSup hne hs
      exact (lt_of_lt_of_le hs' (hg hlt.le)).le
    · by_contra h; push_neg at h
      have : s ∈ A := h
      exact absurd (le_csSup hbdd this) (not_le.2 hs)

theorem HGV_core (ν G : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure G]
    (F : ℝ × ℝ → ℝ) (g : ℝ → ℝ) (hg : Antitone g) (hgi : Integrable g ν)
    (hg0 : ∫ s, g s ∂ν = 0) (hF : ∀ e, Antitone (fun s => F (s, e)))
    (hFg : Integrable (fun p : ℝ × ℝ => F p * g p.1) (ν.prod G)) :
    0 ≤ ∫ p : ℝ × ℝ, F p * g p.1 ∂(ν.prod G) := by
  obtain ⟨t, ht⟩ := HGV_threshold ν g hg hgi hg0
  rw [integral_prod_symm _ hFg]
  refine integral_nonneg_of_ae ?_
  filter_upwards [hFg.prod_left_ae] with e he
  have hc : Integrable (fun s => F (t, e) * g s) ν := hgi.const_mul _
  have hsplit : ∫ s, F (s, e) * g s ∂ν =
      ∫ s, (F (s, e) - F (t, e)) * g s ∂ν + F (t, e) * ∫ s, g s ∂ν := by
    rw [← integral_const_mul, ← integral_add]
    · congr 1; funext s; ring
    · have := he.sub hc
      refine this.congr (Filter.Eventually.of_forall fun s => ?_)
      simp only [Pi.sub_apply]; ring
    · exact hc
  rw [hsplit, hg0, mul_zero, add_zero]
  refine integral_nonneg_of_ae ?_
  filter_upwards [ht] with s hs
  rcases lt_trichotomy s t with h | h | h
  · have h1 : F (t, e) ≤ F (s, e) := hF e h.le
    exact mul_nonneg (by linarith) (hs.1 h)
  · subst h; simp
  · have h1 : F (s, e) ≤ F (t, e) := hF e h.le
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (hs.2 h)

theorem HGV_deriv_anti (u : ℝ → ℝ) (hu_conc : ConcaveOn ℝ Set.univ u)
    (hu_diff : Differentiable ℝ u) : Antitone (deriv u) :=
  antitoneOn_univ.1 (hu_conc.antitoneOn_deriv (fun x _ => hu_diff x))

theorem solution
    (ν G : Measure ℝ) [IsProbabilityMeasure ν] [IsProbabilityMeasure G]
    (hG_mean : ∫ e, e ∂G = 0) (hG_L2 : MemLp id 2 G)
    (W a b c₁ I : ℝ) (hb : 0 < b) (hI : max a 0 < I) (hc₁ : 0 < c₁) (hc₁b : c₁ * b < 1)
    (φ : ℝ → ℝ) (hφ_mono : Monotone φ) (hφ_meas : Measurable φ) (hφ_int : Integrable φ ν)
    (x0r : ℝ) (h12 : ∫ s, φ s ∂ν = x0r)
    (u : ℝ → ℝ) (hu_conc : ConcaveOn ℝ Set.univ u) (hu_diff : Differentiable ℝ u)
    (hint_du : Integrable (fun p : ℝ × ℝ => deriv u (HedgeInv.Value.unhedgedPayoff W a b c₁ I p.1 p.2)) (ν.prod G))
    (hint_prod : Integrable
      (fun p : ℝ × ℝ => deriv u (HedgeInv.Value.unhedgedPayoff W a b c₁ I p.1 p.2) * (x0r - φ p.1)) (ν.prod G)) :
    (∫ p : ℝ × ℝ, deriv u (HedgeInv.Value.unhedgedPayoff W a b c₁ I p.1 p.2) ∂(ν.prod G)) *
        (∫ p : ℝ × ℝ, (x0r - φ p.1) ∂(ν.prod G)) ≤
      ∫ p : ℝ × ℝ, deriv u (HedgeInv.Value.unhedgedPayoff W a b c₁ I p.1 p.2) * (x0r - φ p.1) ∂(ν.prod G) ∧
    ∫ p : ℝ × ℝ, (x0r - φ p.1) ∂(ν.prod G) = 0 := by
  have hgi : Integrable (fun s => x0r - φ s) ν := (integrable_const x0r).sub hφ_int
  have hg0 : ∫ s, (x0r - φ s) ∂ν = 0 := by
    rw [integral_sub (integrable_const x0r) hφ_int, h12]; simp
  have hprod0 : ∫ p : ℝ × ℝ, (x0r - φ p.1) ∂(ν.prod G) = 0 := by
    have h1 : ∫ z : ℝ × ℝ, (x0r - φ z.1) * (fun _ : ℝ => (1:ℝ)) z.2 ∂(ν.prod G) =
        (∫ s, (x0r - φ s) ∂ν) * ∫ _, (1:ℝ) ∂G := integral_prod_mul (fun s => x0r - φ s) (fun _ => (1:ℝ))
    simpa [hg0] using h1
  refine ⟨?_, hprod0⟩
  rw [hprod0, mul_zero]
  have hanti : Antitone (fun s => x0r - φ s) := fun x y h => by
    have := hφ_mono h; linarith
  refine HGV_core ν G (fun p => deriv u (HedgeInv.Value.unhedgedPayoff W a b c₁ I p.1 p.2))
    (fun s => x0r - φ s) hanti hgi hg0 ?_ hint_prod
  intro e s s' hss'
  refine HGV_deriv_anti u hu_conc hu_diff ?_
  simp only [HedgeInv.Value.unhedgedPayoff]
  have : min (s + e) ((I - a) / b) ≤ min (s' + e) ((I - a) / b) := min_le_min_right _ (by linarith)
  linarith

