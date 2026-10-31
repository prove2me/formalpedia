-- Prove2me | solution 1 for MinBuying.theorem4_regular_tight
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:12:15.315539+00:00
-- url     : https://prove2.me/submissions/e34f61a0-79b4-44b9-bc80-78f58416d097

import Theorems.Thm_MinBuying_critical_ratio_characterization
import Theorems.Thm_MinBuying_lemma1_triangular_reduction
import Theorems.Thm_MinBuying_lemma2_canonical_reduction
import Theorems.Thm_MinBuying_lemma3_canonical_bound
import Theorems.Thm_MinBuying_lemma4_canonical_tightness
import Theorems.Thm_MinBuying_lemmaEC2_continuous_smoothing
import Theorems.Thm_MinBuying_triangular_revenue_homogeneity

open MeasureTheory Set MinBuying

private lemma cap_feasible (I : CanonicalInstance) : FeasiblePrices (canonicalPrices I) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · exact le_of_lt (lt_trans zero_lt_one I.terminal_one_lt)
  · intro j
    exact le_of_lt (lt_trans zero_lt_one (I.cap_one_lt j))

private lemma revenue_le_opt {n : ℕ} (μ : JointLaw n) (hμ : WellPosed μ)
    (p : Prices n) (hp : FeasiblePrices p) : Revenue μ p ≤ DPRevenue μ := by
  apply le_csSup hμ.1
  exact ⟨p, hp, rfl⟩

private lemma normalized_triangular_bound (n : ℕ) (hn : 0 < n)
    (I : TriangularInstance n) (hI : UPRevenue (triangularJoint I) = 1) :
    DPRevenue (triangularJoint I) ≤ 1 / criticalRatio := by
  by_contra h
  have hgap : 0 < DPRevenue (triangularJoint I) - 1 / criticalRatio := sub_pos.mpr (lt_of_not_ge h)
  obtain ⟨J, _, hloss, hUP⟩ := lemma2_canonical_reduction n hn I hI
    ((DPRevenue (triangularJoint I) - 1 / criticalRatio) / 2) (half_pos hgap)
  have hbound := lemma3_canonical_bound J hUP
  linarith

private lemma regular_bound (n : ℕ) (F : Fin n → Measure ℝ) (hF : RegularInstance F)
    (hrho : 0 < criticalRatio) :
    criticalRatio * DPRevenue (productLaw F) ≤ UPRevenue (productLaw F) := by
  obtain ⟨m, hm, _, I, hI, hDP, hUP⟩ := lemma1_triangular_reduction n F hF
  have hU : 0 < UPRevenue (triangularJoint I) := hI.2.2.2.2
  obtain ⟨J, _, _, _, hJD, hJU⟩ := triangular_revenue_homogeneity m I hI
    (1 / UPRevenue (triangularJoint I)) (one_div_pos.mpr hU)
  have hnorm : UPRevenue (triangularJoint J) = 1 := by
    rw [hJU]
    exact one_div_mul_cancel hU.ne'
  have hb := normalized_triangular_bound m hm J hnorm
  rw [hJD] at hb
  have hratio : DPRevenue (triangularJoint I) / UPRevenue (triangularJoint I)
      ≤ 1 / criticalRatio := by simpa [div_eq_mul_inv, mul_comm] using hb
  have hcross := (div_le_div_iff₀ hU hrho).mp hratio
  calc
    criticalRatio * DPRevenue (productLaw F)
      ≤ criticalRatio * DPRevenue (triangularJoint I) := mul_le_mul_of_nonneg_left hDP hrho.le
    _ ≤ UPRevenue (triangularJoint I) := by nlinarith
    _ ≤ UPRevenue (productLaw F) := hUP

private lemma regular_sharpness (hrho : 0 < criticalRatio) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (F : Fin n → Measure ℝ), RegularInstance F ∧
      1 / criticalRatio - ε < DPRevenue (productLaw F) / UPRevenue (productLaw F) := by
  let Q := 1 / criticalRatio
  have hQ : 0 < Q := one_div_pos.mpr hrho
  let η := min (ε / 4) (Q / 4)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηε : η ≤ ε / 4 := min_le_left _ _
  have hηQ : η ≤ Q / 4 := min_le_right _ _
  obtain ⟨I, hIU, hID⟩ := lemma4_canonical_tightness η hη
  obtain ⟨J, _, hcap, hJU⟩ := lemma2_canonical_reduction (I.count + 1) (by omega)
    (canonicalParameters I) hIU η hη
  have hcaplow : Q - 2 * η < Revenue (canonicalLaw J) (canonicalPrices J) := by
    change Q - η < DPRevenue (canonicalLaw I) at hID
    change DPRevenue (canonicalLaw I) - η ≤ Revenue (canonicalLaw J) (canonicalPrices J) at hcap
    linarith
  have hcappos : 0 < Revenue (canonicalLaw J) (canonicalPrices J) := by linarith
  have hcapup := lemma3_canonical_bound J hJU
  change Revenue (canonicalLaw J) (canonicalPrices J) ≤ Q at hcapup
  obtain ⟨δ₀, hδ₀, hsmooth⟩ := lemmaEC2_continuous_smoothing (J.count + 1) (by omega)
    (canonicalParameters J) hJU
  let δ := min (δ₀ / 2) (min (1 / 2 : ℝ) (η / Q))
  have hδ : 0 < δ := lt_min (half_pos hδ₀) (lt_min (by norm_num) (div_pos hη hQ))
  have hδle0 : δ ≤ δ₀ / 2 := min_le_left _ _
  have hδle1 : δ ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδleη : δ ≤ η / Q := le_trans (min_le_right _ _) (min_le_right _ _)
  have hδsmall : δ < min 1 δ₀ := lt_min (by linarith) (by linarith)
  have h1δ : 0 < 1 - δ := by linarith
  have hδQ : δ * Q ≤ η := (le_div_iff₀ hQ).mp hδleη
  obtain ⟨F, hF, hsame, hFU⟩ := hsmooth δ hδ hδsmall
  refine ⟨J.count + 1, F, hF, ?_⟩
  change Revenue (productLaw F) (canonicalPrices J) =
    Revenue (canonicalLaw J) (canonicalPrices J) at hsame
  have hDF := revenue_le_opt (productLaw F) hF.2.2 (canonicalPrices J) (cap_feasible J)
  rw [hsame] at hDF
  have hUF : 0 < UPRevenue (productLaw F) := hF.2.2.2.2.2.2
  have hUscaled : UPRevenue (productLaw F) * (1 - δ) ≤ 1 :=
    (le_div_iff₀ h1δ).mp hFU
  have hratio : Revenue (canonicalLaw J) (canonicalPrices J) * (1 - δ) ≤
      DPRevenue (productLaw F) / UPRevenue (productLaw F) := by
    apply (le_div_iff₀ hUF).2
    have hmul := mul_le_mul_of_nonneg_left hUscaled hcappos.le
    nlinarith
  have hloss := mul_le_mul_of_nonneg_left hcapup hδ.le
  have hclose : Q - ε < Revenue (canonicalLaw J) (canonicalPrices J) * (1 - δ) := by
    nlinarith
  exact lt_of_lt_of_le hclose hratio

theorem solution :
    criticalRatio ∈ Ioo (0 : ℝ) 1 ∧
    criticalRatio * continuousBenchmark criticalRatio = 1 ∧
    (∀ x ∈ Ioo (0 : ℝ) 1,
      x * continuousBenchmark x = 1 → x = criticalRatio) ∧
    (∀ (n : ℕ) (F : Fin n → Measure ℝ), RegularInstance F →
      criticalRatio * DPRevenue (productLaw F) ≤ UPRevenue (productLaw F)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → Measure ℝ),
      RegularInstance F ∧
      1 / criticalRatio - ε < DPRevenue (productLaw F) / UPRevenue (productLaw F)) := by
  obtain ⟨hρ, hroot, hunique, _⟩ := critical_ratio_characterization
  exact ⟨hρ, hroot, hunique, fun n F hF => regular_bound n F hF hρ.1,
    fun ε hε => regular_sharpness hρ.1 ε hε⟩
