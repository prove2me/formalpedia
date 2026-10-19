-- Prove2me | solution 1 for OAI.BackwardIntertwiners.normalized_support_separation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:57:32.630533+00:00
-- url     : https://prove2.me/submissions/93cd9f31-de4f-45db-9b71-2633e3f0baee

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/WeightSeparation.lean:L89-L167
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.normalized_support_separation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Theorems.Thm_OAI_BackwardIntertwiners_bounded_above_of_min
import Theorems.Thm_OAI_BackwardIntertwiners_bounds_of_weight
import Theorems.Thm_OAI_BackwardIntertwiners_no_both_unbounded
import Theorems.Thm_OAI_BackwardIntertwiners_stepRatio_summable

-- ---- from OAI.Analysis.BackwardIntertwiners.CoefficientSupport ----
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

namespace CoefficientEnvelope

variable {d : ℕ → ℂ} {G : ℕ → ℝ}
variable (hu : ∀ n : ℕ, ∃ k, n < k ∧ d k ≠ 0)
variable (hG : DiscreteConvex G) (hG0 : G 0 = 0)
variable (hb : ∀ n, ‖d n‖ ≤ Real.exp (-G n))

end CoefficientEnvelope

lemma nat_support_unbounded {d : ℤ → ℂ}
    (hu : ¬∃ m : ℤ, ∀ j : ℤ, d j ≠ 0 → j ≤ m) :
    ∀ n : ℕ, ∃ k, n < k ∧ d (k:ℤ) ≠ 0 := by
  push Not at hu
  intro n
  obtain ⟨j, hd, hj⟩ := hu n
  refine ⟨j.toNat, by omega, ?_⟩
  have he : (j.toNat:ℤ) = j := by omega
  simpa only [he] using hd

end
end BackwardIntertwiners

end OAI

-- ---- from OAI.Analysis.BackwardIntertwiners.WeightSeparation ----
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

lemma reflectedWeight_pos {w : ℤ → ℝ} (hw : ∀ j, 0 < w j) (j : ℤ) :
    0 < reflectedWeight w j := inv_pos.mpr (hw _)

lemma reflectedWeight_antitone {w : ℤ → ℝ} (hw : ∀ j, 0 < w j) (hdec : Antitone w) :
    Antitone (reflectedWeight w) := by
  intro i j hij
  exact (inv_le_inv₀ (hw _) (hw _)).mpr (hdec (neg_le_neg hij))

lemma reflected_positiveLog (w : ℤ → ℝ) : positiveLog (reflectedWeight w) = negativeLog w := by
  funext n
  simp [positiveLog, negativeLog, reflectedWeight, Real.log_inv]

lemma reflected_stepRatio_summable {w : ℤ → ℝ} (hs : Summable (stepRatio w)) :
    Summable (stepRatio (reflectedWeight w)) := by
  have hh := hs.comp_injective (i := fun j : ℤ => -j-1) (by
    intro a b hab; dsimp only at hab; omega)
  apply hh.congr
  intro j
  dsimp [stepRatio, reflectedWeight]
  have e₁ : -j-1+1 = -j := by omega
  have e₂ : -(j+1) = -j-1 := by omega
  rw [e₁, e₂, inv_div_inv]

lemma reflected_correlations {b c : ℤ → ℂ}
    (hz : ∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, b j * c (j-r)) = 0) :
    ∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, c (-j) * b (-(j-r))) = 0 := by
  intro r hr
  let e : ℤ ≃ ℤ := ⟨fun j => (r:ℤ)-j, fun j => (r:ℤ)-j, by intro j; dsimp only; omega, by intro j; dsimp only; omega⟩
  calc (∑' j : ℤ, c (-j) * b (-(j-r))) =
      ∑' j : ℤ, b (e j) * c (e j-r) := by
        apply tsum_congr
        intro j
        dsimp [e]
        have e₁ : (r:ℤ)-j = -(j-r) := by omega
        have e₂ : (r:ℤ)-j-r = -j := by omega
        rw [e₁, show -(j-(r:ℤ))-(r:ℤ) = -j by omega, mul_comm]
    _ = ∑' j : ℤ, b j * c (j-r) := e.tsum_eq (fun j : ℤ => b j * c (j-r))
    _ = 0 := hz r hr

lemma reflected_bounds {w : ℤ → ℝ} (hw : ∀ j, 0 < w j) {b c : ℤ → ℂ}
    (hb : ∀ j, ‖b j‖ ≤ w j) (hc : ∀ j, ‖c j‖*w j ≤ 1) :
    (∀ j, ‖c (-j)‖ ≤ reflectedWeight w j) ∧
    (∀ j, ‖b (-j)‖*reflectedWeight w j ≤ 1) := by
  constructor
  · intro j
    simpa only [reflectedWeight, one_div] using (le_div_iff₀ (hw (-j))).mpr (hc (-j))
  · intro j
    dsimp [reflectedWeight]
    rw [← div_eq_mul_inv]
    exact (div_le_one (hw _)).mpr (hb _)

theorem normalized_support_separation {w : ℤ → ℝ} (hw : ∀ j, 0 < w j)
    (hdec : Antitone w) (hw0 : w 0 = 1)
    (hP : DiscreteConvex (negativeLog w)) (hQ : DiscreteConvex (positiveLog w))
    {lam δ : ℝ} (hlam : Real.log 3 < lam) (hδ : lam < δ)
    (hqp : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ negativeLog w n)
    (hqq : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ positiveLog w n) :
    SupportSeparation w := by
  intro b c hbn hcn hb hc hz
  have hδ0 : 0 < δ := lt_trans (lt_trans (Real.log_pos (by norm_num : (1:ℝ)<3)) hlam) hδ
  have hP0 : negativeLog w 0 = 0 := by simp [negativeLog, hw0]
  have hQ0 : positiveLog w 0 = 0 := by simp [positiveLog, hw0]
  have hs := stepRatio_summable hw hw0 hP hQ hδ0 hqp hqq
  have hb_bd : ∃ m : ℤ, ∀ j : ℤ, b j ≠ 0 → j ≤ m := by
    by_cases hc_bd : ∃ m : ℤ, ∀ j : ℤ, c j ≠ 0 → m ≤ j
    · obtain ⟨h, hch, hh⟩ := Int.exists_least_of_bdd hc_bd hcn
      apply bounded_above_of_min hw hdec hw0 hs hQ hδ0 hqq hb hc hch ?_ hz
      intro j hj
      by_contra hne
      have := hh j hne
      omega
    · by_contra hbu
      have hcu : ¬∃ m : ℤ, ∀ j : ℤ, c (-j) ≠ 0 → j ≤ m := by
        rintro ⟨m, hm⟩
        apply hc_bd
        refine ⟨-m, ?_⟩
        intro j hj
        have hh := hm (-j) (by simpa using hj)
        omega
      exact no_both_unbounded (bounds_of_weight hw hb hc) hP hQ hP0 hQ0 hlam hδ hqp hqq
        (nat_support_unbounded hbu) (nat_support_unbounded hcu) hz
  obtain ⟨t, hbt, ht⟩ := Int.exists_greatest_of_bdd hb_bd hbn
  have hc_bd : ∃ m : ℤ, ∀ j : ℤ, c j ≠ 0 → m ≤ j := by
    have hwr0 : reflectedWeight w 0 = 1 := by simp [reflectedWeight, hw0]
    have hQr : DiscreteConvex (positiveLog (reflectedWeight w)) := by
      rw [reflected_positiveLog]; exact hP
    have hqpr : ∀ᶠ n : ℕ in atTop, δ*(n:ℝ)^2 ≤ positiveLog (reflectedWeight w) n := by
      simpa only [reflected_positiveLog] using hqp
    obtain ⟨hbr, hcr⟩ := reflected_bounds hw hb hc
    have hzref := reflected_correlations hz
    have hm := bounded_above_of_min (reflectedWeight_pos hw) (reflectedWeight_antitone hw hdec)
      hwr0 (reflected_stepRatio_summable hs) hQr hδ0 hqpr hbr hcr
      (h := -t) (by simpa using hbt) (by
        intro j hj
        by_contra hne
        have hh := ht (-j) hne
        omega) hzref
    obtain ⟨m, hm⟩ := hm
    refine ⟨-m, ?_⟩
    intro j hj
    have hh := hm (-j) (by simpa using hj)
    omega
  obtain ⟨h, hch, hh⟩ := Int.exists_least_of_bdd hc_bd hcn
  have hbmax : ∀ j : ℤ, t < j → b j = 0 := by
    intro j hj
    by_contra hne
    have := ht j hne
    omega
  have hcmin : ∀ j : ℤ, j < h → c j = 0 := by
    intro j hj
    by_contra hne
    have := hh j hne
    omega
  refine ⟨t, h, hbt, hch, hbmax, hcmin, ?_⟩
  by_contra! hth
  let r := (t-h).toNat
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hri : (r:ℤ) = t-h := by dsimp [r]; omega
  have he : (∑' j : ℤ, b j * c (j-r)) = b t * c h := by
    rw [tsum_eq_single t]
    · congr 2
      omega
    · intro j hj
      by_cases hbj : b j = 0
      · simp [hbj]
      · have htj := ht j hbj
        rw [hcmin _ (by omega), mul_zero]
  have hzero := hz r hr
  rw [he] at hzero
  exact (mul_ne_zero hbt hch) hzero

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.normalized_support_separation := @_root_.OAI.BackwardIntertwiners.normalized_support_separation
