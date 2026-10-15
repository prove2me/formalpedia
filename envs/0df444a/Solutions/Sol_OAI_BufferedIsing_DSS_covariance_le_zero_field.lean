-- Prove2me | solution 1 for OAI.BufferedIsing.DSS.covariance_le_zero_field
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:05:06.66415+00:00
-- url     : https://prove2.me/submissions/cd124e0a-8919-4ae0-924a-da4acb566ab8

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Influence.lean:L260-L274
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.DSS.covariance_le_zero_field. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Definitions.Def_OAI_Probability_Ising_Covariance
import Definitions.Def_OAI_Probability_Ising_Contraction
import Definitions.Def_OAI_Probability_Ising_GibbsMeasure
import Definitions.Def_OAI_Probability_Ising_Interpolation
import Definitions.Def_OAI_Probability_Ising_FieldUpdate
import Definitions.Def_OAI_Probability_Ising_Influence
import Theorems.Thm_OAI_BufferedIsing_DSS_influence_of_card
import Theorems.Thm_OAI_BufferedIsing_DSS_mean_mono
import Theorems.Thm_OAI_BufferedIsing_DSS_pin_comparison_of_removed

-- ---- from OAI.Probability.Ising.GibbsMeasure ----
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing.DSS

noncomputable section

variable {V : Type*} [Fintype V]

lemma mass_pos (J : V → V → ℝ) (h : V → ℝ) (σ : V → Bool) : 0 < mass J h σ :=
  Real.exp_pos _

lemma part_pos (J : V → V → ℝ) (h : V → ℝ) : 0 < part J h := by
  classical
  exact Finset.sum_pos (fun σ _ => mass_pos J h σ) Finset.univ_nonempty

lemma sgn_neg (b : Bool) : sgn (!b) = -sgn b := by cases b <;> norm_num [sgn]
lemma sgn_sq (b : Bool) : sgn b * sgn b = 1 := by cases b <;> norm_num [sgn]
lemma average_const (J : V → V → ℝ) (h : V → ℝ) (c : ℝ) :
    average J h (fun _ => c) = c := by
  unfold average
  rw [← Finset.sum_mul]
  exact mul_div_cancel_left₀ c (part_pos J h).ne'

end

end BufferedIsing.DSS

end OAI

-- ---- from OAI.Probability.Ising.FieldUpdate ----
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing.DSS

noncomputable section

variable {V : Type*} [Fintype V]

lemma sum_insert (v : V) (f : (V → Bool) → ℝ) :
    (∑ σ, f σ) =
      (∑ η, f (insertSpin v true η)) + ∑ η, f (insertSpin v false η) := by
  rw [← (Equiv.funSplitAt v Bool).symm.sum_comp f, Fintype.sum_prod_type]
  simp only [insertSpin, Fintype.sum_bool]

lemma sum_remove (v : V) (f : V → ℝ) :
    (∑ u, f u) = f v + ∑ u : {u : V // u ≠ v}, f u := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ v)]
  have he : (∑ u ∈ Finset.univ.erase v, f u) = ∑ u : {u : V // u ≠ v}, f u := by
    exact Finset.sum_subtype _ (fun _ => by simp) _
  rw [he, add_comm]

lemma hamiltonian_insert (J : V → V → ℝ) (h : V → ℝ) (v : V)
    (b : Bool) (η : {u : V // u ≠ v} → Bool) :
    hamiltonian J h (insertSpin v b η) = J v v + h v * sgn b +
      hamiltonian (removedCoupling J v) (removedField J h v b) η := by
  unfold hamiltonian
  rw [sum_remove v (fun u => ∑ w, J u w * sgn (insertSpin v b η u) * sgn (insertSpin v b η w))]
  rw [sum_remove v (fun u => h u * sgn (insertSpin v b η u))]
  simp_rw [sum_remove v (fun w => J _ w * sgn (insertSpin v b η _) * sgn (insertSpin v b η w))]
  simp only [insertSpin_self, insertSpin_other, mul_assoc, sgn_sq, mul_one,
    Finset.sum_add_distrib, removedCoupling, removedField, add_mul, Finset.sum_add_distrib]
  have he : (∑ u : {u : V // u ≠ v}, J v u * (sgn b * sgn (η u))) +
        (∑ u : {u : V // u ≠ v}, J u v * (sgn (η u) * sgn b)) =
      ∑ u : {u : V // u ≠ v}, (J v u + J u v) * sgn b * sgn (η u) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    ring
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc] at he
  linarith

lemma mass_insert (J : V → V → ℝ) (h : V → ℝ) (v : V)
    (b : Bool) (η : {u : V // u ≠ v} → Bool) :
    mass J h (insertSpin v b η) = Real.exp (J v v + h v * sgn b) *
      mass (removedCoupling J v) (removedField J h v b) η := by
  simp only [mass, hamiltonian_insert, Real.exp_add]

lemma pinMean_self (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool) :
    pinMean J h v b v = sgn b := by
  simp only [pinMean, insertSpin_self, average_const]

lemma pinMean_other (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool)
    (o : V) (hov : o ≠ v) :
    pinMean J h v b o = mean (removedCoupling J v) (removedField J h v b) ⟨o, hov⟩ := by
  unfold pinMean mean
  congr 1
  funext η
  exact congrArg sgn (insertSpin_other v b η ⟨o, hov⟩)

lemma pinMean_mono (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (h : V → ℝ) (v o : V) : pinMean J h v false o ≤ pinMean J h v true o := by
  by_cases hov : o = v
  · subst o
    simp [pinMean_self, sgn]
  · rw [pinMean_other _ _ _ _ _ hov, pinMean_other _ _ _ _ _ hov]
    apply mean_mono (removedCoupling J v) (fun u w => hJ u.val w.val)
    intro u
    dsimp [removedField, sgn]
    nlinarith [hJ v u, hJ u v]

lemma average_mul_part (J : V → V → ℝ) (h : V → ℝ) (f : (V → Bool) → ℝ) :
    average J h f * part J h = ∑ σ, mass J h σ * f σ := by
  exact div_mul_cancel₀ _ (part_pos J h).ne'

lemma pinPart_pos (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool) :
    0 < pinPart J h v b := mul_pos (Real.exp_pos _) (part_pos _ _)

lemma part_split (J : V → V → ℝ) (h : V → ℝ) (v : V) :
    part J h = pinPart J h v true + pinPart J h v false := by
  rw [part, sum_insert v]
  simp_rw [mass_insert, ← Finset.mul_sum]
  simp only [pinPart, part]
  congr!

lemma mean_split (J : V → V → ℝ) (h : V → ℝ) (v o : V) :
    mean J h o = (pinPart J h v true * pinMean J h v true o +
      pinPart J h v false * pinMean J h v false o) / part J h := by
  unfold mean average
  rw [sum_insert v]
  congr 1
  have H (b : Bool) : (∑ η, mass J h (insertSpin v b η) * sgn (insertSpin v b η o)) =
      pinPart J h v b * pinMean J h v b o := by
    simp_rw [mass_insert, mul_assoc, ← Finset.mul_sum]
    rw [pinPart, pinMean, mul_assoc, mul_comm (part _ _), average_mul_part]
    congr!
  rw [H, H]

lemma mean_self_split (J : V → V → ℝ) (h : V → ℝ) (v : V) :
    mean J h v = (pinPart J h v true - pinPart J h v false) /
      (pinPart J h v true + pinPart J h v false) := by
  rw [mean_split J h v v, pinMean_self, pinMean_self, part_split J h v]
  simp [sgn, sub_eq_add_neg]

lemma hamiltonian_flip (J : V → V → ℝ) (h : V → ℝ) (σ : V → Bool) :
    hamiltonian J (-h) (fun u => !(σ u)) = hamiltonian J h σ := by
  simp [hamiltonian, sgn_neg]

lemma mass_flip (J : V → V → ℝ) (h : V → ℝ) (σ : V → Bool) :
    mass J (-h) (fun u => !(σ u)) = mass J h σ := by
  simp only [mass, hamiltonian_flip]

lemma part_neg (J : V → V → ℝ) (h : V → ℝ) : part J (-h) = part J h := by
  rw [part, ← flipEquiv.sum_comp]
  simp only [flipEquiv, Equiv.coe_fn_mk, mass_flip]
  rfl

lemma mean_neg (J : V → V → ℝ) (h : V → ℝ) (v : V) :
    mean J (-h) v = -mean J h v := by
  rw [mean, average, part_neg, ← flipEquiv.sum_comp]
  simp only [flipEquiv, Equiv.coe_fn_mk, mass_flip, sgn_neg, mul_neg,
    Finset.sum_neg_distrib, neg_div]
  rfl

lemma mean_zero (J : V → V → ℝ) (v : V) : mean J 0 v = 0 := by
  have H := mean_neg J 0 v
  simp only [neg_zero] at H
  linarith

end

end BufferedIsing.DSS

end OAI

-- ---- from OAI.Probability.Ising.Influence ----
namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing.DSS

noncomputable section

universe u

variable {V : Type u} [Fintype V]

/-- Arbitrary real background fields do not increase the influence of a finite
nonnegative perturbation, on every finite ferromagnetic graph. -/
theorem influence (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v) : InfluenceBound J :=
  influence_of_card (Fintype.card V) V rfl J hJ

lemma pin_gap_comparison (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (g : V → ℝ) (v o : V) :
    pinMean J g v true o - pinMean J g v false o ≤
      pinMean J 0 v true o - pinMean J 0 v false o := by
  have H := pin_comparison_of_removed J hJ g 0 (le_refl _) v o
    (influence (removedCoupling J v) (fun u w => hJ u w))
  simpa only [add_zero, sub_zero, neg_zero] using H

lemma sum_pin_first (J : V → V → ℝ) (h : V → ℝ) (v o : V) (b : Bool) :
    (∑ η, mass J h (insertSpin v b η) * sgn (insertSpin v b η o)) =
      pinPart J h v b * pinMean J h v b o := by
  simp_rw [mass_insert, mul_assoc, ← Finset.mul_sum]
  rw [pinPart, pinMean, mul_assoc, mul_comm (part _ _), average_mul_part]
  congr!

lemma correlation_split (J : V → V → ℝ) (h : V → ℝ) (u v : V) :
    correlation J h u v =
      (pinPart J h v true * pinMean J h v true u -
        pinPart J h v false * pinMean J h v false u) / part J h := by
  unfold correlation average
  rw [sum_insert v]
  simp only [insertSpin_self, show sgn true = 1 from rfl, show sgn false = -1 from rfl,
    mul_one, mul_neg, Finset.sum_neg_distrib, sum_pin_first, sub_eq_add_neg]

lemma covariance_identity (J : V → V → ℝ) (h : V → ℝ) (u v : V) :
    correlation J h u v - mean J h u * mean J h v =
      (1 - (mean J h v) ^ 2) * (pinMean J h v true u - pinMean J h v false u) / 2 := by
  rw [correlation_split, mean_split J h v u, mean_self_split J h v, part_split J h v]
  have hz : pinPart J h v true + pinPart J h v false ≠ 0 :=
    (add_pos (pinPart_pos _ _ _ _) (pinPart_pos _ _ _ _)).ne'
  field_simp
  ring

/-- Conditioning at a site and applying the influence inequality bounds arbitrary-field covariance by zero-field correlation. -/
theorem covariance_le_zero_field (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (g : V → ℝ) (u v : V) :
    correlation J g u v - mean J g u * mean J g v ≤ correlation J 0 u v := by
  have hgap := pin_gap_comparison J hJ g v u
  have hnonneg := sub_nonneg.mpr (pinMean_mono J hJ g v u)
  have hprod := mul_nonneg (sq_nonneg (mean J g v)) hnonneg
  have hzero := covariance_identity J 0 u v
  simp only [mean_zero, zero_mul, sub_zero, zero_pow (by decide : 2 ≠ 0),
    sub_zero, one_mul] at hzero
  rw [covariance_identity]
  calc
    _ ≤ (pinMean J g v true u - pinMean J g v false u) / 2 := by nlinarith
    _ ≤ (pinMean J 0 v true u - pinMean J 0 v false u) / 2 := by linarith
    _ = correlation J 0 u v := hzero.symm

end

end BufferedIsing.DSS

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing OAI.BufferedIsing.DSS
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V]

theorem solution (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (g : V → ℝ) (u v : V) :
    correlation J g u v - mean J g u * mean J g v ≤ correlation J 0 u v := by
  first
    | exact OAI.BufferedIsing.DSS.covariance_le_zero_field J hJ g u v
    | exact OAI.BufferedIsing.DSS.covariance_le_zero_field
    | (apply OAI.BufferedIsing.DSS.covariance_le_zero_field <;> assumption)
    | (intros; apply OAI.BufferedIsing.DSS.covariance_le_zero_field <;> assumption)
