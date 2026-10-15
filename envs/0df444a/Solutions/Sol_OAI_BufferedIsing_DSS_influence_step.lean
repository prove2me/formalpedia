-- Prove2me | solution 1 for OAI.BufferedIsing.DSS.influence_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:58:51.752397+00:00
-- url     : https://prove2.me/submissions/8a8e5b22-35ee-4821-8ad8-1e6bebf620c2

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Influence.lean:L38-L113
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.DSS.influence_step. The node keeps its source
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
import Theorems.Thm_OAI_BufferedIsing_DSS_interpolation
import Theorems.Thm_OAI_BufferedIsing_DSS_mean_field_update
import Theorems.Thm_OAI_BufferedIsing_DSS_mean_mono

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
lemma sgn_le_one (b : Bool) : sgn b ≤ 1 := by cases b <;> norm_num [sgn]
lemma neg_one_le_sgn (b : Bool) : -1 ≤ sgn b := by cases b <;> norm_num [sgn]
lemma average_const (J : V → V → ℝ) (h : V → ℝ) (c : ℝ) :
    average J h (fun _ => c) = c := by
  unfold average
  rw [← Finset.sum_mul]
  exact mul_div_cancel_left₀ c (part_pos J h).ne'

lemma mean_lt_one (J : V → V → ℝ) (h : V → ℝ) (v : V) : mean J h v < 1 := by
  classical
  rw [mean, average, div_lt_one (part_pos J h)]
  apply Finset.sum_lt_sum
  · intro σ _
    exact mul_le_of_le_one_right (mass_pos J h σ).le (sgn_le_one _)
  · refine ⟨fun _ => false, Finset.mem_univ _, ?_⟩
    simp only [sgn, Bool.false_eq_true, ↓reduceIte]
    nlinarith [mass_pos J h (fun _ => false)]

lemma neg_one_lt_mean (J : V → V → ℝ) (h : V → ℝ) (v : V) : -1 < mean J h v := by
  classical
  rw [mean, average, lt_div_iff₀ (part_pos J h)]
  rw [part, Finset.mul_sum]
  apply Finset.sum_lt_sum
  · intro σ _
    nlinarith [neg_one_le_sgn (σ v), mass_pos J h σ]
  · refine ⟨fun _ => true, Finset.mem_univ _, ?_⟩
    simp only [sgn, ↓reduceIte]
    nlinarith [mass_pos J h (fun _ => true)]

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

lemma mean_affine (J : V → V → ℝ) (h : V → ℝ) (v o : V) :
    mean J h o = (pinMean J h v true o + pinMean J h v false o) / 2 +
      mean J h v * (pinMean J h v true o - pinMean J h v false o) / 2 := by
  rw [mean_split J h v o, mean_self_split J h v, part_split J h v]
  have hz : pinPart J h v true + pinPart J h v false ≠ 0 :=
    (add_pos (pinPart_pos _ _ _ _) (pinPart_pos _ _ _ _)).ne'
  field_simp
  ring

omit [Fintype V] in
lemma removedField_shift (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool) (t : ℝ) :
    removedField J (h + fieldAt v t) v b = removedField J h v b := by
  ext u
  simp [removedField, u.property]

lemma pinMean_shift (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool) (o : V) (t : ℝ) :
    pinMean J (h + fieldAt v t) v b o = pinMean J h v b o := by
  simp only [pinMean, removedField_shift]

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

lemma mean_nonneg (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (h : V → ℝ) (hh : 0 ≤ h) (v : V) : 0 ≤ mean J h v := by
  simpa only [mean_zero] using mean_mono J hJ 0 h hh v

lemma mean_mixture_identity (J : V → V → ℝ) (h : V → ℝ) (v o : V)
    (t s α : ℝ) (b : Bool) :
    mean J (h + fieldAt v t) o -
      (α * mean J (h + fieldAt v s) o + (1 - α) * pinMean J h v b o) =
    (mean J (h + fieldAt v t) v -
      (α * mean J (h + fieldAt v s) v + (1 - α) * sgn b)) *
      (pinMean J h v true o - pinMean J h v false o) / 2 := by
  rw [mean_affine J (h + fieldAt v t) v o, mean_affine J (h + fieldAt v s) v o]
  simp only [pinMean_shift]
  cases b <;> norm_num [sgn] <;> ring

lemma mean_mixture_le (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (h : V → ℝ) (v o : V) (t s α : ℝ) (b : Bool)
    (H : mean J (h + fieldAt v t) v ≤
      α * mean J (h + fieldAt v s) v + (1 - α) * sgn b) :
    mean J (h + fieldAt v t) o ≤
      α * mean J (h + fieldAt v s) o + (1 - α) * pinMean J h v b o := by
  have hh := mean_mixture_identity J h v o t s α b
  have hd := sub_nonneg.mpr (pinMean_mono J hJ h v o)
  have hp := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr H) hd
  linarith

lemma mean_mixture_ge (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (h : V → ℝ) (v o : V) (t s α : ℝ) (b : Bool)
    (H : α * mean J (h + fieldAt v s) v + (1 - α) * sgn b ≤
      mean J (h + fieldAt v t) v) :
    α * mean J (h + fieldAt v s) o + (1 - α) * pinMean J h v b o ≤
      mean J (h + fieldAt v t) o := by
  have hh := mean_mixture_identity J h v o t s α b
  have hd := sub_nonneg.mpr (pinMean_mono J hJ h v o)
  have hp := mul_nonneg (sub_nonneg.mpr H) hd
  linarith

lemma mean_mixture_eq (J : V → V → ℝ) (h : V → ℝ) (v o : V) (t s α : ℝ) (b : Bool)
    (H : mean J (h + fieldAt v t) v =
      α * mean J (h + fieldAt v s) v + (1 - α) * sgn b) :
    mean J (h + fieldAt v t) o =
      α * mean J (h + fieldAt v s) o + (1 - α) * pinMean J h v b o := by
  have hh := mean_mixture_identity J h v o t s α b
  rw [H, sub_self, zero_mul, zero_div] at hh
  exact sub_eq_zero.mp hh

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

lemma tanh_nonneg_of_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Real.tanh t := by
  rw [Real.tanh_eq]
  exact div_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith)))
    (add_pos (Real.exp_pos _) (Real.exp_pos _)).le

lemma reference_update {z c : ℝ} (hc : 1 + z * c ≠ 0) :
    update z c = ((1 - c) / (1 + z * c)) * z + (1 - (1 - c) / (1 + z * c)) := by
  dsimp [update]
  field_simp
  ring

lemma update_neg (a c : ℝ) : update (-a) (-c) = -update a c := by
  simp only [update, neg_mul_neg]
  ring

lemma mixture_weight_range {z c : ℝ} (hz : 0 ≤ z) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 ≤ (1 - c) / (1 + z * c) ∧ (1 - c) / (1 + z * c) ≤ 1 := by
  have hden : 0 < 1 + z * c := by nlinarith [mul_nonneg hz hc0]
  constructor
  · exact div_nonneg (by linarith) hden.le
  · apply (div_le_one hden).mpr
    nlinarith [mul_nonneg hz hc0]

/-- The induction step combines bounds for a smaller increment support and for pinned gaps. -/
lemma influence_step (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (g h : V → ℝ) (hh : 0 ≤ h) (v o : V) (t : ℝ) (ht : 0 ≤ t)
    (Hfield : ∀ (g' : V → ℝ) (o' : V),
      mean J (g' + h) o' - mean J (g' - h) o' ≤ mean J h o' - mean J (-h) o')
    (Hpin : pinMean J (g + h) v true o - pinMean J (g - h) v false o ≤
      pinMean J h v true o - pinMean J (-h) v false o) :
    mean J ((g + h) + fieldAt v t) o - mean J ((g - h) + fieldAt v (-t)) o ≤
      mean J (h + fieldAt v t) o - mean J ((-h) + fieldAt v (-t)) o := by
  let a := mean J (g + h) v
  let b := mean J (g - h) v
  let z := mean J h v
  let c := Real.tanh t
  let α := (1 - c) / (1 + z * c)
  have ha : -1 < a ∧ a < 1 := ⟨neg_one_lt_mean _ _ _, mean_lt_one _ _ _⟩
  have hb : -1 < b ∧ b < 1 := ⟨neg_one_lt_mean _ _ _, mean_lt_one _ _ _⟩
  have hz0 : 0 ≤ z := mean_nonneg J hJ h hh v
  have hz1 : z < 1 := mean_lt_one J h v
  have hc : 0 ≤ c ∧ c < 1 := ⟨tanh_nonneg_of_nonneg ht, Real.tanh_lt_one t⟩
  have hab : b ≤ a := by
    apply mean_mono J hJ
    intro u
    dsimp
    exact le_trans (sub_le_self _ (hh u)) (le_add_of_nonneg_right (hh u))
  have hgap : a - b ≤ 2 * z := by
    have H := Hfield g v
    rw [mean_neg] at H
    dsimp [a, b, z]
    linarith
  obtain ⟨d, hd0, hd1, Hup, Hlo⟩ := interpolation ha hb hab hc hz0 hgap
  let s := Real.artanh d
  have hs : Real.tanh s = d := Real.tanh_artanh ⟨hd0, hd1⟩
  have hα : 0 ≤ α ∧ α ≤ 1 := mixture_weight_range hz0 hc.1 hc.2
  have Up : mean J ((g + h) + fieldAt v t) o ≤
      α * mean J ((g + h) + fieldAt v s) o + (1 - α) * pinMean J (g + h) v true o := by
    apply mean_mixture_le J hJ
    rw [mean_field_update, mean_field_update, hs]
    simpa only [sgn, ↓reduceIte, mul_one, update, a, α, c] using Hup
  have Lo : α * mean J ((g - h) + fieldAt v s) o + (1 - α) * pinMean J (g - h) v false o ≤
      mean J ((g - h) + fieldAt v (-t)) o := by
    apply mean_mixture_ge J hJ
    rw [mean_field_update, mean_field_update, Real.tanh_neg, hs]
    simpa only [sgn, Bool.false_eq_true, ↓reduceIte, mul_neg_one, sub_eq_add_neg,
      update, b, α, c] using Hlo
  have hzden : 1 + z * c ≠ 0 := (by nlinarith [mul_nonneg hz0 hc.1] : 0 < 1 + z * c).ne'
  have RefUp : mean J (h + fieldAt v t) o =
      α * mean J h o + (1 - α) * pinMean J h v true o := by
    have H := mean_mixture_eq J h v o t 0 α true
    simp only [fieldAt_zero, add_zero] at H
    apply H
    rw [mean_field_update]
    simpa only [sgn, ↓reduceIte, mul_one, update, z, α, c] using reference_update hzden
  have RefLo : mean J ((-h) + fieldAt v (-t)) o =
      α * mean J (-h) o + (1 - α) * pinMean J (-h) v false o := by
    have H := mean_mixture_eq J (-h) v o (-t) 0 α false
    simp only [fieldAt_zero, add_zero] at H
    apply H
    rw [mean_field_update, mean_neg, Real.tanh_neg]
    have He : update (-z) (-c) = α * (-z) - (1 - α) := by
      rw [update_neg, reference_update hzden]
      dsimp [α]
      ring
    simpa only [sgn, Bool.false_eq_true, ↓reduceIte, mul_neg_one, sub_eq_add_neg,
      update, z, α, c] using He
  have Hcommon : mean J ((g + h) + fieldAt v s) o - mean J ((g - h) + fieldAt v s) o ≤
      mean J h o - mean J (-h) o := by
    convert Hfield (g + fieldAt v s) o using 1
    congr 2 <;> ext u <;> simp <;> ring
  calc
    _ ≤ α * (mean J ((g + h) + fieldAt v s) o - mean J ((g - h) + fieldAt v s) o) +
        (1 - α) * (pinMean J (g + h) v true o - pinMean J (g - h) v false o) := by linarith
    _ ≤ α * (mean J h o - mean J (-h) o) +
        (1 - α) * (pinMean J h v true o - pinMean J (-h) v false o) :=
      add_le_add (mul_le_mul_of_nonneg_left Hcommon hα.1)
        (mul_le_mul_of_nonneg_left Hpin (sub_nonneg.mpr hα.2))
    _ = _ := by rw [RefUp, RefLo]; ring

end

end BufferedIsing.DSS

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing OAI.BufferedIsing.DSS
open scoped BigOperators Classical
universe u
variable {V : Type u} [Fintype V]

theorem solution (J : V → V → ℝ) (hJ : ∀ u v, 0 ≤ J u v)
    (g h : V → ℝ) (hh : 0 ≤ h) (v o : V) (t : ℝ) (ht : 0 ≤ t)
    (Hfield : ∀ (g' : V → ℝ) (o' : V),
      mean J (g' + h) o' - mean J (g' - h) o' ≤ mean J h o' - mean J (-h) o')
    (Hpin : pinMean J (g + h) v true o - pinMean J (g - h) v false o ≤
      pinMean J h v true o - pinMean J (-h) v false o) :
    mean J ((g + h) + fieldAt v t) o - mean J ((g - h) + fieldAt v (-t)) o ≤
      mean J (h + fieldAt v t) o - mean J ((-h) + fieldAt v (-t)) o := by
  first
    | exact OAI.BufferedIsing.DSS.influence_step J hJ g h hh v o t ht Hfield Hpin
    | exact OAI.BufferedIsing.DSS.influence_step
    | (apply OAI.BufferedIsing.DSS.influence_step <;> assumption)
    | (intros; apply OAI.BufferedIsing.DSS.influence_step <;> assumption)
