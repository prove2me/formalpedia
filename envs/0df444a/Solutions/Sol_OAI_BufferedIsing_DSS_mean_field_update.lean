-- Prove2me | solution 1 for OAI.BufferedIsing.DSS.mean_field_update
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:56:41.542304+00:00
-- url     : https://prove2.me/submissions/8ba08ced-66c2-4c2a-965a-f5e801456a74

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/FieldUpdate.lean:L171-L186
-- (upload_full_project.md Phase 4): solution for node OAI.BufferedIsing.DSS.mean_field_update. The node keeps its source
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

omit [Fintype V] in
lemma removedField_shift (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool) (t : ℝ) :
    removedField J (h + fieldAt v t) v b = removedField J h v b := by
  ext u
  simp [removedField, u.property]

lemma pinPart_shift (J : V → V → ℝ) (h : V → ℝ) (v : V) (b : Bool) (t : ℝ) :
    pinPart J (h + fieldAt v t) v b = pinPart J h v b * Real.exp (t * sgn b) := by
  simp only [pinPart, removedField_shift, Pi.add_apply, fieldAt_self, add_mul,
    ← add_assoc, Real.exp_add]
  ring

lemma mean_field_update (J : V → V → ℝ) (h : V → ℝ) (v : V) (t : ℝ) :
    mean J (h + fieldAt v t) v = (mean J h v + Real.tanh t) /
      (1 + mean J h v * Real.tanh t) := by
  rw [mean_self_split J (h + fieldAt v t) v, mean_self_split J h v]
  simp only [pinPart_shift, sgn, ↓reduceIte, Bool.false_eq_true, mul_one, mul_neg_one]
  rw [Real.tanh_eq]
  have hp := pinPart_pos J h v true
  have hm := pinPart_pos J h v false
  have he := Real.exp_pos t
  have hf := Real.exp_pos (-t)
  have hsum : pinPart J h v true + pinPart J h v false ≠ 0 := (add_pos hp hm).ne'
  have hexp : Real.exp t + Real.exp (-t) ≠ 0 := (add_pos he hf).ne'
  field_simp
  ring_nf
  field_simp
  ring

end

end BufferedIsing.DSS

end OAI

-- ---- platform node ----
open OAI OAI.BufferedIsing OAI.BufferedIsing.DSS
open scoped BigOperators Classical
variable {V : Type*} [Fintype V]

theorem solution (J : V → V → ℝ) (h : V → ℝ) (v : V) (t : ℝ) :
    mean J (h + fieldAt v t) v = (mean J h v + Real.tanh t) /
      (1 + mean J h v * Real.tanh t) := by
  first
    | exact OAI.BufferedIsing.DSS.mean_field_update J h v t
    | exact OAI.BufferedIsing.DSS.mean_field_update
    | (apply OAI.BufferedIsing.DSS.mean_field_update <;> assumption)
    | (intros; apply OAI.BufferedIsing.DSS.mean_field_update <;> assumption)
