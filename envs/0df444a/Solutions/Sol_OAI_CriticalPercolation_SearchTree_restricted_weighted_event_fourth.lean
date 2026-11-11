-- Prove2me | solution 1 for OAI.CriticalPercolation.SearchTree.restricted_weighted_event_fourth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:25:26.758254+00:00
-- url     : https://prove2.me/submissions/bf682721-cdb6-4385-bd21-df8acfd71e27

import Mathlib
import Definitions.Def_OAIQ228B002

section
-- module Solutions.Q228_CP.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Density
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
open Set

namespace CriticalPercolation.FiniteProduct
variable {E A : Type*} [Fintype E] [Fintype A]

lemma sum_density [DecidableEq E] (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) :
    ∑ ω, density w ω = 1 := by
  classical
  unfold density
  rw [← Fintype.prod_sum]
  simp [h]

lemma expect_const (w : E → A → ℝ) (h : ∀ e, ∑ a, w e a = 1) (c : ℝ) :
    expect w (fun _ => c) = c := by
  classical
  rw [expect, ← Finset.sum_mul, sum_density w h, one_mul]

lemma expect_add (w : E → A → ℝ) (f g : (E → A) → ℝ) :
    expect w (fun ω => f ω + g ω) = expect w f + expect w g := by
  classical
  simp [expect, mul_add, Finset.sum_add_distrib]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_FiniteProductPin
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E A : Type*} [Fintype E] [Fintype A]

omit [Fintype E] [Fintype A] in
lemma pin_nonneg (w : E → A → ℝ) (hw : ∀ e a, 0 ≤ w e a) (e : E) (b : A) :
    ∀ j a, 0 ≤ pin w e b j a := by
  intro j a
  by_cases h : j = e
  · subst j; simp [pin]; split_ifs <;> norm_num
  · simpa [pin,h] using hw j a

omit [Fintype E] in
lemma pin_normalized (w : E → A → ℝ) (hw : ∀ e, ∑ a, w e a = 1) (e : E) (b : A) :
    ∀ j, ∑ a, pin w e b j a = 1 := by
  intro j
  by_cases h : j = e
  · subst j; simp [pin]
  · simpa [pin,h] using hw j

omit [Fintype A] in
lemma density_pin (w : E → A → ℝ) (e : E) (b : A) (ω : E → A) :
    density (pin w e b) ω =
      (if ω e = b then 1 else 0)*∏ j ∈ (Finset.univ : Finset E).erase e, w j (ω j) := by
  rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e)]
  simp only [pin,Function.update_self]
  have he : (∏ j ∈ (Finset.univ : Finset E).erase e, Function.update w e
      (fun a => if a = b then 1 else 0) j (ω j)) =
      ∏ j ∈ (Finset.univ : Finset E).erase e, w j (ω j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [he,mul_comm]

lemma expect_mask_pin (w : E → A → ℝ) (e : E) (b : A) (f : (E → A) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) = w e b*expect (pin w e b) f := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [density_pin]
  dsimp only
  by_cases h : ω e = b
  · rw [ite_eq_left h,ite_eq_left h,one_mul]
    rw [density,← Finset.prod_erase_mul _ _ (Finset.mem_univ e),h]
    ring
  · simp [h]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_Potential
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.FiniteProduct
open scoped Classical

variable {E : Type*} [Fintype E]

lemma expect_prop_mask_pin (w : E → Prop → ℝ) (e : E) (b : Prop) (f : (E → Prop) → ℝ) :
    expect w (fun ω => if ω e = b then f ω else 0) = w e b*expect (pin w e b) f := by
  convert expect_mask_pin w e b f using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext ω
  by_cases h : ω e = b <;> simp [h]

end CriticalPercolation.FiniteProduct

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Exploration_Score
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct

variable {E R : Type*} [Fintype E]

lemma expect_prop_ite (w : E → Prop → ℝ) (e : E) (f g : Set E → ℝ) :
    expect w (fun ω => if ω e then f ω else g ω) =
      w e True*expect (pin w e True) f+w e False*expect (pin w e False) g := by
  calc
    _ = expect w (fun ω => (if ω e = True then f ω else 0) +
        (if ω e = False then g ω else 0)) := by
      congr 1
      funext ω
      by_cases h : ω e <;> simp [h]
    _ = _ := by
      rw [expect_add]
      apply congrArg₂ (· + ·)
      · convert expect_prop_mask_pin w e True f using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]
      · convert expect_prop_mask_pin w e False g using 1
        all_goals try with_reducible_and_instances rfl
        congr 1
        funext ω
        by_cases h : ω e <;> simp [h]

end CriticalPercolation.SearchTree

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype E] [DecidableEq V] in
lemma fresh_pin (w : E → Prop → ℝ) (p : ℝ) (read : Finset E) (hf : Fresh w p read)
    (e : E) (b : Prop) : Fresh (pin w e b) p (insert e read) := by
  intro j hj
  have hj' : j ≠ e ∧ j ∉ read := by simpa only [Finset.mem_insert,not_or] using hj
  have hje : j ≠ e := hj'.1
  unfold pin
  simp only [Function.update,dite_eq_right hje]
  exact hf j hj'.2

end CriticalPercolation.LazyDFS

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedIntegralBand
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace CriticalPercolation
variable {X : Type*} [MeasurableSpace X]

lemma lintegral_fractional_fourth (μ : Measure X) (f h : X → ℝ≥0∞)
    (hf : AEMeasurable f μ) (hh : AEMeasurable h μ) (hh1 : ∀ x, h x≤1) :
    (∫⁻ x, f x*h x ∂μ)^4 ≤ (∫⁻ x, (f x)^4 ∂μ)*(∫⁻ x, h x ∂μ)^3 := by
  have hpq : (4:ℝ).HolderConjugate (4/3) := Real.holderConjugate_iff.mpr (by norm_num)
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf hh
  have P : (∫⁻ x, h x^(4/3:ℝ) ∂μ) ≤ ∫⁻ x, h x ∂μ :=
    lintegral_mono (fun x => ENNReal.rpow_le_self_of_le_one (hh1 x) (by norm_num))
  have H' : (∫⁻ x, f x*h x ∂μ) ≤
      (∫⁻ x, (f x)^4 ∂μ)^(1/4:ℝ)*(∫⁻ x, h x ∂μ)^(3/4:ℝ) := by
    calc _ ≤ _ := H
         _ ≤ _ := by
           norm_num only [show (1/(4/3:ℝ))=3/4 by norm_num,ENNReal.rpow_ofNat]
           gcongr
  have H4 := ENNReal.rpow_le_rpow H' (by norm_num : (0:ℝ)≤4)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ)≤4),
    ←ENNReal.rpow_mul,←ENNReal.rpow_mul] at H4
  simpa only [show (1/4:ℝ)*4=1 by norm_num,show (3/4:ℝ)*4=3 by norm_num,
    ENNReal.rpow_one,ENNReal.rpow_ofNat] using H4

end CriticalPercolation
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedQuery
attribute [-instance] _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical

namespace CriticalPercolation.SearchTree
open FiniteProduct

variable {E R : Type*}

lemma quadraticCost_nonneg (a : E → ℝ) (t : SearchTree E R) (ω : E → Prop) :
    0 ≤ t.quadraticCost a ω := by
  induction t with
  | done r => rfl
  | ask e l r hl hr =>
    simp only [quadraticCost]
    split_ifs <;> positivity

lemma takeQuadratic_sum_eq (a : E → ℝ) (p : ℝ) (t : SearchTree E R)
    (B : ℝ) (ω : E → Prop) (h : t.quadraticCost a ω ≤ B) :
    (t.takeQuadratic a B).weightedSum a p ω = t.weightedSum a p ω := by
  induction t generalizing B with
  | done r => rfl
  | ask e l r hl hr =>
    have ha : (a e)^2 ≤ B := by
      simp only [quadraticCost] at h
      split_ifs at h <;> linarith [quadraticCost_nonneg a l ω,quadraticCost_nonneg a r ω]
    simp only [takeQuadratic,ite_eq_left ha,weightedSum]
    split_ifs with he
    · rw [hr]
      simp only [quadraticCost,ite_eq_left he] at h
      linarith
    · rw [hl]
      simp only [quadraticCost,ite_eq_right he] at h
      linarith

lemma fourthPotential_step (x a B δ : ℝ) (hB : a^2≤B) (hδ : δ^2≤a^2) :
    (x+δ)^4 + 7*(B-a^2)*(x+δ)^2 + 5*(B-a^2)^2 ≤
      x^4+7*B*x^2+5*B^2+(4*x^3+14*(B-a^2)*x)*δ := by
  have h4 : δ^4≤a^4 := by nlinarith [sq_nonneg (δ^2-a^2),sq_nonneg δ,sq_nonneg a]
  have hxx := mul_le_mul_of_nonneg_left hδ (sq_nonneg x)
  have hb := mul_le_mul_of_nonneg_left hδ (sub_nonneg.mpr hB)
  have hba := mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hB)
  nlinarith [sq_nonneg (x*δ-2*δ^2)]

variable [Fintype E] [DecidableEq E]

lemma expected_takeQuadratic_fourth_shift (a : E → ℝ) (t : SearchTree E R)
    (used : Finset E) (ht : t.Valid used) (p : ℝ) (hp : p∈Set.Icc 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p used) (B : ℝ) (hB : 0≤B) (x : ℝ) :
    expect w (fun ω => (x+(t.takeQuadratic a B).weightedSum a p ω)^4) ≤
      x^4+7*B*x^2+5*B^2 := by
  induction t generalizing used w B x with
  | done r =>
    simp only [takeQuadratic,weightedSum,add_zero,expect_const w hw]
    nlinarith [sq_nonneg B,mul_nonneg hB (sq_nonneg x)]
  | ask e l r hl hr =>
    by_cases ha : (a e)^2≤B
    · have hB' : 0≤B-(a e)^2 := sub_nonneg.mpr ha
      have h0 := hl _ ht.2.1 (pin w e False) (pin_normalized w hw e False)
        (pin_nonneg w hn e False) (LazyDFS.fresh_pin w p used hf e False) _ hB' (x-a e*p)
      have h1 := hr _ ht.2.2 (pin w e True) (pin_normalized w hw e True)
        (pin_nonneg w hn e True) (LazyDFS.fresh_pin w p used hf e True) _ hB' (x+a e*(1-p))
      have he := hf e ht.1
      have hp0 : 0≤1-p^2 := by nlinarith [hp.1,hp.2]
      have hp1 : 0≤1-(1-p)^2 := by nlinarith [hp.1,hp.2]
      have hδ0 : (-a e*p)^2≤(a e)^2 := by
        nlinarith [mul_nonneg (sq_nonneg (a e)) hp0]
      have hδ1 : (a e*(1-p))^2≤(a e)^2 := by
        nlinarith [mul_nonneg (sq_nonneg (a e)) hp1]
      have g0 := fourthPotential_step x (a e) B (-a e*p) ha hδ0
      have g1 := fourthPotential_step x (a e) B (a e*(1-p)) ha hδ1
      have heq : (fun ω => (x+((.ask e l r : SearchTree E R).takeQuadratic a B).weightedSum a p ω)^4) =
          (fun ω => if ω e then ((x+a e*(1-p))+(r.takeQuadratic a (B-(a e)^2)).weightedSum a p ω)^4
            else ((x-a e*p)+(l.takeQuadratic a (B-(a e)^2)).weightedSum a p ω)^4) := by
        funext ω
        simp only [takeQuadratic,ite_eq_left ha,weightedSum]
        split_ifs <;> congr 1 <;> ring
      rw [heq]
      erw [expect_prop_ite]
      rw [he.1,he.2]
      have h0' := mul_le_mul_of_nonneg_left (h0.trans (by simpa only [sub_eq_add_neg,neg_mul] using g0))
        (sub_nonneg.mpr hp.2)
      have h1' := mul_le_mul_of_nonneg_left (h1.trans g1) hp.1
      nlinarith
    · simp only [takeQuadratic,ite_eq_right ha,weightedSum,add_zero,expect_const w hw]
      nlinarith [sq_nonneg B,mul_nonneg hB (sq_nonneg x)]

lemma expected_takeQuadratic_fourth (a : E → ℝ) (t : SearchTree E R)
    (used : Finset E) (ht : t.Valid used) (p : ℝ) (hp : p∈Set.Icc 0 1)
    (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b=1) (hn : ∀ e b, 0≤w e b)
    (hf : LazyDFS.Fresh w p used) (B : ℝ) (hB : 0≤B) :
    expect w (fun ω => ((t.takeQuadratic a B).weightedSum a p ω)^4) ≤ 5*B^2 := by
  simpa using expected_takeQuadratic_fourth_shift a t used ht p hp w hw hn hf B hB 0

end CriticalPercolation.SearchTree
end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_ProductMeasure_BitMeasure
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable _root_.OAI.CriticalPercolation.Priority.instFintypeOrder _root_.OAI.CriticalPercolation.QueryTree.leafFintype _root_.OAI.CriticalPercolation.QueryTree.nodeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation
namespace BernoulliProduct

lemma bitWeight_sum (p : unitInterval) : ∑ b, bitWeight p b = 1 := by
  simp [bitWeight]

lemma bitWeight_nonneg (p : unitInterval) (b : Prop) : 0 ≤ bitWeight p b := by
  unfold bitWeight
  split_ifs
  · exact p.property.1
  · exact sub_nonneg.mpr p.property.2

lemma bitMeasure_real_singleton (p : unitInterval) (b : Prop) :
    (bitMeasure p).real {b} = bitWeight p b := by
  by_cases hb : b
  · have he : b = True := propext (iff_true_intro hb)
    subst b
    simp [bitMeasure, bitWeight, measureReal_def]
  · have he : b = False := propext (iff_false_intro hb)
    subst b
    simp [bitMeasure, bitWeight, measureReal_def]

variable {E : Type*}

lemma integral_bits_eq_expect [Fintype E] (q : E → unitInterval) (f : (E → Prop) → ℝ) :
    (∫ ω, f ω ∂(Measure.infinitePi fun e => bitMeasure (q e))) =
      FiniteProduct.expect (fun e => bitWeight (q e)) f := by
  rw [Measure.infinitePi_eq_pi, integral_fintype Integrable.of_finite]
  unfold FiniteProduct.expect FiniteProduct.density
  apply Finset.sum_congr rfl
  intro ω _
  rw [smul_eq_mul]
  congr 1
  simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun e _ => bitMeasure_real_singleton (q e) (ω e))

lemma integral_law_eq_expect [Fintype E] (q : E → unitInterval) (f : Set E → ℝ) :
    (∫ ω, f ω ∂law q) =
      FiniteProduct.expect (fun e => bitWeight (q e)) (fun ω => f {e | ω e}) := by
  rw [law, integral_map MeasurableEquiv.setOfPred.measurable.aemeasurable
    Integrable.of_finite.aestronglyMeasurable, integral_bits_eq_expect]
  rfl

lemma law_map_restrict (q : E → unitInterval) (s : Set E) :
    (law q).map (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set s) =
      law (fun e : s => q e) := by
  have hmeas : Measurable (fun ω : Set E => (Subtype.val ⁻¹' ω : Set s)) :=
    measurable_set_iff.mpr (fun bond => measurable_set_mem bond.val)
  unfold law
  rw [Measure.map_map hmeas MeasurableEquiv.setOfPred.measurable]
  have hcomp : (fun ω : Set E => Subtype.val ⁻¹' ω : Set E → Set s) ∘
      MeasurableEquiv.setOfPred =
      MeasurableEquiv.setOfPred ∘ s.domRestrict := rfl
  rw [hcomp, ← Measure.map_map MeasurableEquiv.setOfPred.measurable (by fun_prop),
    Measure.infinitePi_map_restrict']

end BernoulliProduct
end CriticalPercolation
open Set
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedQueryLaw
attribute [-instance] _root_.OAI.CriticalPercolation.LocalProjective.spaceMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.SearchTree
variable {E R : Type*} [Fintype E] [DecidableEq E]

lemma lintegral_takeQuadratic_fourth (a : E → ℝ) (t : SearchTree E R)
    (ht : t.Valid ∅) (p : unitInterval) (B : ℝ) (hB : 0≤B) :
    (∫⁻ ω : Set E, ENNReal.ofReal (|(t.takeQuadratic a B).weightedSum a p ω|)^4
      ∂BernoulliProduct.law (fun _ => p)) ≤ ENNReal.ofReal (5*B^2) := by
  have h0 (ω : Set E) : (|(t.takeQuadratic a B).weightedSum a p ω|)^4 =
      ((t.takeQuadratic a B).weightedSum a p ω)^4 := by rw [pow_abs,abs_of_nonneg (by positivity)]
  simp only [←ENNReal.ofReal_pow (abs_nonneg _),h0]
  rw [←ofReal_integral_eq_lintegral_ofReal Integrable.of_finite
    (Filter.Eventually.of_forall (fun _ => by positivity)),BernoulliProduct.integral_law_eq_expect]
  apply ENNReal.ofReal_le_ofReal
  exact expected_takeQuadratic_fourth a t ∅ ht p p.2 _
    (fun _ => BernoulliProduct.bitWeight_sum p) (fun _ => BernoulliProduct.bitWeight_nonneg p)
    (fun _ _ => ⟨by simp [BernoulliProduct.bitWeight],by simp [BernoulliProduct.bitWeight]⟩) B hB

end CriticalPercolation.SearchTree
namespace CriticalPercolation.BernoulliProduct
variable {E : Type*}

lemma lintegral_restrict (p : unitInterval) (s : Set E)
    (F : Set s → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω : Set E, F (Subtype.val ⁻¹' ω) ∂law (fun _ => p)) =
      ∫⁻ ω : Set s, F ω ∂law (fun _ => p) := by
  rw [←law_map_restrict (fun _ : E => p) s]
  exact (lintegral_map hF (Measurable.of_eval (fun edge => measurable_set_mem edge.val))).symm

end CriticalPercolation.BernoulliProduct
namespace CriticalPercolation.SearchTree
variable {E R : Type*}

theorem restricted_weighted_event_fourth_oai (s : Set E) [Fintype s] [DecidableEq s]
    (a : s → ℝ) (t : SearchTree s R) (ht : t.Valid ∅) (p : unitInterval)
    (B : ℝ) (hB : 0≤B) (h : Set E → ℝ≥0∞) (hm : Measurable h) (hh1 : ∀ ω, h ω≤1)
    (hcost : ∀ ω, h ω≠0 → t.quadraticCost a (Subtype.val ⁻¹' ω)≤B) :
    (∫⁻ ω : Set E, ENNReal.ofReal |t.weightedSum a p (Subtype.val ⁻¹' ω)| *h ω
      ∂BernoulliProduct.law (fun _ => p))^4 ≤
      ENNReal.ofReal (5*B^2)*(∫⁻ ω, h ω ∂BernoulliProduct.law (fun _ => p))^3 := by
  let f : Set E → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal |(t.takeQuadratic a B).weightedSum a p (Subtype.val ⁻¹' ω)|
  have hf0 : Measurable (fun η : Set s =>
      ENNReal.ofReal |(t.takeQuadratic a B).weightedSum a p η|) := measurable_of_finite _
  have hf : Measurable f := hf0.comp
    (Measurable.of_eval (fun edge : s => measurable_set_mem edge.val))
  have heq : (fun ω : Set E => ENNReal.ofReal |t.weightedSum a p (Subtype.val ⁻¹' ω)| *h ω) =
      fun ω => f ω*h ω := by
    funext ω
    by_cases hh : h ω=0
    · simp [hh]
    · rw [show f ω= ENNReal.ofReal |t.weightedSum a p (Subtype.val ⁻¹' ω)| by
        dsimp only [f]
        exact congrArg (fun z : ℝ => ENNReal.ofReal |z|)
          (t.takeQuadratic_sum_eq a p B (fun e => e.val∈ω) (hcost ω hh))]
  rw [heq]
  apply (CriticalPercolation.lintegral_fractional_fourth _ f h hf.aemeasurable hm.aemeasurable hh1).trans
  apply mul_le_mul_left
  change (∫⁻ ω : Set E, (ENNReal.ofReal
    |(t.takeQuadratic a B).weightedSum a p (Subtype.val ⁻¹' ω)|)^4
      ∂BernoulliProduct.law (fun _ => p)) ≤ _
  rw [BernoulliProduct.lintegral_restrict p s
    (fun η : Set s => (ENNReal.ofReal |(t.takeQuadratic a B).weightedSum a p η|)^4)
    (measurable_of_finite _)]
  exact lintegral_takeQuadratic_fourth a t ht p B hB

end CriticalPercolation.SearchTree
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.SearchTree.restricted_weighted_event_fourth_oai.{u_1, u_2} := @OAI.CriticalPercolation.SearchTree.restricted_weighted_event_fourth_oai.{u_1, u_2}
