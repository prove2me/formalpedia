-- Prove2me | solution 1 for NarrowDNF.adaptive_approximation_to_dnf
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:32:50.260299+00:00
-- url     : https://prove2.me/submissions/18c79b68-123f-404b-a77c-a35c461d9026

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ActivationLoad
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_AdaptiveShift
import Definitions.Def_NarrowDNF_CertificateBounds
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_MainStatements
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_Activation_controlled_monotonicization
import Theorems.Thm_NarrowDNF_Activation_positive_certificate
import Theorems.Thm_NarrowDNF_Activation_truncatedDNF_error_bound

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure

section


/-!
# Bias-matched shifts on a Boolean fiber

This file proves the two-point calculation used in Lemma 3.1 of
the 2026-11-06 STOC revision. The probability of the upper shift is `1 - p` and the
probability of the lower shift is `p`; the input fiber has the same bias `p`.

The error theorem is a conditional, single-fiber statement. Passing to an
arbitrary Boolean cube requires a separate summation/integration argument.
-/

namespace NarrowDNF.FiberShift

@[simp] private theorem true_not_le_false : ¬ ((true : Bool) ≤ false) := by decide



























end NarrowDNF.FiberShift


end

section


/-!
# Coordinate shifts on Boolean functions

The unbranched shift formulas are equivalent to the two-slice definitions in
the shift definitions preceding Lemma 3.1 of the 2026-11-06 STOC revision, by Boolean idempotence. This file concerns
monotonicity; the global biased-error bound requires a separate finite-sum
argument.
-/

namespace NarrowDNF

variable {ι : Type*} [DecidableEq ι]









@[simp] private theorem upperShift_lowerInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    upperShift i v (lowerInput i x) = v (lowerInput i x) := by
  simp [upperShift, lowerInput]

@[simp] private theorem upperShift_upperInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    upperShift i v (upperInput i x) = (v (lowerInput i x) || v (upperInput i x)) := by
  simp [upperShift, lowerInput, upperInput, Bool.or_comm]

@[simp] private theorem lowerShift_lowerInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    lowerShift i v (lowerInput i x) = (v (lowerInput i x) && v (upperInput i x)) := by
  simp [lowerShift, lowerInput, upperInput]

@[simp] private theorem lowerShift_upperInput (i : ι) (v : Cube ι → Bool) (x : Cube ι) :
    lowerShift i v (upperInput i x) = v (upperInput i x) := by
  simp [lowerShift, upperInput]





































end NarrowDNF


end

section


/-!
# Adaptive atoms under shifts

The precise content of Lemma 3.2 of the 2026-11-06 STOC revision, including its
atom-recovery proof (formerly in Appendix B of arXiv:2609.00240v1).
All activations carry the locality field from `Activation`; no decoder or atom
recovery oracle is assumed. The unbranched formulas for shifts are equivalent
to the paper's two-slice formulas by Boolean idempotence.
-/

namespace NarrowDNF

variable {ι : Type*} [DecidableEq ι]





private theorem forceInput_mono (D : Finset ι) : Monotone (forceInput D) := by
  intro x y hxy i
  simp only [forceInput]
  split
  · exact le_rfl
  · exact hxy i



namespace Activation











private theorem force_increasing {J : Activation ι} (hJ : J.Increasing) (D : Finset ι) :
    (J.force D).Increasing := by
  intro S x y hxy
  exact hJ S (forceInput_mono D hxy)

















end Activation
end NarrowDNF


end

section


namespace NarrowDNF

variable {ι : Type*} [Fintype ι] [DecidableEq ι]





omit [Fintype ι] [DecidableEq ι] in
private theorem termHolds_mono (T : Finset ι) : Monotone (TermHolds T) := by
  intro x y hxy hx i hi
  have := hxy i
  cases hyi : y i
  · rw [hx i hi, hyi] at this
    exact False.elim ((by decide : ¬(true ≤ false)) this)
  · rfl

omit [Fintype ι] [DecidableEq ι] in
private theorem dnfHolds_mono (terms : Finset (Finset ι)) : Monotone (DNFHolds terms) := by
  intro x y hxy hx
  obtain ⟨T, hT, hxT⟩ := hx
  exact ⟨T, hT, termHolds_mono T hxy hxT⟩

namespace Activation





omit [DecidableEq ι] in
@[simp] private theorem mem_activeFinset (J : Activation ι) (x : Cube ι) (i : ι) :
    i ∈ J.activeFinset x ↔ i ∈ J.active x := by
  classical
  simp [activeFinset]

omit [DecidableEq ι] in
@[simp] private theorem mem_certificate (J : Activation ι) (x : Cube ι) (i : ι) :
    i ∈ J.certificate x ↔ i ∈ J.active x ∧ x i = true := by
  classical
  simp [certificate]





omit [DecidableEq ι] in
private theorem certificate_forces {J : Activation ι} (hJ : J.Increasing)
    {u : Cube ι → Bool} (hu : Monotone u) (hm : J.Measurable u)
    {x : Cube ι} (hx : u x = true) {y : Cube ι}
    (hy : TermHolds (J.certificate x) y) : u y = true := by
  apply positive_certificate hJ hu hm hx
  intro i hi hxi
  exact hy i ((mem_certificate J x i).mpr ⟨hi, hxi⟩)



private theorem truncatedTerms_width (J : Activation ι) (u : Cube ι → Bool) (w : ℕ)
    {T : Finset ι} (hT : T ∈ J.truncatedTerms u w) : T.card ≤ w := by
  classical
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hT
  exact (Finset.mem_filter.mp hx).2.2

private theorem truncatedTerms_sound {J : Activation ι} (hJ : J.Increasing)
    {u : Cube ι → Bool} (hu : Monotone u) (hm : J.Measurable u) (w : ℕ)
    {y : Cube ι} (hy : DNFHolds (J.truncatedTerms u w) y) : u y = true := by
  classical
  obtain ⟨T, hT, hyT⟩ := hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hT
  exact certificate_forces hJ hu hm (Finset.mem_filter.mp hx).2.1 hyT





end Activation
end NarrowDNF


end

section


namespace NarrowDNF
namespace Activation
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]



@[simp] private theorem truncatedDNF_eq_true (J : Activation ι) (u : Cube ι → Bool)
    (w : ℕ) (x : Cube ι) :
    J.truncatedDNF u w x = true ↔ DNFHolds (J.truncatedTerms u w) x := by
  classical simp [truncatedDNF]

private theorem truncatedDNF_monotone (J : Activation ι) (u : Cube ι → Bool) (w : ℕ) :
    Monotone (J.truncatedDNF u w) := by
  intro x y hxy
  cases hx : J.truncatedDNF u w x
  · exact Bool.false_le _
  · have hy := dnfHolds_mono (J.truncatedTerms u w) hxy
      ((truncatedDNF_eq_true J u w x).mp hx)
    rw [(truncatedDNF_eq_true J u w y).mpr hy]

private theorem truncatedDNF_le {J : Activation ι} (hJ : J.Increasing)
    {u : Cube ι → Bool} (hu : Monotone u) (hm : J.Measurable u) (w : ℕ) :
    J.truncatedDNF u w ≤ u := by
  intro x
  cases hx : J.truncatedDNF u w x
  · exact Bool.false_le _
  · rw [truncatedTerms_sound hJ hu hm w ((truncatedDNF_eq_true J u w x).mp hx)]





end Activation
end NarrowDNF


end

section


/-!
# Finite Bernoulli product probability

The probability model is an explicit finite sum of product weights. Algebraic
identities hold for every real parameter; positivity claims state `0 ≤ p ≤ 1`.
No theorem here assumes a probability law or an analytic input without proof.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.ProductMeasure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]



@[simp] private theorem bitWeight_false (p : ℝ) : bitWeight p false = 1 - p := rfl
@[simp] private theorem bitWeight_true (p : ℝ) : bitWeight p true = p := rfl









private theorem bitWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ bitWeight p b := by
  cases b <;> simp only [bitWeight_false, bitWeight_true]
  · exact sub_nonneg.mpr hp1
  · exact hp0

omit [DecidableEq ι] in
private theorem weight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ι → Bool) :
    0 ≤ weight p x :=
  Finset.prod_nonneg fun i _ => bitWeight_nonneg hp0 hp1 (x i)





/-- Finite distributivity for independently chosen coordinates. -/
private theorem sum_prod_coordinates {α : Type*} [Fintype α] (F : ι → α → ℝ) :
    (∑ x : ι → α, ∏ i, F i (x i)) = ∏ i, ∑ a, F i a := by
  classical
  simpa only [Fintype.piFinset_univ] using
    (Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset α)) F).symm

@[simp] private theorem sum_weight (p : ℝ) : ∑ x : ι → Bool, weight p x = 1 := by
  unfold weight
  rw [sum_prod_coordinates]
  simp

@[simp] private theorem expectation_const (p c : ℝ) : expectation (ι := ι) p (fun _ => c) = c := by
  simp [expectation, ← Finset.sum_mul]

@[simp] private theorem expectation_zero (p : ℝ) : expectation (ι := ι) p (fun _ => 0) = 0 :=
  expectation_const p 0

@[simp] private theorem expectation_one (p : ℝ) : expectation (ι := ι) p (fun _ => 1) = 1 :=
  expectation_const p 1

private theorem expectation_add (p : ℝ) (F G : (ι → Bool) → ℝ) :
    expectation p (fun x => F x + G x) = expectation p F + expectation p G := by
  simp [expectation, mul_add, Finset.sum_add_distrib]







private theorem expectation_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {F G : (ι → Bool) → ℝ} (hFG : ∀ x, F x ≤ G x) :
    expectation p F ≤ expectation p G :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hFG x) (weight_nonneg hp0 hp1 x)







@[simp] private theorem error_self (p : ℝ) (f : (ι → Bool) → Bool) : error p f f = 0 := by
  simp [error, probability]



private theorem error_triangle {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f g h : (ι → Bool) → Bool) : error p f h ≤ error p f g + error p g h := by
  unfold error probability
  rw [← expectation_add]
  apply expectation_mono hp0 hp1
  intro x
  cases hfx : f x <;> cases hgx : g x <;> cases hhx : h x <;> simp [hfx, hgx, hhx]





































end NarrowDNF.ProductMeasure

end

end

section


namespace NarrowDNF
namespace Activation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lemma 4.1 of the 2026-11-06 STOC revision, including its exact explicit DNF,
pointwise domination and both probability bounds. The closed bias interval
strengthens the paper's ambient interior-bias convention. -/
private theorem certificates_and_truncation {J : Activation ι} (hJ : J.Increasing)
    {u : Cube ι → Bool} (hu : Monotone u) (hm : J.Measurable u)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (w : ℕ) :
    (∀ x, u x = true → ∀ y, TermHolds (J.certificate x) y → u y = true) ∧
    (∀ T ∈ J.truncatedTerms u w, T.card ≤ w) ∧
    Monotone (J.truncatedDNF u w) ∧
    J.truncatedDNF u w ≤ u ∧
    ProductMeasure.error p u (J.truncatedDNF u w) ≤
      ProductMeasure.probability p (fun x => w < (J.certificate x).card) ∧
    ProductMeasure.probability p (fun x => w < (J.certificate x).card) ≤
      ProductMeasure.expectation p (fun x => ((J.activeFinset x).card : ℝ)) / (w + 1 : ℝ) := by
  refine ⟨?_, ?_, truncatedDNF_monotone J u w, truncatedDNF_le hJ hu hm w, ?_⟩
  · intro x hx y hy
    exact certificate_forces hJ hu hm hx hy
  · intro T hT
    exact truncatedTerms_width J u w hT
  · exact truncatedDNF_error_bound hJ hu hm w (ProductMeasure.weight p)
      (ProductMeasure.weight_nonneg hp0 hp1)

end Activation
end NarrowDNF


end

noncomputable section
open NarrowDNF
open ProductMeasure
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- The shift-certificate part of Theorem 1.2 with all actual structural inputs
exposed. `HatamiInput.lean` supplies the proved existence of these inputs. -/
theorem solution {p ε L : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hε : 0 < ε) (hL0 : 0 ≤ L) {d : ℕ} {f h : Cube ι → Bool}
    (hf : Monotone f) {J : Activation ι} (hJ : J.Increasing)
    (hd : J.ArityLE d) (hh : J.Measurable h)
    (he : error p f h ≤ ε/4) (hL : J.load p ≤ L) :
    ∃ terms : Finset (Finset ι),
      (∀ T ∈ terms, T.card ≤ Nat.ceil (4 * (2 : ℝ)^d * L / ε)) ∧
      error p f (evalDNF terms) ≤ ε := by
  classical
  have ha : (0 : ℝ) < ε/4 := by positivity
  obtain ⟨D, u, hu, hm, heu, hcost⟩ :=
    Activation.controlled_monotonicization hp0 hp1 ha.le hL0 hf hJ hd hh he hL (ε/4) ha
  let w := Nat.ceil (4 * (2 : ℝ)^d * L / ε)
  let terms := (J.force D).truncatedTerms u w
  refine ⟨terms, ?_, ?_⟩
  · exact fun T hT => Activation.truncatedTerms_width _ u w hT
  · have hcost' : expectation p (fun x => (((J.force D).activeFinset x).card : ℝ)) ≤
        2 * (2 : ℝ)^d * L := by
      have ha0 : ε/4 ≠ 0 := ne_of_gt ha
      rw [div_self ha0] at hcost
      have hp : (2-p)^d ≤ (2:ℝ)^d := pow_le_pow_left₀ (by linarith) (by linarith) d
      have hnon : (0:ℝ) ≤ L*2 := mul_nonneg hL0 (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hp hnon]
    have hbound := (Activation.certificates_and_truncation
      (Activation.force_increasing hJ D) hu hm p hp0.le hp1.le w).2.2.2.2
    have hceil : 4 * (2 : ℝ)^d * L / ε ≤ (w : ℝ) := Nat.le_ceil _
    have hbudget : 2 * (2 : ℝ)^d * L / (w+1 : ℝ) ≤ ε/2 := by
      apply (div_le_iff₀ (by positivity : (0:ℝ) < (w:ℝ)+1)).mpr
      have hmul := (div_le_iff₀ hε).mp hceil
      nlinarith
    have heug : error p u ((J.force D).truncatedDNF u w) ≤ ε/2 :=
      hbound.1.trans (hbound.2.trans ((div_le_div_of_nonneg_right hcost' (by positivity)).trans hbudget))
    have htriangle := error_triangle hp0.le hp1.le f u ((J.force D).truncatedDNF u w)
    change error p f ((J.force D).truncatedDNF u w) ≤ ε
    linarith
