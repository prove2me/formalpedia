-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedAffineProductMixed_primePower_event_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:39:28.681006+00:00
-- url     : https://prove2.me/submissions/33c6cfa7-764e-4ec4-95a0-554a1d8c2a50

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B247
import Definitions.Def_OAIE3v2B254
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineMixedModulusBad_probability_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteConditionedMass
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem eventProbability_nonneg {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (E : Ω → Prop) : 0 ≤ p.eventProbability E := by
  classical
  exact p.mean_nonneg (fun x => by split_ifs <;> norm_num)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EmbeddedFiniteConditioning
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem norm_complexMean_sub_le_weight_l1 {X : Type*} [Fintype X]
    (p q : FiniteProbabilityWeights X) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖p.complexMean f - q.complexMean f‖ ≤ ∑ x, |p.weight x - q.weight x| := by
  simp only [complexMean, ← Finset.sum_sub_distrib, ← sub_mul, ← Complex.ofReal_sub]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)).trans_eq (mul_one _)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductPMFMap
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem dependentProductPMF_apply {D : Type*} [Fintype D] {X : D → Type*}
    [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)] [∀ d, MeasurableSingletonClass (X d)]
    (p : ∀ d, PMF (X d)) (x : ∀ d, X d) : dependentProductPMF p x = ∏ d, p d (x d) := by
  simp only [dependentProductPMF, Measure.toPMF_apply, Measure.pi_singleton]
  exact Finset.prod_congr rfl (fun d _ => (p d).toMeasure_apply_singleton (x d) (measurableSet_singleton _))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

theorem dependentProductPMF_map {J : Type*} [Fintype J] {X Y : J → Type*}
    [∀ j, Countable (X j)] [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSingletonClass (X j)]
    [∀ j, Countable (Y j)] [∀ j, MeasurableSpace (Y j)] [∀ j, MeasurableSingletonClass (Y j)]
    (p : ∀ j, PMF (X j)) (f : ∀ j, X j → Y j) :
    (dependentProductPMF p).map (fun x j => f j (x j)) =
      dependentProductPMF (fun j => (p j).map (f j)) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  simp only [dependentProductPMF, Measure.toPMF_toMeasure]
  rw [Measure.pi_map_pi (fun j => (measurable_of_countable (f j)).aemeasurable)]
  congr 1
  funext j
  exact PMF.toMeasure_map (f j) (p j) (measurable_of_countable _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformSelectedCoefficientProductLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem selectedCoefficientJoin_injective {A J X : Type*}
    (e : A ↪ J) (x0 : X) (tail : SelectedCoefficientComplement e → X) :
    Function.Injective (selectedCoefficientJoin e x0 tail) := by
  intro b c he
  funext a
  have h := congrFun he (e a)
  simpa only [selectedCoefficientJoin_selected] using h

theorem selectedCoefficientJoin_eta {A J X : Type*}
    (e : A ↪ J) (x0 : X) (z : J → X) :
    selectedCoefficientJoin e x0 (fun k => z k.val) (fun a => z (e a)) = z := by
  funext j
  by_cases hj : j ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hj
    exact selectedCoefficientJoin_selected e x0 _ _ a
  · exact selectedCoefficientJoin_complement e x0 _ _ ⟨j, hj⟩

theorem prod_selected_complement {A J M : Type*} [Fintype A] [Fintype J]
    [CommMonoid M] (e : A ↪ J) (f : J → M) :
    (∏ j, f j) = (∏ k : SelectedCoefficientComplement e, f k.val) * ∏ a, f (e a) := by
  let : Fintype {j : J // j ∈ Set.range e} := Subtype.fintype (fun j => j ∈ Set.range e)
  have he : (∏ a, f (e a)) = ∏ k : {j : J // j ∈ Set.range e}, f k.val :=
    Fintype.prod_equiv (Equiv.ofInjective e e.injective) _ _ (fun _ => rfl)
  rw [he, mul_comm]
  convert (Fintype.prod_subtype_mul_prod_subtype (fun j => j ∈ Set.range e) f).symm

theorem independentProductPMF_selected_split {A J X : Type*}
    [Fintype A] [Fintype J] [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (e : A ↪ J) (x0 : X) (p : J → PMF X) :
    independentProductPMF p =
      (independentProductPMF (fun k : SelectedCoefficientComplement e => p k.val)).bind
        (fun tail => (independentProductPMF (fun a => p (e a))).map
          (selectedCoefficientJoin e x0 tail)) := by
  ext z
  let tail := fun k : SelectedCoefficientComplement e => z k.val
  let selected := fun a : A => z (e a)
  have hz : selectedCoefficientJoin e x0 tail selected = z :=
    selectedCoefficientJoin_eta e x0 z
  rw [← hz, PMF.bind_apply, tsum_eq_single tail]
  · rw [pmf_map_injective_at _ _ (selectedCoefficientJoin_injective e x0 tail)]
    simp only [independentProductPMF_apply]
    rw [prod_selected_complement e]
    simp only [selectedCoefficientJoin_complement, selectedCoefficientJoin_selected]
  · intro other hother
    have hr : selectedCoefficientJoin e x0 tail selected ∉
        Set.range (selectedCoefficientJoin e x0 other) := by
      rintro ⟨b, he⟩
      apply hother
      funext k
      have h := congrFun he k.val
      simpa only [selectedCoefficientJoin_complement] using h
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem independentProductPMF_uniform {J X : Type*}
    [Fintype J] [Fintype X] [Nonempty X]
    [MeasurableSpace X] [MeasurableSingletonClass X] :
    independentProductPMF (fun _ : J => PMF.uniformOfFintype X) =
      PMF.uniformOfFintype (J → X) := by
  ext x
  simp only [independentProductPMF_apply, PMF.uniformOfFintype_apply,
    Fintype.card_fun, Finset.prod_const, Finset.card_univ, Nat.cast_pow, ENNReal.inv_pow]

theorem uniformOfFintype_selected_split {A J X : Type*}
    [Fintype A] [Fintype J] [Fintype X] [Nonempty X]
    (e : A ↪ J) (x0 : X) :
    PMF.uniformOfFintype (J → X) =
      (PMF.uniformOfFintype (SelectedCoefficientComplement e → X)).bind
        (fun tail => (PMF.uniformOfFintype (A → X)).map
          (selectedCoefficientJoin e x0 tail)) := by
  let : MeasurableSpace X := ⊤
  have : MeasurableSingletonClass X := ⟨fun _ => trivial⟩
  have h := independentProductPMF_selected_split e x0 (fun _ => PMF.uniformOfFintype X)
  simp only [independentProductPMF_uniform] at h
  convert h using 1
  congr 1
  congr 1
  exact Subsingleton.elim _ _

theorem uniformZMod_selected_split {A J : Type*}
    [Fintype A] [Fintype J] (N : ℕ) [NeZero N] (e : A ↪ J) :
    PMF.uniformOfFintype (J → ZMod N) =
      (PMF.uniformOfFintype (SelectedCoefficientComplement e → ZMod N)).bind
        (fun tail => (PMF.uniformOfFintype (A → ZMod N)).map
          (selectedCoefficientJoin e (0 : ZMod N) tail)) :=
  uniformOfFintype_selected_split e 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

theorem toPMF_bind_apply {Y : Type*} (p : FiniteProbabilityWeights X)
    (q : X → PMF Y) (y : Y) :
    (p.toPMF.bind q) y = ∑ x, ENNReal.ofReal (p.weight x) * q x y := by
  rw [PMF.bind_apply, tsum_fintype]
  simp only [toPMF_apply]

theorem toPMF_bind_toReal {Y : Type*} (p : FiniteProbabilityWeights X)
    (q : X → PMF Y) (y : Y) :
    ((p.toPMF.bind q) y).toReal = p.mean (fun x => (q x y).toReal) := by
  rw [toPMF_bind_apply, ENNReal.toReal_sum (fun x _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((q x).apply_ne_top y))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (p.nonneg _), mean]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

theorem pi_uniform_weight {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, Nonempty (Ω j)]
    (x : ∀ j, Ω j) :
    (pi (fun j => uniform (Ω j))).weight x = (uniform (∀ j, Ω j)).weight x := by
  simp [pi, uniform, Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteProbabilityWeights

theorem ofSupportedPMF_map_complexMean {X Y : Type*} [Fintype Y]
    (p : PMF X) (T : Finset X) (hT : ∀ x ∉ T, (p x).toReal = 0)
    (f : X → Y) (g : Y → ℂ) :
    (ofSupportedPMF p T hT).complexMean (fun x => g (f x.val)) =
      (ofPMF (p.map f)).complexMean g := by
  apply Complex.ext
  · rw [complexMean_re, complexMean_re]
    exact ofSupportedPMF_map_mean p T hT f (fun y => (g y).re)
  · simpa [complexMean, mean, Complex.mul_im] using
      ofSupportedPMF_map_mean p T hT f (fun y => (g y).im)

end FiniteProbabilityWeights

theorem shiftedSmoothProductFiniteWeights_map_complexMean
    {I Y : Type*} [Fintype I] [Fintype Y]
    (a S : I → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (f : (I → ℤ) → Y) (g : Y → ℂ) :
    (shiftedSmoothProductFiniteWeights a S hS hZ).complexMean (fun x => g (f x.val)) =
      (FiniteProbabilityWeights.ofPMF ((shiftedSmoothProductPMF a S hS hZ).map f)).complexMean g :=
  FiniteProbabilityWeights.ofSupportedPMF_map_complexMean _ _ _ f g

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteMixedArrayRefresh
namespace OAI

section

namespace Erdos3

variable {A B J K C V S T U W : Type*}

theorem mixedArray_extend (e : A ↪ J) (d : B ↪ K)
    (xs : A → V) (xd : B → V) (fs : J → V) (fd : K → V) (fc : C → V) :
    Sum.elim (Function.extend e xs fs) (Sum.elim (Function.extend d xd fd) fc) =
      Function.extend (mixedArrayEmbedding e d) (Sum.elim xs xd)
        (Sum.elim fs (Sum.elim fd fc)) := by
  classical
  funext x
  cases x with
  | inl j =>
    by_cases hj : ∃ a, e a = j
    · obtain ⟨a, rfl⟩ := hj
      exact (e.injective.extend_apply xs fs a).trans
        ((mixedArrayEmbedding (C := C) e d).injective.extend_apply
          (Sum.elim xs xd) (Sum.elim fs (Sum.elim fd fc)) (Sum.inl a)).symm
    · have hnone : ¬ ∃ x, mixedArrayEmbedding (C := C) e d x = Sum.inl j := by
        rintro ⟨a | b, h⟩
        · exact hj ⟨a, Sum.inl.inj h⟩
        · cases h
      simp only [Sum.elim_inl, Function.extend_apply' _ _ _ hj,
        Function.extend_apply' _ _ _ hnone]
  | inr x =>
    cases x with
    | inl k =>
      by_cases hk : ∃ b, d b = k
      · obtain ⟨b, rfl⟩ := hk
        exact (d.injective.extend_apply xd fd b).trans
          ((mixedArrayEmbedding (C := C) e d).injective.extend_apply
            (Sum.elim xs xd) (Sum.elim fs (Sum.elim fd fc)) (Sum.inr b)).symm
      · have hnone : ¬ ∃ x, mixedArrayEmbedding (C := C) e d x = Sum.inr (Sum.inl k) := by
          rintro ⟨a | b, h⟩
          · cases h
          · exact hk ⟨b, Sum.inl.inj (Sum.inr.inj h)⟩
        simp only [Sum.elim_inr, Sum.elim_inl, Function.extend_apply' _ _ _ hk,
          Function.extend_apply' _ _ _ hnone]
    | inr c =>
      have hnone : ¬ ∃ x, mixedArrayEmbedding (C := C) e d x = Sum.inr (Sum.inr c) := by
        rintro ⟨a | b, h⟩ <;> cases h
      simp only [Function.extend_apply' _ _ _ hnone, Sum.elim_inr]

theorem extend_comp_equiv (p : S ≃ U) (q : T ≃ W) (actual : S ↪ T) (g : U ↪ W)
    (h : ∀ s, q (actual s) = g (p s)) (selected : U → V) (base : W → V) :
    Function.extend g selected base ∘ q =
      Function.extend actual (selected ∘ p) (base ∘ q) := by
  classical
  funext t
  by_cases ht : ∃ s, actual s = t
  · obtain ⟨s, rfl⟩ := ht
    change Function.extend g selected base (q (actual s)) = _
    rw [h, g.injective.extend_apply, actual.injective.extend_apply]
    rfl
  · have hnone : ¬ ∃ u, g u = q t := by
      rintro ⟨u, hu⟩
      apply ht
      refine ⟨p.symm u, q.injective ?_⟩
      rw [h, p.apply_symm_apply, hu]
    change Function.extend g selected base (q t) = _
    rw [Function.extend_apply' _ _ _ hnone, Function.extend_apply' _ _ _ ht]
    rfl

theorem mixedArray_extend_comp_equiv (e : A ↪ J) (d : B ↪ K)
    (p : S ≃ A ⊕ B) (q : T ≃ J ⊕ (K ⊕ C)) (actual : S ↪ T)
    (h : ∀ s, q (actual s) = mixedArrayEmbedding e d (p s))
    (xs : A → V) (xd : B → V) (fs : J → V) (fd : K → V) (fc : C → V) :
    Sum.elim (Function.extend e xs fs) (Sum.elim (Function.extend d xd fd) fc) ∘ q =
      Function.extend actual ((Sum.elim xs xd) ∘ p)
        ((Sum.elim fs (Sum.elim fd fc)) ∘ q) := by
  rw [mixedArray_extend]
  exact extend_comp_equiv p q actual (mixedArrayEmbedding e d) h _ _

theorem map_coordinate_extend (e : A ↪ J) (F : J → V → W)
    (selected : A → V) (fixed : J → V) :
    (fun j => F j (Function.extend e selected fixed j)) =
      Function.extend e (fun a => F (e a) (selected a)) (fun j => F j (fixed j)) := by
  classical
  funext j
  by_cases hj : ∃ a, e a = j
  · obtain ⟨a, rfl⟩ := hj
    rw [e.injective.extend_apply, e.injective.extend_apply]
  · rw [Function.extend_apply' _ _ _ hj, Function.extend_apply' _ _ _ hj]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteProductWeightL1
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

private theorem abs_sub_min_identity (x y : ℝ) :
    |x - y| = x + y - 2 * min x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem pi_weight_l1_le_sum {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    (p q : ∀ j, FiniteProbabilityWeights (Ω j)) :
    (∑ x, |(pi p).weight x - (pi q).weight x|) ≤
      ∑ j, ∑ x, |(p j).weight x - (q j).weight x| := by
  classical
  let h : ∀ j, Ω j → ℝ := fun j x => min ((p j).weight x) ((q j).weight x)
  let a : J → ℝ := fun j => ∑ x, h j x
  have hh (j) (x : Ω j) : 0 ≤ h j x := le_min ((p j).nonneg x) ((q j).nonneg x)
  have ha0 (j) : 0 ≤ a j := Finset.sum_nonneg (fun x _ => hh j x)
  have ha1 (j) : a j ≤ 1 := by
    calc
      a j ≤ ∑ x, (p j).weight x := Finset.sum_le_sum (fun x _ => min_le_left _ _)
      _ = 1 := (p j).total
  have hlower := one_sub_sum_le_positive_prod Finset.univ a (fun j => 1 - a j)
    (fun j _ => ha0 j) (fun j _ => ⟨sub_nonneg.mpr (ha1 j), by linarith [ha0 j]⟩)
    (fun j _ => by simp)
  have hpoint (x : ∀ j, Ω j) :
      |(pi p).weight x - (pi q).weight x| ≤
        (pi p).weight x + (pi q).weight x - 2 * ∏ j, h j (x j) := by
    rw [abs_sub_min_identity]
    have hp : (∏ j, h j (x j)) ≤ (pi p).weight x :=
      Finset.prod_le_prod (fun j _ => hh j (x j)) (fun j _ => min_le_left _ _)
    have hq : (∏ j, h j (x j)) ≤ (pi q).weight x :=
      Finset.prod_le_prod (fun j _ => hh j (x j)) (fun j _ => min_le_right _ _)
    linarith [le_min hp hq]
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  have hprod : (∑ x : ∀ j, Ω j, ∏ j, h j (x j)) = ∏ j, a j :=
    (Fintype.prod_sum h).symm
  have hcoord (j) : (∑ x, |(p j).weight x - (q j).weight x|) = 2 * (1 - a j) := by
    simp_rw [abs_sub_min_identity]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
      (p j).total, (q j).total]
    change 1 + 1 - 2 * a j = _
    ring
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    (pi p).total, (pi q).total, hprod] at hsum
  simp_rw [hcoord]
  rw [← Finset.mul_sum]
  linarith

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformResidueSmallPeriod
namespace OAI


namespace Erdos3

open scoped BigOperators Classical Matrix

theorem uniformPMF_map_fiber {G H : Type*} [Fintype G] [Nonempty G]
    [DecidableEq H] (f : G → H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card G := by
  classical
  rw [pmf_map_toReal_indicator, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

theorem uniformPMF_map_hom_image {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      if y ∈ f.range then (Nat.card f.range : ℝ)⁻¹ else 0 := by
  classical
  rw [uniformPMF_map_fiber]
  by_cases hy : y ∈ f.range
  · simp only [hy, ite_true]
    have he := AddMonoidHom.card_fiber_eq_of_mem_range f hy
      (show (0 : H) ∈ Set.range f from ⟨0, f.map_zero⟩)
    have hk : (Finset.univ.filter (fun x => f x = 0)).card = Fintype.card f.ker := by
      simp [Fintype.card_subtype, AddMonoidHom.mem_ker]
    have hc : Fintype.card f.ker * Fintype.card f.range = Fintype.card G := by
      simpa only [AddSubgroup.index_ker, Nat.card_eq_fintype_card] using f.ker.card_mul_index
    rw [he, hk, ← hc, Nat.cast_mul, Nat.card_eq_fintype_card]
    have hkn : (Fintype.card f.ker : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  · simp only [hy, ite_false]
    have hz : Finset.univ.filter (fun x => f x = y) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hy ⟨x, (Finset.mem_filter.mp hx).2⟩
    simp [hz]

theorem uniformPMF_map_hom_index {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] (f : G →+ H) (y : H) :
    ((PMF.uniformOfFintype G).map f y).toReal =
      (if y ∈ f.range then (f.range.index : ℝ) else 0) / Fintype.card H := by
  classical
  rw [uniformPMF_map_hom_image]
  by_cases hy : y ∈ f.range
  · simp only [hy, ite_true]
    have hcard : (Nat.card f.range : ℝ) * f.range.index = Fintype.card H := by
      have h := f.range.card_mul_index
      rw [Nat.card_eq_fintype_card (α := H)] at h
      exact_mod_cast h
    have hn : (Nat.card f.range : ℝ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
    have hh : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    apply (eq_div_iff hh).mpr
    rw [← hcard, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  · simp [hy]

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformHomFiberWeights
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem uniform_mean_surjective_hom_fiber {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (y : H) :
    (FiniteProbabilityWeights.uniform G).mean (fun x => if f x = y then (1 : ℝ) else 0) =
      (Fintype.card H : ℝ)⁻¹ := by
  have h := uniformPMF_map_hom_index f y
  have hr : f.range = ⊤ := by
    ext z
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_top, iff_true]
    exact hf z
  have hy : y ∈ f.range := hf y
  rw [if_pos hy, hr] at h
  simp only [AddSubgroup.index_top, Nat.cast_one, one_div] at h
  rw [uniformPMF_map_fiber] at h
  calc
    _ = ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card G := by
      rw [FiniteProbabilityWeights.uniform_mean, Fintype.expect_eq_sum_div_card]
      simp
    _ = _ := h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.UniformHomExpectation
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem uniform_mean_surjective_hom {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (g : H → ℝ) :
    (FiniteProbabilityWeights.uniform G).mean (fun x => g (f x)) =
      (FiniteProbabilityWeights.uniform H).mean g := by
  calc
    _ = ∑ y : H, (FiniteProbabilityWeights.uniform G).mean
        (fun x => if f x = y then (1 : ℝ) else 0) * g y := by
      unfold FiniteProbabilityWeights.mean
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp [mul_ite, ite_mul]
    _ = ∑ y : H, (Fintype.card H : ℝ)⁻¹ * g y := by
      simp_rw [uniform_mean_surjective_hom_fiber f hf]
    _ = _ := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RationalPolynomialForecastBoxError
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem tupleResidueReduction_surjective {A : Type*} {q N : ℕ} (hq : q ∣ N) :
    Function.Surjective (tupleResidueReduction (A := A) hq) := by
  intro y
  choose x hx using fun a => ZMod.castHom_surjective hq (y a)
  exact ⟨x, funext hx⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothBadPrimeProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem coefficientCRTEquiv_apply {L J : Type*} [Fintype L]
    (q : L → ℕ) (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (x : J → ZMod (∏ l, q l)) (l : L) (j : J) :
    coefficientCRTEquiv q hq x l j =
      ZMod.castHom (Finset.dvd_prod_of_mem q (Finset.mem_univ l)) (ZMod (q l)) (x j) :=
  ZMod.prodEquivPi_apply q hq (x j) l

theorem selectedPrimePower_coprime (S : Finset ℕ) (a : ℕ → ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    Pairwise (fun p q : S => (p.val ^ a p).Coprime (q.val ^ a q)) := by
  intro p q hpq
  exact Nat.coprime_pow_primes _ _ (hprime p p.property) (hprime q q.property)
    (fun h => hpq (Subtype.ext h))

theorem selectedPrimePower_nonzero (S : Finset ℕ) (a : ℕ → ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    (∀ p : S, p.val ^ a p ≠ 0) ∧ (∏ p : S, p.val ^ a p) ≠ 0 := by
  have hp (p : S) : p.val ^ a p ≠ 0 := pow_ne_zero _ (hprime p p.property).ne_zero
  exact ⟨hp, Finset.prod_ne_zero_iff.mpr (fun p _ => hp p)⟩

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem shiftedSmoothCoefficientPMF_residue_apply (a S : ℝ) (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum a S) (M : ℕ) [NeZero M] (r : ZMod M) :
    ((shiftedSmoothCoefficientPMF a S hS hZ).map (fun k : ℤ => (k : ZMod M)) r).toReal =
      shiftedSmoothSampleSum ((a - r.val) / M) (S / M) / shiftedSmoothSampleSum a S := by
  have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hinj : Function.Injective (fun k : ℤ => (r.val : ℤ) + M * k) := by
    intro j k h
    exact mul_left_cancel₀ hM (add_left_cancel h)
  rw [pmf_map_toReal_indicator]
  have he := hinj.tsum_eq (f := fun z : ℤ =>
      (shiftedSmoothCoefficientPMF a S hS hZ z).toReal *
        (if (z : ZMod M) = r then 1 else 0)) (by
    intro z hz
    have hz' : (z : ZMod M) = r := by
      by_contra hn
      simp only [Function.mem_support, hn, ite_false, mul_zero, ne_eq, not_true_eq_false] at hz
    obtain ⟨k, hk⟩ := (ZMod.intCast_eq_iff M z r).mp hz'
    exact ⟨k, hk.symm⟩)
  rw [← he]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
    zero_mul, add_zero, ZMod.natCast_zmod_val, ite_true, mul_one,
    shiftedSmoothCoefficientPMF_apply]
  rw [tsum_div_const]
  congr 1
  unfold shiftedSmoothSampleSum
  apply tsum_congr
  intro k
  congr 1
  field_simp
  ring

theorem shiftedSmoothSampleSum_sub_width_abs_le (a : ℝ) {S : ℝ} (hS : 1 ≤ S) :
    |shiftedSmoothSampleSum a S - S| ≤ 4 * (probabilityProfileLipschitz : ℝ) := by
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have he := shiftedSmoothSampleSum_error a hS
  have he' : |shiftedSmoothSampleSum a S - S| / S ≤
      4 * (probabilityProfileLipschitz : ℝ) / S := by
    calc
      _ = |(shiftedSmoothSampleSum a S - S) / S| := by rw [abs_div, abs_of_pos hS0]
      _ = |shiftedSmoothSampleSum a S / S - 1| := by rw [sub_div, div_self hS0.ne']
      _ ≤ _ := he
  exact (div_le_div_iff_of_pos_right hS0).mp he'

theorem shiftedSmoothCoefficientPMF_residue_error (a S : ℝ) (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum a S) (M : ℕ) [NeZero M]
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S) (r : ZMod M) :
    |((shiftedSmoothCoefficientPMF a S hS hZ).map (fun k : ℤ => (k : ZMod M)) r).toReal -
      1 / (M : ℝ)| ≤ 16 * (probabilityProfileLipschitz : ℝ) / S := by
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  have hM : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM1
  have hL1 : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
  have hL : (0 : ℝ) ≤ probabilityProfileLipschitz := NNReal.coe_nonneg _
  have hbase : 8 * (probabilityProfileLipschitz : ℝ) ≤ S := by
    have := mul_le_mul_of_nonneg_left hM1 (show 0 ≤ 8 * (probabilityProfileLipschitz : ℝ) by positivity)
    nlinarith only [this, hlarge]
  have hSM : 1 ≤ S / M := by
    apply (le_div_iff₀ hM).mpr
    nlinarith only [hlarge, mul_le_mul_of_nonneg_right hL1 hM.le]
  have hmain := shiftedSmoothSampleSum_sub_width_abs_le a (show 1 ≤ S by linarith)
  have hprog := shiftedSmoothSampleSum_sub_width_abs_le ((a - r.val) / M) hSM
  have hmainDiv : |S / M - shiftedSmoothSampleSum a S / M| ≤
      4 * (probabilityProfileLipschitz : ℝ) := by
    rw [← sub_div, abs_div, abs_of_pos hM, abs_sub_comm]
    exact (div_le_iff₀ hM).mpr (hmain.trans (by nlinarith only [mul_le_mul_of_nonneg_left hM1 (show 0 ≤ 4 * (probabilityProfileLipschitz : ℝ) by positivity)]))
  have hnum : |shiftedSmoothSampleSum ((a - r.val) / M) (S / M) -
      shiftedSmoothSampleSum a S / M| ≤ 8 * (probabilityProfileLipschitz : ℝ) := by
    have h := abs_sub_le (shiftedSmoothSampleSum ((a - r.val) / M) (S / M))
      (S / M) (shiftedSmoothSampleSum a S / M)
    linarith
  rw [shiftedSmoothCoefficientPMF_residue_apply]
  have heq : shiftedSmoothSampleSum ((a - r.val) / M) (S / M) / shiftedSmoothSampleSum a S -
      1 / (M : ℝ) =
      (shiftedSmoothSampleSum ((a - r.val) / M) (S / M) - shiftedSmoothSampleSum a S / M) /
        shiftedSmoothSampleSum a S := by field_simp
  rw [heq, abs_div, abs_of_pos hZ]
  apply (div_le_iff₀ hZ).mpr
  apply hnum.trans
  have hlo := (shiftedSmoothSampleSum_bounds a hbase).1
  calc
    _ = (16 * (probabilityProfileLipschitz : ℝ) / S) * (S / 2) := by field_simp; norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by positivity)

theorem shiftedSmoothCoefficientPMF_residue_l1 (a S : ℝ) (hS : 0 < S)
    (hZ : 0 < shiftedSmoothSampleSum a S) (M : ℕ) [NeZero M]
    (hlarge : 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S) :
    (∑ r : ZMod M,
      |((shiftedSmoothCoefficientPMF a S hS hZ).map (fun k : ℤ => (k : ZMod M)) r).toReal -
        1 / (M : ℝ)|) ≤ 16 * (probabilityProfileLipschitz : ℝ) * M / S := by
  calc
    _ ≤ ∑ _r : ZMod M, 16 * (probabilityProfileLipschitz : ℝ) / S :=
      Finset.sum_le_sum (fun r _ => shiftedSmoothCoefficientPMF_residue_error a S hS hZ M hlarge r)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]; ring

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open FiniteProbabilityWeights

theorem shiftedSmoothProductPMF_residue_weight {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) (M : ℕ) [NeZero M]
    (r : J → ZMod M) :
    (ofPMF ((shiftedSmoothProductPMF a S hS hZ).map
      (fun x j => (x j : ZMod M)))).weight r =
    (pi (fun j => smoothCoefficientResidueWeights (a j) (S j) (hS j)
      (shiftedSmoothProductMass_coordinate_pos a S hS hZ j) M)).weight r := by
  rw [ofPMF_weight, shiftedSmoothProductPMF_eq_independent]
  change ((dependentProductPMF _).map _ r).toReal = _
  rw [dependentProductPMF_map, dependentProductPMF_apply, ENNReal.toReal_prod]
  rfl

theorem shiftedSmoothProductPMF_residue_l1 {J : Type*} [Fintype J]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    (hZ : 0 < shiftedSmoothProductMass a S) (M : ℕ) [NeZero M]
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S j) :
    (∑ r, |(ofPMF ((shiftedSmoothProductPMF a S hS hZ).map
      (fun x j => (x j : ZMod M)))).weight r -
      (uniform (J → ZMod M)).weight r|) ≤
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * M / S j := by
  let hz := shiftedSmoothProductMass_coordinate_pos a S hS hZ
  have h := pi_weight_l1_le_sum
    (fun j => smoothCoefficientResidueWeights (a j) (S j) (hS j) (hz j) M)
    (fun _ : J => uniform (ZMod M))
  simp only [pi_uniform_weight] at h
  simp only [shiftedSmoothProductPMF_residue_weight]
  apply h.trans
  apply Finset.sum_le_sum
  intro j _
  simpa only [smoothCoefficientResidueWeights, ofPMF_weight, uniform, ZMod.card, one_div] using
    shiftedSmoothCoefficientPMF_residue_l1 (a j) (S j) (hS j) (hz j) M (hlarge j)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open FiniteProbabilityWeights

theorem uniform_coefficientCRT_event {L J : Type*} [Fintype L] [Fintype J]
    (q : L → ℕ) [∀ l, NeZero (q l)] [NeZero (∏ l, q l)]
    (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    (E : ∀ l, (J → ZMod (q l)) → Prop) :
    (uniform (J → ZMod (∏ l, q l))).eventProbability
        (fun y => ∀ l, E l (coefficientCRTEquiv q hq y l)) =
      ∏ l, (uniform (J → ZMod (q l))).eventProbability (E l) := by
  have h := uniform_mean_surjective_hom (coefficientCRTEquiv q hq).toAddMonoidHom
    (coefficientCRTEquiv q hq).surjective
    (fun y => @ite ℝ (∀ l, E l (y l)) (Classical.propDecidable _) 1 0)
  have hevent : (uniform (J → ZMod (∏ l, q l))).eventProbability
      (fun y => ∀ l, E l (coefficientCRTEquiv q hq y l)) =
      (uniform (∀ l, J → ZMod (q l))).eventProbability (fun y => ∀ l, E l (y l)) := by
    simp only [eventProbability, AddEquiv.coe_toAddMonoidHom] at h ⊢
    convert h using 1
    unfold mean
    apply Finset.sum_congr rfl
    intro x _
    congr 1
  rw [hevent]
  have hpi : (uniform (∀ l, J → ZMod (q l))).eventProbability (fun y => ∀ l, E l (y l)) =
      (pi (fun l => uniform (J → ZMod (q l)))).eventProbability (fun y => ∀ l, E l (y l)) := by
    unfold eventProbability mean
    apply Finset.sum_congr rfl
    intro y _
    rw [pi_uniform_weight]
  rw [hpi, eventProbability_pi]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.MixedSmoothUniformBadPrimeProduct
namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem uniform_fiberLaw_surjective_hom {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) :
    (FiniteProbabilityWeights.uniform G).fiberLaw f =
      FiniteProbabilityWeights.uniform H := by
  apply FiniteProbabilityWeights.eq_of_weight_eq
  intro y
  have hh := uniform_mean_surjective_hom_fiber f hf y
  change _ = (Fintype.card H : ℝ)⁻¹
  convert hh using 1
  unfold FiniteProbabilityWeights.fiberLaw FiniteProbabilityWeights.fiberMean
  congr 1

theorem uniform_complexMean_surjective_hom {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [Fintype G] [Fintype H]
    (f : G →+ H) (hf : Function.Surjective f) (g : H → ℂ) :
    (FiniteProbabilityWeights.uniform G).complexMean (fun x => g (f x)) =
      (FiniteProbabilityWeights.uniform H).complexMean g := by
  rw [← FiniteProbabilityWeights.fiberLaw_complexMean,
    uniform_fiberLaw_surjective_hom f hf]

theorem uniform_tupleResidueReduction_complexMean {D : Type*}
    [Fintype D] [DecidableEq D] {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (g : (D → ZMod M) → ℂ) :
    (FiniteProbabilityWeights.uniform (D → ZMod N)).complexMean
      (fun x => g (tupleResidueReduction hMN x)) =
      (FiniteProbabilityWeights.uniform (D → ZMod M)).complexMean g :=
  uniform_complexMean_surjective_hom (tupleResidueReduction hMN)
    (tupleResidueReduction_surjective hMN) g

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open FiniteProbabilityWeights

theorem finiteWeights_prod_same_l1 {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : FiniteProbabilityWeights X) (u : FiniteProbabilityWeights Y) :
    (∑ z : X × Y, |(p.prod u).weight z - (q.prod u).weight z|) =
      ∑ x : X, |p.weight x - q.weight x| := by
  simp only [FiniteProbabilityWeights.prod, ← sub_mul, abs_mul,
    abs_of_nonneg (u.nonneg _), Fintype.sum_prod_type, ← Finset.mul_sum,
    u.total, mul_one]

private theorem uniform_pair_sum_complexMean {J D : Type*} [Fintype J] [Fintype D]
    (M : ℕ) [NeZero M] (f : ((J ⊕ D) → ZMod M) → ℂ) :
    ((uniform (J → ZMod M)).prod (uniform (D → ZMod M))).complexMean
      (fun p => f (Sum.elim p.1 p.2)) =
      (uniform ((J ⊕ D) → ZMod M)).complexMean f := by
  rw [complexMean_prod]
  simp_rw [uniform_complexMean]
  have hprod := Finset.expect_product' (Finset.univ : Finset (J → ZMod M))
    (Finset.univ : Finset (D → ZMod M)) (fun x y => f (Sum.elim x y))
  rw [Finset.univ_product_univ] at hprod
  rw [← hprod]
  exact Fintype.expect_equiv (mixedResidueArrayEquiv J D (ZMod M)) _ _ (fun _ => rfl)

theorem mixedSmoothUniform_residue_complexMean_eq {J D : Type*} [Fintype J] [Fintype D]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) (hZ : 0 < shiftedSmoothProductMass a S)
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (f : ((J ⊕ D) → ZMod M) → ℂ) :
    ((shiftedSmoothProductFiniteWeights a S hS hZ).prod (uniform (D → ZMod N))).complexMean
      (fun z => f (Sum.elim (fun j => (z.1.val j : ZMod M))
        (fun d => ZMod.castHom hMN (ZMod M) (z.2 d)))) =
    ((ofPMF ((shiftedSmoothProductPMF a S hS hZ).map
      (fun x j => (x j : ZMod M)))).prod (uniform (D → ZMod M))).complexMean
      (fun z => f (Sum.elim z.1 z.2)) := by
  rw [complexMean_prod, complexMean_prod]
  have hred (x : J → ZMod M) :
      (uniform (D → ZMod N)).complexMean (fun y => f (Sum.elim x
        (fun d => ZMod.castHom hMN (ZMod M) (y d)))) =
      (uniform (D → ZMod M)).complexMean (fun y => f (Sum.elim x y)) :=
    uniform_tupleResidueReduction_complexMean hMN (fun y => f (Sum.elim x y))
  simp_rw [hred]
  exact shiftedSmoothProductFiniteWeights_map_complexMean a S hS hZ
    (fun x j => (x j : ZMod M)) (fun x => (uniform (D → ZMod M)).complexMean
      (fun y => f (Sum.elim x y)))

theorem mixedSmoothUniform_residue_l1 {J D : Type*} [Fintype J] [Fintype D]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) (hZ : 0 < shiftedSmoothProductMass a S)
    (M : ℕ) [NeZero M]
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S j) :
    (∑ z : (J → ZMod M) × (D → ZMod M),
      |((ofPMF ((shiftedSmoothProductPMF a S hS hZ).map
          (fun x j => (x j : ZMod M)))).prod (uniform (D → ZMod M))).weight z -
        ((uniform (J → ZMod M)).prod (uniform (D → ZMod M))).weight z|) ≤
      ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * M / S j := by
  rw [finiteWeights_prod_same_l1]
  exact shiftedSmoothProductPMF_residue_l1 a S hS hZ M hlarge

theorem mixedSmoothUniform_residue_complexMean_error {J D : Type*} [Fintype J] [Fintype D]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) (hZ : 0 < shiftedSmoothProductMass a S)
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S j)
    (f : ((J ⊕ D) → ZMod M) → ℂ) (hf : ∀ r, ‖f r‖ ≤ 1) :
    ‖((shiftedSmoothProductFiniteWeights a S hS hZ).prod (uniform (D → ZMod N))).complexMean
      (fun z => f (Sum.elim (fun j => (z.1.val j : ZMod M))
        (fun d => ZMod.castHom hMN (ZMod M) (z.2 d)))) -
      (uniform ((J ⊕ D) → ZMod M)).complexMean f‖ ≤
      ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * M / S j := by
  rw [mixedSmoothUniform_residue_complexMean_eq a S hS hZ hMN,
    ← uniform_pair_sum_complexMean M f]
  let p : FiniteProbabilityWeights (J → ZMod M) :=
    ofPMF ((shiftedSmoothProductPMF a S hS hZ).map (fun x j => (x j : ZMod M)))
  let q : FiniteProbabilityWeights (J → ZMod M) := uniform (J → ZMod M)
  let u : FiniteProbabilityWeights (D → ZMod M) := uniform (D → ZMod M)
  let g : (J → ZMod M) × (D → ZMod M) → ℂ := fun z => f (Sum.elim z.1 z.2)
  have hg : ∀ z, ‖g z‖ ≤ 1 := fun z => hf (Sum.elim z.1 z.2)
  have htest := norm_complexMean_sub_le_weight_l1 (p.prod u) (q.prod u) g hg
  have hweight : (∑ z, |(p.prod u).weight z - (q.prod u).weight z|) ≤
      ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * M / S j :=
    mixedSmoothUniform_residue_l1 (D := D) a S hS hZ M hlarge
  exact htest.trans hweight

private theorem complexMean_indicator_eq_event {T : Type*} [Fintype T]
    (p : FiniteProbabilityWeights T) (E : T → Prop) :
    p.complexMean (fun x => if E x then (1 : ℂ) else 0) = (p.eventProbability E : ℂ) := by
  simp only [complexMean, eventProbability, mean, Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

theorem mixedSmoothUniform_residue_event_error {J D : Type*} [Fintype J] [Fintype D]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) (hZ : 0 < shiftedSmoothProductMass a S)
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * M ≤ S j)
    (E : ((J ⊕ D) → ZMod M) → Prop) :
    |((shiftedSmoothProductFiniteWeights a S hS hZ).prod (uniform (D → ZMod N))).eventProbability
      (fun z => E (Sum.elim (fun j => (z.1.val j : ZMod M))
        (fun d => ZMod.castHom hMN (ZMod M) (z.2 d)))) -
      (uniform ((J ⊕ D) → ZMod M)).eventProbability E| ≤
      ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * M / S j := by
  have h := mixedSmoothUniform_residue_complexMean_error a S hS hZ hMN hlarge
    (fun r => if E r then (1 : ℂ) else 0) (fun r => by split_ifs <;> norm_num)
  rw [complexMean_indicator_eq_event, complexMean_indicator_eq_event,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open FiniteProbabilityWeights

theorem selectedPrimePower_product_dvd (S : Finset ℕ) (a : ℕ → ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) {N : ℕ}
    (hcover : ∀ p ∈ S, p ^ a p ∣ N) :
    (∏ p : S, p.val ^ a p) ∣ N := by
  apply Fintype.prod_dvd_of_isRelPrime
  · intro p q hpq
    exact Nat.coprime_iff_isRelPrime.mp (selectedPrimePower_coprime S a hprime hpq)
  · intro p
    exact hcover p p.property

theorem coefficientCRTEquiv_mixed_reduction {L J D : Type*} [Fintype L]
    (q : L → ℕ) (hq : Pairwise (fun l k => (q l).Coprime (q k)))
    {N : ℕ} (hMN : (∏ l, q l) ∣ N) (x : J → ℤ) (r : D → ZMod N) :
    coefficientCRTEquiv q hq
      (Sum.elim (fun j => (x j : ZMod (∏ l, q l)))
        (fun d => ZMod.castHom hMN (ZMod (∏ l, q l)) (r d))) =
      (fun l => Sum.elim (fun j => (x j : ZMod (q l)))
        (fun d => ZMod.cast (r d))) := by
  funext l k
  cases k with
  | inl j =>
    rw [coefficientCRTEquiv_apply]
    exact map_intCast _ _
  | inr d =>
    rw [coefficientCRTEquiv_apply]
    change ZMod.castHom _ (ZMod (q l))
      (ZMod.castHom hMN (ZMod (∏ l, q l)) (r d)) = ZMod.cast (r d)
    rw [← RingHom.comp_apply, ZMod.castHom_comp, ZMod.castHom_apply]

private theorem uniform_event_fintype_congr {X : Type*} [Nonempty X]
    (i₁ i₂ : Fintype X) (E : X → Prop) :
    @eventProbability X i₁ (@uniform X i₁ inferInstance) E =
      @eventProbability X i₂ (@uniform X i₂ inferInstance) E := by
  cases Subsingleton.elim i₁ i₂
  rfl

theorem mixedSmoothUniform_primePower_event
    {J D : Type*} [Fintype J] [Fintype D] {N : ℕ} [NeZero N]
    (center width : J → ℝ) (hwidth : ∀ j, 0 < width j)
    (hZ : 0 < shiftedSmoothProductMass center width)
    (S : Finset ℕ) (a : ℕ → ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hcover : ∀ p ∈ S, p ^ a p ∣ N)
    [∀ p : S, NeZero (p.val ^ a p)]
    (E : ∀ p : S, ((J ⊕ D) → ZMod (p.val ^ a p)) → Prop)
    (hprob : ∀ p : S,
      (uniform ((J ⊕ D) → ZMod (p.val ^ a p))).eventProbability (E p) ≤
        1 / ((p.val ^ a p : ℕ) : ℝ) ^ 10)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) * (∏ p : S, p.val ^ a p) ≤ width j) :
    ((shiftedSmoothProductFiniteWeights center width hwidth hZ).prod
      (uniform (D → ZMod N))).eventProbability
        (fun x => ∀ p : S, E p (Sum.elim
          (fun j => (x.1.val j : ZMod (p.val ^ a p)))
          (fun d => ZMod.cast (x.2 d)))) ≤
      1 / ((∏ p : S, p.val ^ a p : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (∏ p : S, p.val ^ a p) / width j := by
  let : NeZero (∏ p : S, p.val ^ a p) := ⟨(selectedPrimePower_nonzero S a hprime).2⟩
  let q : S → ℕ := fun p => p.val ^ a p
  let hq := selectedPrimePower_coprime S a hprime
  have hMN : (∏ p : S, q p) ∣ N := selectedPrimePower_product_dvd S a hprime hcover
  let F : ((J ⊕ D) → ZMod (∏ p : S, q p)) → Prop :=
    fun y => ∀ p : S, E p (coefficientCRTEquiv q hq y p)
  have htransfer := mixedSmoothUniform_residue_event_error center width hwidth hZ hMN hlarge F
  have hF (x : rectangularWeightIndices center width 1 × (D → ZMod N)) :
      F (Sum.elim (fun j => (x.1.val j : ZMod (∏ p : S, q p)))
        (fun d => ZMod.castHom hMN (ZMod (∏ p : S, q p)) (x.2 d))) =
      (∀ p : S, E p (Sum.elim (fun j => (x.1.val j : ZMod (p.val ^ a p)))
        (fun d => ZMod.cast (x.2 d)))) := by
    unfold F
    rw [coefficientCRTEquiv_mixed_reduction]
  simp only [hF] at htransfer
  have huniform : (uniform ((J ⊕ D) → ZMod (∏ p : S, q p))).eventProbability F ≤
      1 / ((∏ p : S, p.val ^ a p : ℕ) : ℝ) ^ 10 := by
    have hu : (uniform ((J ⊕ D) → ZMod (∏ p : S, q p))).eventProbability F =
        ∏ p : S, (uniform ((J ⊕ D) → ZMod (q p))).eventProbability (E p) := by
      convert uniform_coefficientCRT_event q hq E using 1
      · exact uniform_event_fintype_congr _ _ _
      · apply Finset.prod_congr rfl
        intro p _
        exact uniform_event_fintype_congr _ _ _
    rw [hu]
    calc
      _ ≤ ∏ p : S, 1 / ((p.val ^ a p : ℕ) : ℝ) ^ 10 :=
        Finset.prod_le_prod (fun p _ => (uniform _).eventProbability_nonneg (E p))
          (fun p _ => hprob p)
      _ = _ := by
        simp only [one_div, ← Finset.prod_inv_distrib, ← Finset.prod_pow, Nat.cast_prod]
  have hupper := (abs_le.mp htransfer).2
  dsimp only [q] at hupper huniform
  linarith only [hupper, huniform]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

theorem allocatedRankComponentCoefficientEmbedding_selected
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (j : Fin m) (o : AllocatedCongruenceRankOutput X E inactive j) (l : Fin L) :
    allocatedRankComponentCoefficientEmbedding inactive
      ⟨⟨j, o⟩, allocatedRankComponentSelectedEmbedding inactive spatial kernel block j o l⟩ =
      allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block ⟨j, o, l⟩ := by
  rcases o with x | i | a <;> rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}

attribute [local instance] OAI.Erdos3.VectorPolynomial.congruenceIndexFintype
attribute [local instance] OAI.Erdos3.VectorPolynomial.congruenceIndexDecidableEq
theorem allocatedMixedCoefficientEquiv_cast (inactive : LayerSamplerAxis I n → Prop)
    {L N : ℕ} [NeZero N] (M : ℕ)
    (x : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N) :
    allocatedMixedCoefficientEquiv inactive L (ZMod M)
      (Sum.elim (fun j => (x j : ZMod M)) (fun j => ZMod.cast (deck j))) =
        fun j => (allocatedMixedSelectedValues inactive x deck j : ZMod M) := by
  funext j
  rcases j with ⟨j,(z | e | i),l⟩
  · rfl
  · exact (ZMod.cast_eq_val _).trans (Int.cast_natCast _).symm
  · rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankFullProductLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

theorem allocatedFullCoefficientSplit_selected
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩)
    (s : AllocatedCongruenceCoefficientIndex X E inactive L) :
    allocatedFullCoefficientSplit (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block s) =
      mixedArrayEmbedding (allocatedSmoothFullEmbedding inactive spatial block)
        (allocatedDeckFullEmbedding kernel) (allocatedCongruenceCoefficientSplit inactive L s) := by
  rcases s with ⟨j,(x | e | i),l⟩ <;> rfl

theorem allocatedMixedFullArray_refresh {R : Type*}
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩)
    (selectedSmooth : AllocatedSmoothRankCoefficientIndex X inactive L → R)
    (selectedDeck : AllocatedDeckRankCoefficientIndex E L → R)
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → R)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → R)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → R) :
    allocatedMixedFullArray
      (Function.extend (allocatedSmoothFullEmbedding inactive spatial block) selectedSmooth smooth)
      (Function.extend (allocatedDeckFullEmbedding kernel) selectedDeck deck) continuous =
      Function.extend (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block)
        (Sum.elim selectedSmooth selectedDeck ∘ allocatedCongruenceCoefficientSplit inactive L)
        (allocatedMixedFullArray smooth deck continuous) :=
  mixedArray_extend_comp_equiv (allocatedSmoothFullEmbedding inactive spatial block)
    (allocatedDeckFullEmbedding kernel) (allocatedCongruenceCoefficientSplit inactive L)
    allocatedFullCoefficientSplit (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block)
    (allocatedFullCoefficientSplit_selected inactive spatial kernel block)
    selectedSmooth selectedDeck smooth deck continuous

theorem allocatedMixedFullArray_refresh_selected {N : ℕ}
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩)
    (selectedSmooth : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (selectedDeck : AllocatedDeckRankCoefficientIndex E L → ZMod N)
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → ℤ)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → ℤ) :
    allocatedMixedFullArray
      (Function.extend (allocatedSmoothFullEmbedding inactive spatial block) selectedSmooth smooth)
      (fun k => ((Function.extend (allocatedDeckFullEmbedding kernel) selectedDeck deck k).val : ℤ)) continuous =
      Function.extend (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block)
        (allocatedMixedSelectedValues inactive selectedSmooth selectedDeck)
        (allocatedMixedFullArray smooth (fun k => (deck k).val) continuous) := by
  have hdeck : (fun k => ((Function.extend (allocatedDeckFullEmbedding kernel) selectedDeck deck k).val : ℤ)) =
      Function.extend (allocatedDeckFullEmbedding kernel) (fun k => ((selectedDeck k).val : ℤ)) (fun k => ((deck k).val : ℤ)) := by
    funext k
    exact Function.apply_extend (fun z : ZMod N => (z.val : ℤ)) _ _ _
  rw [hdeck]
  exact allocatedMixedFullArray_refresh inactive spatial kernel block selectedSmooth
    (fun k => (selectedDeck k).val) smooth (fun k => (deck k).val) continuous

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineProbability
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {L : ℕ} {R : Type*}

theorem allocatedCongruenceAffineCoefficients_intCast
    (inactive : LayerSamplerAxis I n → Prop) (stride : X → ℤ)
    (offset c : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ) (N : ℕ) :
    (fun j => ((allocatedCongruenceAffineCoefficients (R := ℤ) inactive stride offset c j : ℤ) : ZMod N)) =
      allocatedCongruenceAffineCoefficients inactive (fun x => (stride x : ZMod N))
        (fun j => (offset j : ZMod N)) (fun j => (c j : ZMod N)) := by
  funext j
  rcases j with ⟨j,(x | o),l⟩
  · simp only [allocatedCongruenceAffineCoefficients, Int.cast_add, Int.cast_mul]
  · rfl

theorem allocatedMixedAffineSelectedValues_cast
    (inactive : LayerSamplerAxis I n → Prop) (stride : X → ℤ)
    (offset : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    {N : ℕ} [NeZero N] (M : ℕ)
    (x : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N) :
    allocatedCongruenceAffineCoefficients inactive (fun x => (stride x : ZMod M))
      (fun j => (offset j : ZMod M))
      (allocatedMixedCoefficientEquiv inactive L (ZMod M)
        (Sum.elim (fun j => (x j : ZMod M)) (fun j => ZMod.cast (deck j)))) =
      (fun j => (allocatedMixedAffineSelectedValues inactive stride offset x deck j : ZMod M)) := by
  rw [allocatedMixedCoefficientEquiv_cast]
  exact (allocatedCongruenceAffineCoefficients_intCast inactive stride offset _ M).symm

theorem allocatedMixedAffineSelectedValues_natCast
    (inactive : LayerSamplerAxis I n → Prop) (stride : X → ℕ)
    (offset : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    {N : ℕ} [NeZero N] (M : ℕ)
    (x : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N) :
    allocatedCongruenceAffineCoefficients inactive (fun x => (stride x : ZMod M))
      (fun j => (offset j : ZMod M))
      (allocatedMixedCoefficientEquiv inactive L (ZMod M)
        (Sum.elim (fun j => (x j : ZMod M)) (fun j => ZMod.cast (deck j)))) =
      (fun j => (allocatedMixedAffineSelectedValues inactive (fun x => (stride x : ℤ))
        offset x deck j : ZMod M)) := by
  simpa only [Int.cast_natCast] using
    allocatedMixedAffineSelectedValues_cast inactive (fun x => (stride x : ℤ)) offset M x deck

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ} {R : Type*}

theorem allocatedFullSmoothAffine_extend [Semiring R]
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩)
    (stride : X → R) (residue : Option (LayerSamplerVariables G I n B) × X → R)
    (selected : AllocatedSmoothRankCoefficientIndex X inactive L → R)
    (fixed : AllocatedFullSmoothCoefficientIndex G X I n B → R) :
    allocatedFullSmoothAffine stride residue
      (Function.extend (allocatedSmoothFullEmbedding inactive spatial block) selected fixed) =
      Function.extend (allocatedSmoothFullEmbedding inactive spatial block)
        (allocatedSelectedSmoothAffine inactive spatial stride residue selected)
        (allocatedFullSmoothAffine stride residue fixed) := by
  let F : AllocatedFullSmoothCoefficientIndex G X I n B → R → R :=
    fun t v => match t with
    | .inl t => residue t + stride t.2 * v
    | .inr _ => v
  have hs : (fun a => F (allocatedSmoothFullEmbedding inactive spatial block a) (selected a)) =
      allocatedSelectedSmoothAffine inactive spatial stride residue selected := by
    funext a
    rcases a with ⟨j,(x | i),l⟩ <;> rfl
  have h := map_coordinate_extend (allocatedSmoothFullEmbedding inactive spatial block) F selected fixed
  have hf (z : AllocatedFullSmoothCoefficientIndex G X I n B → R) :
      (fun t => F t (z t)) = allocatedFullSmoothAffine stride residue z := by
    funext t
    rcases t with t | t <;> rfl
  rw [hs, hf, hf] at h
  exact h

theorem allocatedMixedSelectedValues_affine {N : ℕ}
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (stride : X → ℤ) (residue : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (selected : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N) :
    allocatedMixedSelectedValues inactive
      (allocatedSelectedSmoothAffine inactive spatial stride residue selected) deck =
      allocatedMixedAffineSelectedValues inactive stride
        (allocatedSelectedNoiseOffset inactive spatial residue) selected deck := by
  funext a
  rcases a with ⟨j,(x | e | i),l⟩ <;> rfl

theorem allocatedMixedFullArray_affine_refresh_selected {N : ℕ}
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩)
    (stride : X → ℤ) (residue : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (selectedSmooth : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (selectedDeck : AllocatedDeckRankCoefficientIndex E L → ZMod N)
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → ℤ)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → ℤ) :
    allocatedMixedFullArray
      (allocatedFullSmoothAffine stride residue
        (Function.extend (allocatedSmoothFullEmbedding inactive spatial block) selectedSmooth smooth))
      (fun k => ((Function.extend (allocatedDeckFullEmbedding kernel) selectedDeck deck k).val : ℤ)) continuous =
      Function.extend (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block)
        (allocatedMixedAffineSelectedValues inactive stride
          (allocatedSelectedNoiseOffset inactive spatial residue) selectedSmooth selectedDeck)
        (allocatedMixedFullArray (allocatedFullSmoothAffine stride residue smooth)
          (fun k => (deck k).val) continuous) := by
  rw [allocatedFullSmoothAffine_extend, allocatedMixedFullArray_refresh_selected,
    allocatedMixedSelectedValues_affine]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankActualRefreshBad
namespace OAI

section

namespace Erdos3

theorem extend_restrict_disjoint_fiber {T A S K R : Type*} {U : T → Type*}
    (full : (Σ t, U t) ↪ K) (slot : ∀ t, A ↪ U t)
    (selected : S ↪ K) (reindex : T × A ≃ S)
    (hselected : ∀ t a, selected (reindex (t,a)) = full ⟨t, slot t a⟩)
    (f : K → R) (c : S → R) (t : T) (u : U t) :
    Function.extend selected c f (full ⟨t,u⟩) =
      Function.extend (slot t) (fun a => c (reindex (t,a)))
        (fun z => f (full ⟨t,z⟩)) u := by
  classical
  by_cases hu : ∃ a, slot t a = u
  · obtain ⟨a,rfl⟩ := hu
    rw [← hselected t a, selected.injective.extend_apply,
      (slot t).injective.extend_apply]
  · rw [Function.extend_apply' _ _ _ hu]
    apply Function.extend_apply'
    rintro ⟨z,hz⟩
    obtain ⟨⟨s,a⟩,rfl⟩ := reindex.surjective z
    rw [hselected] at hz
    have htu := full.injective hz
    have hst : s = t := congrArg Sigma.fst htu
    subst s
    have hlocal : slot t a = u := eq_of_heq (Sigma.mk.inj htu).2
    exact hu ⟨a,hlocal⟩

theorem map_extend_selected {A K R S : Type*} (slot : A ↪ K)
    (map : R → S) (fixed : K → R) (fresh : A → R) (k : K) :
    map (Function.extend slot fresh fixed k) =
      Function.extend slot (fun a => map (fresh a)) (fun z => map (fixed z)) k := by
  classical
  by_cases hk : ∃ a, slot a = k
  · obtain ⟨a,rfl⟩ := hk
    rw [slot.injective.extend_apply, slot.injective.extend_apply]
  · rw [Function.extend_apply' _ _ _ hk, Function.extend_apply' _ _ _ hk]

end Erdos3

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

theorem allocatedActualRefresh_component {R : Type*}
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (f : AllocatedActualCoefficientIndex G X I E n B → R)
    (c : AllocatedCongruenceCoefficientIndex X E inactive L → R)
    (j : Fin m) (o : AllocatedCongruenceRankOutput X E inactive j)
    (q : AllocatedRankComponentCoefficient (G := G) (B := B) inactive j o) :
    Function.extend (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block)
      c f (allocatedRankComponentCoefficientEmbedding inactive ⟨⟨j,o⟩,q⟩) =
      Function.extend (allocatedRankComponentSelectedEmbedding inactive spatial kernel block j o)
        (fun l => c ⟨j,o,l⟩)
        (fun z => f (allocatedRankComponentCoefficientEmbedding inactive ⟨⟨j,o⟩,z⟩)) q := by
  exact extend_restrict_disjoint_fiber
    (allocatedRankComponentCoefficientEmbedding inactive)
    (fun t => allocatedRankComponentSelectedEmbedding inactive spatial kernel block t.1 t.2)
    (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block)
    (allocatedCongruenceCoefficientReindex inactive L)
    (fun t l => (allocatedRankComponentCoefficientEmbedding_selected
      inactive spatial kernel block t.1 t.2 l).symm) f c ⟨j,o⟩ q

theorem allocatedActualRefresh_component_reduce
    (N : ℕ) (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (c : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    (j : Fin m) (o : AllocatedCongruenceRankOutput X E inactive j)
    (q : AllocatedRankComponentCoefficient (G := G) (B := B) inactive j o) :
    ((Function.extend (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block)
      c f (allocatedRankComponentCoefficientEmbedding inactive ⟨⟨j,o⟩,q⟩) : ℤ) : ZMod N) =
      Function.extend (allocatedRankComponentSelectedEmbedding inactive spatial kernel block j o)
        (fun l => (c ⟨j,o,l⟩ : ZMod N))
        (fun z => (f (allocatedRankComponentCoefficientEmbedding inactive ⟨⟨j,o⟩,z⟩) : ZMod N)) q := by
  rw [allocatedActualRefresh_component]
  exact map_extend_selected
    (allocatedRankComponentSelectedEmbedding inactive spatial kernel block j o)
    (fun z : ℤ => (z : ZMod N)) _ _ q

variable [Fintype G] [∀ j, Fintype (I j)] [∀ a, Fintype (B a)]

theorem allocatedActualRefresh_original_congruence
    (N : ℕ) (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (c : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    (j : Fin m) (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    let refreshed := fun z => ((Function.extend
      (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block) c f z : ℤ) : ZMod N)
    let fixed := fun z => (f z : ZMod N)
    allocatedOriginalTaggedTop inactive j (allocatedReadNoise refreshed) (allocatedReadDeck refreshed)
      (fun a => allocatedReadProjection refreshed ⟨j,a.val⟩) v
      (allocatedCongruenceOutputEmbedding inactive j o) =
      allocatedCongruenceRankPolynomial inactive j (allocatedReadNoise fixed) (allocatedReadDeck fixed)
        (fun a => allocatedReadProjection fixed ⟨j,a.val⟩) spatial (kernel j) (block j)
        (fun z l => (c ⟨j,z,l⟩ : ZMod N)) v o := by
  dsimp only
  let fresh : AllocatedCongruenceRankOutput X E inactive j → Fin L → ZMod N :=
    fun z l => (c ⟨j,z,l⟩ : ZMod N)
  have hext (z : AllocatedCongruenceRankOutput X E inactive j) :
      Function.extend (allocatedCongruenceOutputEmbedding inactive j) fresh (fun _ _ => 0)
        (allocatedCongruenceOutputEmbedding inactive j z) = fresh z :=
    (allocatedCongruenceOutputEmbedding inactive j).injective.extend_apply _ _ z
  rcases o with x | i | a
  · have hx : Function.extend (allocatedCongruenceOutputEmbedding inactive j) fresh
        (fun _ _ => 0) (.inl x) = fresh (.inl x) := hext (.inl x)
    have hc := funext (allocatedActualRefresh_component_reduce N inactive spatial kernel block
      f c j (.inl x))
    change homogeneousComponent 1 (conditionPolynomial (allocatedLongEmbedding inactive)
      (allocatedLongEmbedding inactive).injective v (spatialRankPolynomial _)) = _
    unfold allocatedCongruenceRankPolynomial
    change _ = homogeneousComponent 1 (conditionPolynomial (allocatedLongEmbedding inactive)
      (allocatedLongEmbedding inactive).injective v (spatialRankPolynomial
        (Function.extend (spatialKernelRankSlot spatial)
          (Function.extend (allocatedCongruenceOutputEmbedding inactive j) fresh (fun _ _ => 0)
            (.inl x)) _)))
    rw [hx]
    exact congrArg (fun coefficients => homogeneousComponent 1
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v (spatialRankPolynomial coefficients))) hc
  · have hi : Function.extend (allocatedCongruenceOutputEmbedding inactive j) fresh
        (fun _ _ => 0) (.inr (.inl i)) = fresh (.inr (.inl i)) := hext (.inr (.inl i))
    have hc := funext (allocatedActualRefresh_component_reduce N inactive spatial kernel block
      f c j (.inr (.inl i)))
    unfold allocatedCongruenceRankPolynomial
    simp only [allocatedCongruenceOutputEmbedding_deck, allocatedTaggedRankPolynomial,
      allocatedDegreeRankPolynomial, allocatedOriginalTaggedTop, modularDeckPolynomial,
      resampleCoefficientDeckCoordinate_apply]
    change _ = homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive) (allocatedLongEmbedding inactive).injective v
        (modularBoundedCoefficientPolynomial (j.val + 1)
          (Function.extend (kernelRankCoefficientSlot (layerSamplerDegree I n) (kernel j))
            (Function.extend (allocatedCongruenceOutputEmbedding inactive j) fresh (fun _ _ => 0)
              (.inr (.inl i))) _)))
    rw [hi]
    exact congrArg (fun coefficients => homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (modularBoundedCoefficientPolynomial (j.val + 1) coefficients))) hc
  · have ha : Function.extend (allocatedCongruenceOutputEmbedding inactive j) fresh
        (fun _ _ => 0) (.inr (.inr (allocatedCongruenceIntegerEmbedding inactive j a))) =
          fresh (.inr (.inr a)) := hext (.inr (.inr a))
    have hc := funext (allocatedActualRefresh_component_reduce N inactive spatial kernel block
      f c j (.inr (.inr a)))
    unfold allocatedCongruenceRankPolynomial
    simp only [allocatedCongruenceOutputEmbedding_integer, allocatedTaggedRankPolynomial,
      allocatedDegreeRankPolynomial, allocatedOriginalTaggedTop]
    change _ = homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive) (allocatedLongEmbedding inactive).injective v
        (modularBoundedCoefficientPolynomial (j.val + 1)
          (Function.extend (canonicalPrincipalSubblockSlot (layerSamplerDegree I n)
            ⟨j,.inr a.val⟩ (block j (allocatedCongruenceIntegerEmbedding inactive j a)))
            (Function.extend (allocatedCongruenceOutputEmbedding inactive j) fresh (fun _ _ => 0)
              (.inr (.inr (allocatedCongruenceIntegerEmbedding inactive j a)))) _)))
    rw [ha]
    exact congrArg (fun coefficients => homogeneousComponent (j.val + 1)
      (conditionPolynomial (allocatedLongEmbedding inactive)
        (allocatedLongEmbedding inactive).injective v
        (modularBoundedCoefficientPolynomial (j.val + 1) coefficients))) hc

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open _root_.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

variable (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j, a.val⟩)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (c : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)

local notation "refreshed" => Function.extend
  (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block) c f
local notation "selected" => allocatedCongruenceIntegerSelectedCoefficients inactive
  (allocatedReadNoise refreshed) (allocatedReadDeck refreshed)
  (fun j a => allocatedReadProjection refreshed (Sigma.mk j (Subtype.val a))) spatial kernel block

omit [Fintype X] [∀ j, Fintype (E j)] in

theorem allocatedActualRefresh_rank_polynomial
    (N : ℕ) (j : Fin m) (v : LayerSamplerVariables G I n B → ZMod N)
    (o : AllocatedCongruenceRankOutput X E inactive j) :
    allocatedCongruenceRankPolynomial inactive j
      (fun q => ((allocatedReadNoise refreshed q : ℤ) : ZMod N))
      (fun j q i => ((allocatedReadDeck refreshed j q i : ℤ) : ZMod N))
      (fun a q => ((allocatedReadProjection refreshed ⟨j,a.val⟩ q : ℤ) : ZMod N))
      spatial (kernel j) (block j) (fun z l => (selected ⟨j,z,l⟩ : ZMod N)) v o =
    allocatedCongruenceRankPolynomial inactive j
      (fun q => ((allocatedReadNoise f q : ℤ) : ZMod N))
      (fun j q i => ((allocatedReadDeck f j q i : ℤ) : ZMod N))
      (fun a q => ((allocatedReadProjection f ⟨j,a.val⟩ q : ℤ) : ZMod N))
      spatial (kernel j) (block j) (fun z l => (c ⟨j,z,l⟩ : ZMod N)) v o := by
  simp only [allocatedCongruenceIntegerSelectedCoefficients_reduce,
    allocatedCongruenceRankPolynomial_original]
  exact allocatedActualRefresh_original_congruence N inactive spatial kernel block f c j v o

theorem allocatedActualRefresh_rank_probability
    (N : ℕ) [NeZero N] (j : Fin m) (v : LayerSamplerVariables G I n B → ZMod N)
    (w : AllocatedCongruenceRankOutput X E inactive j → ZMod N) :
    allocatedCongruenceRankFailureProbability inactive j
      (fun q => ((allocatedReadNoise refreshed q : ℤ) : ZMod N))
      (fun j q i => ((allocatedReadDeck refreshed j q i : ℤ) : ZMod N))
      (fun a q => ((allocatedReadProjection refreshed ⟨j,a.val⟩ q : ℤ) : ZMod N))
      spatial (kernel j) (block j) (fun z l => (selected ⟨j,z,l⟩ : ZMod N)) v w =
    allocatedCongruenceRankFailureProbability inactive j
      (fun q => ((allocatedReadNoise f q : ℤ) : ZMod N))
      (fun j q i => ((allocatedReadDeck f j q i : ℤ) : ZMod N))
      (fun a q => ((allocatedReadProjection f ⟨j,a.val⟩ q : ℤ) : ZMod N))
      spatial (kernel j) (block j) (fun z l => (c ⟨j,z,l⟩ : ZMod N)) v w := by
  unfold allocatedCongruenceRankFailureProbability
  simp only [allocatedActualRefresh_rank_polynomial]

theorem allocatedActualRefresh_modulusBad
    (C : ℝ) (N : ℕ) [NeZero N] :
    allocatedCongruenceModulusBad inactive
      (allocatedReadNoise refreshed) (allocatedReadDeck refreshed)
      (fun j a => allocatedReadProjection refreshed ⟨j,a.val⟩) spatial kernel block
      C N (fun z => (selected z : ZMod N)) =
    allocatedCongruenceModulusBad inactive
      (allocatedReadNoise f) (allocatedReadDeck f)
      (fun j a => allocatedReadProjection f ⟨j,a.val⟩) spatial kernel block
      C N (fun z => (c z : ZMod N)) := by
  unfold allocatedCongruenceModulusBad
  simp only [allocatedActualRefresh_rank_probability]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MixedSelectedCoefficientProbability
namespace OAI

section

namespace Erdos3
open scoped Classical

theorem pmf_bind_toReal_point_cap {X Y : Type*} (p : PMF X) (q : X → PMF Y)
    (y : Y) {δ : ℝ} (hδ : 0 ≤ δ) (hq : ∀ x, (q x y).toReal ≤ δ) :
    (p.bind q y).toReal ≤ δ := by
  have hpoint (x : X) : q x y ≤ ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_toReal ((q x).apply_ne_top y)]
    exact ENNReal.ofReal_le_ofReal (hq x)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (pmf_bind_point_cap p q y hpoint)).trans_eq (ENNReal.toReal_ofReal hδ)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical
open FiniteProbabilityWeights

theorem pmf_pair_selected_event_cap
    {X Y TX TY SX SY : Type*} (p : PMF X) (q : PMF Y)
    (pt : PMF TX) (qt : PMF TY) (ps : PMF SX) (qs : PMF SY)
    (joinX : TX → SX → X) (joinY : TY → SY → Y)
    (hp : p = pt.bind (fun t => ps.map (joinX t)))
    (hq : q = qt.bind (fun t => qs.map (joinY t)))
    (bad : X → Y → Prop) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbad : ∀ tx ty,
      ((ps.bind (fun x => qs.map (fun y => decide (bad (joinX tx x) (joinY ty y))))) true).toReal ≤ δ) :
    ((p.bind (fun x => q.map (fun y => decide (bad x y)))) true).toReal ≤ δ := by
  rw [hp, PMF.bind_bind]
  apply pmf_bind_toReal_point_cap _ _ true hδ
  intro tx
  rw [PMF.bind_map]
  change ((ps.bind (fun x => q.map (fun y => decide (bad (joinX tx x) y)))) true).toReal ≤ δ
  have he : ps.bind (fun x => q.map (fun y => decide (bad (joinX tx x) y))) =
      qt.bind (fun ty => ps.bind (fun x => qs.map
        (fun y => decide (bad (joinX tx x) (joinY ty y))))) := by
    simp_rw [hq, PMF.map_bind, PMF.map_comp]
    exact PMF.bind_comm ps qt _
  rw [he]
  exact pmf_bind_toReal_point_cap _ _ true hδ (hbad tx)

theorem uniform_weights_toPMF {Y : Type*} [Fintype Y] [Nonempty Y] :
    (uniform Y).toPMF = PMF.uniformOfFintype Y := by
  ext y
  simp only [toPMF_apply, uniform, PMF.uniformOfFintype_apply]
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]

theorem supportedPMF_prod_uniform_event_eq_bind
    {X Y : Type*} [Fintype Y] [Nonempty Y]
    (p : PMF X) (T : Finset X) (hT : ∀ x ∉ T, (p x).toReal = 0)
    (bad : X → Y → Prop) :
    ((ofSupportedPMF p T hT).prod (uniform Y)).eventProbability
      (fun z => bad z.1.val z.2) =
      ((p.bind (fun x => (PMF.uniformOfFintype Y).map (fun y => decide (bad x y)))) true).toReal := by
  have he : p.bind (fun x => (PMF.uniformOfFintype Y).map (fun y => decide (bad x y))) =
      (PMF.uniformOfFintype Y).bind (fun y => p.map (fun x => decide (bad x y))) :=
    PMF.bind_comm p (PMF.uniformOfFintype Y) (fun x y => PMF.pure (decide (bad x y)))
  rw [he, ← uniform_weights_toPMF, toPMF_bind_toReal]
  change ((ofSupportedPMF p T hT).prod (uniform Y)).mean
    (fun z => if bad z.1.val z.2 then 1 else 0) = _
  rw [mean_prod, mean_comm]
  apply congrArg (uniform Y).mean
  funext y
  exact supportedPMF_event_eq_map_true p T hT (fun x => bad x y)

theorem shiftedSmoothProductFiniteWeights_prod_uniform_event_eq_bind
    {J Y : Type*} [Fintype J] [Fintype Y] [Nonempty Y]
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) (hZ : 0 < shiftedSmoothProductMass a S)
    (bad : (J → ℤ) → Y → Prop) :
    ((shiftedSmoothProductFiniteWeights a S hS hZ).prod (uniform Y)).eventProbability
      (fun z => bad z.1.val z.2) =
      (((shiftedSmoothProductPMF a S hS hZ).bind
        (fun x => (PMF.uniformOfFintype Y).map (fun y => decide (bad x y)))) true).toReal :=
  supportedPMF_prod_uniform_event_eq_bind _ _ _ bad

theorem independentProduct_uniform_refresh_event_probability_le
    {A J B K : Type*} [Fintype A] [Fintype J] [Fintype B] [Fintype K]
    (e : A ↪ J) (d : B ↪ K) (p : J → PMF ℤ)
    (a S : A → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hselected : independentProductPMF (fun i => p (e i)) = shiftedSmoothProductPMF a S hS hZ)
    (N : ℕ) [NeZero N] (bad : (J → ℤ) → (K → ZMod N) → Prop) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbad : ∀ (fixed : J → ℤ) (fixedDeck : K → ZMod N),
      (((shiftedSmoothProductPMF a S hS hZ).bind
        (fun c => (PMF.uniformOfFintype (B → ZMod N)).map
          (fun z => decide (bad (Function.extend e c fixed)
            (Function.extend d z fixedDeck))))) true).toReal ≤ δ) :
    (((independentProductPMF p).bind
      (fun x => (PMF.uniformOfFintype (K → ZMod N)).map
        (fun y => decide (bad x y)))) true).toReal ≤ δ := by
  let : Fintype (SelectedCoefficientComplement e) :=
    Subtype.fintype (fun column => column ∉ Set.range e)
  let : Fintype (SelectedCoefficientComplement d) :=
    Subtype.fintype (fun column => column ∉ Set.range d)
  have hp : independentProductPMF p =
      (independentProductPMF (fun t : SelectedCoefficientComplement e => p t.val)).bind
        (fun tail => (shiftedSmoothProductPMF a S hS hZ).map
          (selectedCoefficientJoin e (0 : ℤ) tail)) := by
    rw [independentProductPMF_selected_split e (0 : ℤ) p, hselected] <;> congr!
  apply pmf_pair_selected_event_cap (independentProductPMF p)
    (PMF.uniformOfFintype (K → ZMod N))
    (independentProductPMF (fun t : SelectedCoefficientComplement e => p t.val))
    (PMF.uniformOfFintype (SelectedCoefficientComplement d → ZMod N))
    (shiftedSmoothProductPMF a S hS hZ) (PMF.uniformOfFintype (B → ZMod N))
    (selectedCoefficientJoin e (0 : ℤ)) (selectedCoefficientJoin d (0 : ZMod N))
    hp (by convert uniformZMod_selected_split N d) bad hδ
  intro tx ty
  exact hbad (selectedCoefficientComplementFill e (0 : ℤ) tx)
    (selectedCoefficientComplementFill d (0 : ZMod N) ty)

theorem independentProductPMF_selected_smooth {A J : Type*} [Fintype A]
    (e : A → J) (p : J → PMF ℤ)
    (a S : A → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hcoordinate : ∀ i, p (e i) = shiftedSmoothCoefficientPMF (a i) (S i) (hS i)
      (shiftedSmoothProductMass_coordinate_pos a S hS hZ i)) :
    independentProductPMF (fun i => p (e i)) = shiftedSmoothProductPMF a S hS hZ := by
  rw [shiftedSmoothProductPMF_eq_independent]
  exact congrArg independentProductPMF (funext hcoordinate)

theorem independentProduct_uniform_smooth_selected_event_probability_le
    {A J B K : Type*} [Fintype A] [Fintype J] [Fintype B] [Fintype K]
    (e : A ↪ J) (d : B ↪ K) (p : J → PMF ℤ)
    (a S : A → ℝ) (hS : ∀ i, 0 < S i) (hZ : 0 < shiftedSmoothProductMass a S)
    (hcoordinate : ∀ i, p (e i) = shiftedSmoothCoefficientPMF (a i) (S i) (hS i)
      (shiftedSmoothProductMass_coordinate_pos a S hS hZ i))
    (N : ℕ) [NeZero N] (bad : (J → ℤ) → (K → ZMod N) → Prop) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbad : ∀ (fixed : J → ℤ) (fixedDeck : K → ZMod N),
      ((shiftedSmoothProductFiniteWeights a S hS hZ).prod (uniform (B → ZMod N))).eventProbability
        (fun z => bad (Function.extend e z.1.val fixed) (Function.extend d z.2 fixedDeck)) ≤ δ) :
    (((independentProductPMF p).bind
      (fun x => (PMF.uniformOfFintype (K → ZMod N)).map
        (fun y => decide (bad x y)))) true).toReal ≤ δ := by
  apply independentProduct_uniform_refresh_event_probability_le e d p a S hS hZ
    (independentProductPMF_selected_smooth e p a S hS hZ hcoordinate) N bad hδ
  intro fixed fixedDeck
  have he := shiftedSmoothProductFiniteWeights_prod_uniform_event_eq_bind a S hS hZ
    (fun x y => bad (Function.extend e x fixed) (Function.extend d y fixedDeck))
  exact he.symm.trans_le (hbad fixed fixedDeck)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedModularRankAffineFullWitness
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights

private theorem affineWitness_uniform_le (Y : Type*) (f g : Fintype Y)
    [Nonempty Y] (F : Y → Prop) (r : ℝ)
    (h : @eventProbability Y f (@uniform Y f _) F ≤ r) :
    @eventProbability Y g (@uniform Y g _) F ≤ r := by
  cases Subsingleton.elim f g
  exact h

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable local instance affineWitnessSmoothIndexFintype_rb66b26_1 (inactive : LayerSamplerAxis I n → Prop) :
    Fintype (AllocatedSmoothRankCoefficientIndex X inactive L) := inferInstance
attribute [local instance] OAI.Erdos3.VectorPolynomial.affineWitnessDeckIndexFintype
attribute [local instance] OAI.Erdos3.VectorPolynomial.affineWitnessDeckIndexDecidableEq
noncomputable local instance affineWitnessCongruenceIndexFintype_rb66b26_1 (inactive : LayerSamplerAxis I n → Prop) :
    Fintype (AllocatedCongruenceCoefficientIndex X E inactive L) := inferInstance
noncomputable local instance affineWitnessCongruenceIndexDecidableEq_rb66b26_1 (inactive : LayerSamplerAxis I n → Prop) :
    DecidableEq (AllocatedCongruenceCoefficientIndex X E inactive L) := Classical.decEq _
variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

theorem allocatedAffineMixed_primePower_event {N D : ℕ} [NeZero N]
    (hm : 0 < m) (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (offset : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    (center width : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ)
    (hwidth : ∀ j, 0 < width j) (hZ : 0 < shiftedSmoothProductMass center width)
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hpositive : ∀ p ∈ P, 0 < A p)
    (hdeep : ∀ p ∈ P, ∀ x, 2 * (stride x).factorization p ≤ A p)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hthreshold : ∀ p ∈ P, modularCoefficientPrimeThreshold m ≤ p ^ A p)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : P, p.val ^ A p.val) ≤ width j) :
    ((shiftedSmoothProductFiniteWeights center width hwidth hZ).prod
      (uniform (AllocatedDeckRankCoefficientIndex E L → ZMod N))).eventProbability
      (fun x => ∀ p : P, allocatedCongruenceModulusBad inactive noise r projection spatial kernel block
        C (p.val ^ A p.val) (fun j =>
          (allocatedMixedAffineSelectedValues inactive (fun x => (stride x : ℤ)) offset
            x.1.val x.2 j : ZMod (p.val ^ A p.val)))) ≤
      1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) *
          (∏ p : P, p.val ^ A p.val) / width j := by
  have h := mixedSmoothUniform_primePower_event (N := N) center width hwidth hZ P A
    hprime hcover
    (fun p => allocatedAffineMixedModulusBad inactive noise r projection spatial kernel block
      stride offset C (p.val ^ A p.val))
    (fun p => by
      have ht := allocatedAffineMixedModulusBad_probability_s2 inactive noise r projection spatial kernel block
        hm (hprime p p.property) (hpositive p p.property) hD stride hstride (hdeep p p.property)
        offset hC (hthreshold p p.property) hL
      exact affineWitness_uniform_le _ _ _ _ _ ht)
    hlarge
  simpa only [allocatedAffineMixedModulusBad, allocatedMixedAffineSelectedValues_natCast] using h

theorem allocatedAffineMixedActual_primePower_event
    (fixed : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    {N D : ℕ} [NeZero N]
    (hm : 0 < m) (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (offset : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    (center width : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ)
    (hwidth : ∀ j, 0 < width j) (hZ : 0 < shiftedSmoothProductMass center width)
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hpositive : ∀ p ∈ P, 0 < A p)
    (hdeep : ∀ p ∈ P, ∀ x, 2 * (stride x).factorization p ≤ A p)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hthreshold : ∀ p ∈ P, modularCoefficientPrimeThreshold m ≤ p ^ A p)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : P, p.val ^ A p.val) ≤ width j) :
    ((shiftedSmoothProductFiniteWeights center width hwidth hZ).prod
      (uniform (AllocatedDeckRankCoefficientIndex E L → ZMod N))).eventProbability
      (fun x => ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
        (Function.extend (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block)
          (allocatedMixedAffineSelectedValues inactive (fun x => (stride x : ℤ)) offset x.1.val x.2) fixed)) ≤
      1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) *
          (∏ p : P, p.val ^ A p.val) / width j := by
  have h := allocatedAffineMixed_primePower_event inactive
    (allocatedReadNoise fixed) (allocatedReadDeck fixed)
    (fun j a => allocatedReadProjection fixed ⟨j,a.val⟩) spatial kernel block hm stride hstride offset
    center width hwidth hZ P A hprime hcover hpositive hdeep hD hC hL hthreshold hlarge
  simpa only [allocatedActualModulusBad, allocatedActualRefresh_modulusBad] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical
open FiniteProbabilityWeights
attribute [local irreducible] allocatedActualModulusBad allocatedMixedFullArray independentProductPMF

private theorem affine_decide_eq_classical (p : Prop) [d : Decidable p] :
    @decide p d = @decide p (Classical.propDecidable p) := by
  cases Subsingleton.elim d (Classical.propDecidable p)
  rfl

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
    [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

attribute [local instance] OAI.Erdos3.VectorPolynomial.affineFullWitnessSmoothFintype
noncomputable local instance affineFullWitnessSmoothDecidableEq_rb66b26_1 :
    DecidableEq (AllocatedFullSmoothCoefficientIndex G X I n B) := Classical.decEq _
noncomputable local instance affineFullWitnessSelectedSmoothDecidableEq_rb66b26_1 (inactive : LayerSamplerAxis I n → Prop) :
    DecidableEq (AllocatedSmoothRankCoefficientIndex X inactive L) := Classical.decEq _
attribute [local instance] OAI.Erdos3.VectorPolynomial.affineFullWitnessDeckFintype
attribute [local instance] OAI.Erdos3.VectorPolynomial.affineFullWitnessDeckDecidableEq
noncomputable local instance affineFullWitnessSelectedSmoothFintype_rb66b26_1 (inactive : LayerSamplerAxis I n → Prop) :
    Fintype (AllocatedSmoothRankCoefficientIndex X inactive L) := inferInstance
attribute [local instance] OAI.Erdos3.VectorPolynomial.affineFullWitnessSelectedDeckFintype
attribute [local instance] OAI.Erdos3.VectorPolynomial.affineFullWitnessSelectedDeckDecidableEq
theorem allocatedAffineProductMixed_primePower_event_s2_oai
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → ℤ)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (residue : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (laws : AllocatedFullSmoothCoefficientIndex G X I n B → PMF ℤ)
    {N D : ℕ} [NeZero N] (hm : 0 < m)
    (center width : AllocatedSmoothRankCoefficientIndex X inactive L → ℝ)
    (hwidth : ∀ j, 0 < width j) (hZ : 0 < shiftedSmoothProductMass center width)
    (hcoordinate : ∀ i, laws (allocatedSmoothFullEmbedding inactive spatial block i) =
      shiftedSmoothCoefficientPMF (center i) (width i) (hwidth i)
        (shiftedSmoothProductMass_coordinate_pos center width hwidth hZ i))
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) (hcover : ∀ p ∈ P, p ^ A p ∣ N)
    (hpositive : ∀ p ∈ P, 0 < A p)
    (hdeep : ∀ p ∈ P, ∀ x, 2 * (stride x).factorization p ≤ A p)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    {C : ℝ} (hC : 0 ≤ C)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L)
    (hthreshold : ∀ p ∈ P, modularCoefficientPrimeThreshold m ≤ p ^ A p)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (∏ p : P, p.val ^ A p.val) ≤ width j) :
    (((independentProductPMF laws).bind
      (fun x => (PMF.uniformOfFintype
        (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N)).map
        (fun deck => decide (∀ p : P,
          allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
            (allocatedMixedFullArray (allocatedFullSmoothAffine (fun x => (stride x : ℤ)) residue x)
            (fun i => (deck i).val) continuous))))) true).toReal ≤
      1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
        ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (∏ p : P, p.val ^ A p.val) / width j := by
  let e := allocatedSmoothFullEmbedding (X := X) inactive spatial block
  let d := allocatedDeckFullEmbedding (E := E) (I := I) (n := n) (B := B) kernel
  let bad : (AllocatedFullSmoothCoefficientIndex G X I n B → ℤ) →
      (CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N) → Prop :=
    fun x deck => ∀ p : P,
    allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
      (allocatedMixedFullArray (allocatedFullSmoothAffine (fun x => (stride x : ℤ)) residue x)
            (fun i => (deck i).val) continuous)
  let δ : ℝ := 1 / ((∏ p : P, p.val ^ A p.val : ℕ) : ℝ) ^ 10 +
    ∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (∏ p : P, p.val ^ A p.val) / width j
  have hδ : 0 ≤ δ := add_nonneg (by positivity)
    (Finset.sum_nonneg (fun j _ => div_nonneg (by positivity) (hwidth _).le))
  have hconditional : ∀ (fixed : AllocatedFullSmoothCoefficientIndex G X I n B → ℤ)
      (fixedDeck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N),
      ((shiftedSmoothProductFiniteWeights center width hwidth hZ).prod
        (uniform (AllocatedDeckRankCoefficientIndex E L → ZMod N))).eventProbability
        (fun z => bad (Function.extend e z.1.val fixed) (Function.extend d z.2 fixedDeck)) ≤ δ := by
    intro fixed fixedDeck
    have h := allocatedAffineMixedActual_primePower_event inactive spatial kernel block
      (allocatedMixedFullArray
        (allocatedFullSmoothAffine (fun x => (stride x : ℤ)) residue fixed)
        (fun i => (fixedDeck i).val) continuous) hm stride hstride
      (allocatedSelectedNoiseOffset inactive spatial residue)
      center width hwidth hZ P A hprime hcover hpositive hdeep hD hC hL hthreshold hlarge
    simpa only [e, d, bad, δ, allocatedMixedFullArray_affine_refresh_selected] using h
  simpa only [bad, δ, affine_decide_eq_classical] using
    independentProduct_uniform_smooth_selected_event_probability_le
      e d laws center width hwidth hZ hcoordinate N bad hδ hconditional

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedAffineProductMixed_primePower_event_s2_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedAffineProductMixed_primePower_event_s2_oai.{u_1, u_2, u_3, u_4, u_5}
