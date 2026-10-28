-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.slope_line_action
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:04:31.992531+00:00
-- url     : https://prove2.me/submissions/dd008340-7caf-4770-8fb4-fbfaf4623d21

import Mathlib
import Definitions.Def_OAIQ65Sa015
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_tangent_interval_action

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_PropagationArithmetic
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section BoundedOneDimensionalOrdering

variable {α : Type*}

private theorem real_list_sum_nonpos {l : List ℝ} (h : ∀ x ∈ l, x ≤ 0) : l.sum ≤ 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    exact add_nonpos (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem exists_bounded_step_order (v : α → ℝ) (xs : List α)
    {L U δ x : ℝ} (hLU : L ≤ U) (_hδ : 0 ≤ δ)
    (hstep : ∀ t ∈ xs, |v t| ≤ δ)
    (hx : L-δ ≤ x ∧ x ≤ U+δ)
    (hy : L ≤ x+(xs.map v).sum ∧ x+(xs.map v).sum ≤ U) :
    ∃ ys : List α, ys.Perm xs ∧
      ∀ n : ℕ, L-δ ≤ x+((ys.take n).map v).sum ∧
        x+((ys.take n).map v).sum ≤ U+δ := by
  classical
  induction hn : xs.length using Nat.strong_induction_on generalizing xs x with
  | h n ih =>
    by_cases hnil : xs = []
    · subst xs
      exact ⟨[],List.Perm.refl _,fun _ => by simpa using hx⟩
    have hcons : ∃ t, t ∈ xs := List.exists_mem_of_ne_nil xs hnil
    have hchoose : ∃ t ∈ xs, L-δ ≤ x+v t ∧ x+v t ≤ U+δ := by
      by_cases hlow : x < L
      · have hp : ∃ t ∈ xs, 0 < v t := by
          by_contra! hp
          have hz : (xs.map v).sum ≤ 0 := real_list_sum_nonpos (by
            intro r hr
            obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
            exact hp t ht)
          linarith [hy.1]
        obtain ⟨t,ht,hpos⟩ := hp
        refine ⟨t,ht,by linarith [hx.1],?_⟩
        linarith [(abs_le.mp (hstep t ht)).2]
      · by_cases hhigh : U < x
        · have hp : ∃ t ∈ xs, v t < 0 := by
            by_contra! hp
            have hz : 0 ≤ (xs.map v).sum := List.sum_nonneg (by
              intro r hr
              obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
              exact hp t ht)
            linarith [hy.2]
          obtain ⟨t,ht,hneg⟩ := hp
          refine ⟨t,ht,?_,by linarith [hx.2]⟩
          linarith [(abs_le.mp (hstep t ht)).1]
        · obtain ⟨t,ht⟩ := hcons
          refine ⟨t,ht,?_,?_⟩ <;> linarith [abs_le.mp (hstep t ht)]
    obtain ⟨t,ht,htx⟩ := hchoose
    have hperm : (t :: xs.erase t).Perm xs := (List.perm_cons_erase ht).symm
    have he : v t + ((xs.erase t).map v).sum = (xs.map v).sum := by
      have := (hperm.map v).sum_eq
      simpa using this
    have hlen : (xs.erase t).length < n := by
      rw [← hn]
      rw [List.length_erase_of_mem ht]
      have : 0 < xs.length := List.length_pos_iff.mpr hnil
      omega
    obtain ⟨ys,hys,hbounds⟩ := ih _ hlen (xs.erase t) (x := x+v t)
      (fun s hs => hstep s (List.mem_of_mem_erase hs)) htx
      (by constructor <;> linarith [hy.1,hy.2]) rfl
    refine ⟨t::ys,(List.Perm.cons t hys).trans hperm,?_⟩
    intro k
    cases k with
    | zero => simpa using hx
    | succ k => simpa only [List.take_succ_cons,List.map_cons,List.sum_cons,add_assoc]
        using hbounds k

theorem exists_step_order_near_segment (v : α → ℝ) (xs : List α) {δ : ℝ}
    (hδ : 0 ≤ δ) (hstep : ∀ t ∈ xs, |v t| ≤ δ) :
    ∃ ys : List α, ys.Perm xs ∧ ∀ n : ℕ,
      min 0 (xs.map v).sum - δ ≤ ((ys.take n).map v).sum ∧
      ((ys.take n).map v).sum ≤ max 0 (xs.map v).sum + δ := by
  obtain ⟨ys,hy,hb⟩ := exists_bounded_step_order v xs
    (L := min 0 (xs.map v).sum) (U := max 0 (xs.map v).sum) (x := 0)
    min_le_max hδ hstep
    ⟨by linarith [min_le_left 0 (xs.map v).sum],
     by linarith [le_max_left 0 (xs.map v).sum]⟩
    ⟨by simp, by simp⟩
  exact ⟨ys,hy,fun n => by simpa using hb n⟩

end BoundedOneDimensionalOrdering

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ArithmeticTangentBasis
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ArithmeticTangentBasis

theorem cutRing_coefficients (z : CutRing) :
    (z.re : CutRing) + (z.im : CutRing)*cutTau = z := by
  apply QuadraticAlgebra.ext <;> simp [cutTau]

theorem cutRing_coefficients_bound (z : CutRing) :
    |(z.re : ℝ)| + |(z.im : ℝ)| ≤ 4 * (|ordinary z| + |conjugate z|) := by
  have hs : 1 ≤ Real.sqrt 5 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]
  have hq : |(z.im : ℝ)| ≤ |ordinary z| + |conjugate z| := by
    have he : (z.im : ℝ) * Real.sqrt 5 = ordinary z - conjugate z := by
      have := (eq_div_iff (by positivity : Real.sqrt 5 ≠ 0)).mp (endpointLabel_embedding z)
      exact this
    have ht : |ordinary z - conjugate z| ≤ |ordinary z| + |conjugate z| :=
      abs_sub _ _
    rw [← he,abs_mul,abs_of_nonneg (le_trans zero_le_one hs)] at ht
    nlinarith [abs_nonneg (z.im : ℝ)]
  have hp : |(z.re : ℝ)| ≤ |ordinary z| + 2*|(z.im : ℝ)| := by
    have he : (z.re : ℝ) = ordinary z - (z.im : ℝ)*Real.goldenRatio := by
      rw [ordinary_apply]
      ring
    rw [he]
    calc
      _ ≤ |ordinary z| + |(z.im : ℝ)*Real.goldenRatio| := abs_sub _ _
      _ = |ordinary z| + |(z.im : ℝ)| * Real.goldenRatio := by
        rw [abs_mul, abs_of_pos Real.goldenRatio_pos]
      _ ≤ _ := by nlinarith [Real.goldenRatio_lt_two,abs_nonneg (z.im : ℝ)]
  nlinarith [abs_nonneg (conjugate z)]

theorem tangent_basis_coefficients (u v : CutRing) (huv : u*v = 1) (d : CutRing) :
    ∃ p q : ℤ, d = (p : CutRing)*u + (q : CutRing)*(cutTau*u) ∧
      |(p : ℝ)| + |(q : ℝ)| ≤
        (4*(|ordinary v|+|conjugate v|+1))*(|ordinary d|+|conjugate d|) := by
  let z := d*v
  refine ⟨z.re,z.im,?_,?_⟩
  · have he : z*u = d := by dsimp [z]; calc
      d*v*u = d*(u*v) := by ring
      _ = d := by rw [huv,mul_one]
    calc
      d = z*u := he.symm
      _ = ((z.re : CutRing) + (z.im : CutRing)*cutTau)*u :=
        congrArg (fun w : CutRing => w*u) (cutRing_coefficients z).symm
      _ = _ := by ring
  · have hb := cutRing_coefficients_bound z
    have ho : |ordinary z| = |ordinary d| * |ordinary v| := by simp [z,abs_mul]
    have hc : |conjugate z| = |conjugate d| * |conjugate v| := by simp [z,abs_mul]
    rw [ho,hc] at hb
    nlinarith [abs_nonneg (ordinary d),abs_nonneg (conjugate d),
      abs_nonneg (ordinary v),abs_nonneg (conjugate v),
      mul_nonneg (abs_nonneg (ordinary d)) (abs_nonneg (conjugate v)),
      mul_nonneg (abs_nonneg (conjugate d)) (abs_nonneg (ordinary v))]

end ArithmeticTangentBasis

section FiniteTangentChains

theorem integerSteps_length (k : ℤ) (u : CutRing) :
    ((integerSteps k u).length : ℝ) = |(k : ℝ)| := by
  by_cases hk : 0 ≤ k
  · have hc : (k.toNat : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk
    simp [integerSteps,hk,hc,abs_of_nonneg (by exact_mod_cast hk : (0:ℝ) ≤ k)]
  · have hn : 0 ≤ -k := by omega
    have hc : ((-k).toNat : ℝ) = -(k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
    simp [integerSteps,hk,hc,abs_of_nonpos (by exact_mod_cast (le_of_not_ge hk) : (k:ℝ) ≤ 0)]

theorem integerSteps_mem (k : ℤ) (u e : CutRing) (he : e ∈ integerSteps k u) :
    e = u ∨ e = -u := by
  by_cases hk : 0 ≤ k
  · left
    exact (List.mem_replicate.mp (by simpa only [integerSteps,ite_eq_left hk] using he)).2
  · right
    exact (List.mem_replicate.mp (by simpa only [integerSteps,ite_eq_right hk] using he)).2

private theorem sum_abs_bound_by_length {α : Type*} (v : α → ℝ)
    (xs : List α) {B : ℝ} (hs : ∀ x ∈ xs, |v x| ≤ B) :
    |(xs.map v).sum| ≤ (xs.length : ℝ)*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hs x (by simp)
    have ht := ih (fun y hy => hs y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    calc
      |v x + (xs.map v).sum| ≤ |v x| + |(xs.map v).sum| := abs_add_le _ _
      _ ≤ B + (xs.length : ℝ)*B := add_le_add hx ht
      _ = _ := by ring

theorem tangent_chain (u v : CutRing) (huv : u*v = 1) (d : CutRing) :
    ∃ w : List CutRing,
      w.sum = d ∧
      (∀ e ∈ w, e = u ∨ e = -u ∨ e = cutTau*u ∨ e = -(cutTau*u)) ∧
      (w.length : ℝ) ≤ (4*(|ordinary v|+|conjugate v|+1))*(|ordinary d|+|conjugate d|) ∧
      (∀ n : ℕ,
        min 0 (ordinary d) - (|ordinary u|+|ordinary (cutTau*u)|) ≤
          ordinary (w.take n).sum ∧
        ordinary (w.take n).sum ≤
          max 0 (ordinary d) + (|ordinary u|+|ordinary (cutTau*u)|)) ∧
      ∀ n : ℕ, |(endpointLabel (w.take n).sum : ℝ)| ≤
        (4*(|ordinary v|+|conjugate v|+1))*(|ordinary d|+|conjugate d|)*
          (|(endpointLabel u : ℝ)|+|(endpointLabel (cutTau*u) : ℝ)|) := by
  obtain ⟨p,q,hd,hpq⟩ := tangent_basis_coefficients u v huv d
  let xs := integerSteps p u ++ integerSteps q (cutTau*u)
  have hsum : xs.sum = d := by simp only [xs,List.sum_append,integerSteps_sum]; exact hd.symm
  have hmem : ∀ e ∈ xs, e = u ∨ e = -u ∨ e = cutTau*u ∨ e = -(cutTau*u) := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · rcases integerSteps_mem p u e he with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · rcases integerSteps_mem q (cutTau*u) e he with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
  have ho : ∀ e ∈ xs, |ordinary e| ≤ |ordinary u|+|ordinary (cutTau*u)| := by
    intro e he
    rcases hmem e he with he | he | he | he
    · rw [he]; exact le_add_of_nonneg_right (abs_nonneg _)
    · rw [he,map_neg,abs_neg]; exact le_add_of_nonneg_right (abs_nonneg _)
    · rw [he]; exact le_add_of_nonneg_left (abs_nonneg _)
    · rw [he,map_neg,abs_neg]; exact le_add_of_nonneg_left (abs_nonneg _)
  obtain ⟨w,hw,hbound⟩ := exists_step_order_near_segment ordinary xs (by positivity) ho
  have hwsum : w.sum = d := hw.sum_eq.trans hsum
  have hwm : ∀ e ∈ w, e = u ∨ e = -u ∨ e = cutTau*u ∨ e = -(cutTau*u) :=
    fun e he => hmem e (hw.mem_iff.mp he)
  have hlen : (w.length : ℝ) ≤
      (4*(|ordinary v|+|conjugate v|+1))*(|ordinary d|+|conjugate d|) := by
    rw [hw.length_eq]
    simpa only [xs,List.length_append,Nat.cast_add,integerSteps_length] using hpq
  refine ⟨w,hwsum,hwm,hlen,?_,?_⟩
  · intro n
    simpa only [← map_list_sum,hsum] using hbound n
  · intro n
    let B := |(endpointLabel u : ℝ)|+|(endpointLabel (cutTau*u) : ℝ)|
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hb : ∀ e ∈ w.take n, |(endpointLabel e : ℝ)| ≤ B := by
      intro e he
      have hew := List.mem_of_mem_take he
      have hneg : ∀ z : CutRing, |(endpointLabel (-z) : ℝ)| = |(endpointLabel z : ℝ)| := by
        intro z
        simp only [endpointLabel,QuadraticAlgebra.im_neg,Int.cast_neg,abs_neg]
      rcases hwm e hew with he | he | he | he
      · rw [he]; exact le_add_of_nonneg_right (abs_nonneg _)
      · rw [he,hneg]; exact le_add_of_nonneg_right (abs_nonneg _)
      · rw [he]; exact le_add_of_nonneg_left (abs_nonneg _)
      · rw [he,hneg]; exact le_add_of_nonneg_left (abs_nonneg _)
    rw [endpointLabel_list_sum]
    calc
      _ ≤ ((w.take n).length : ℝ)*B := sum_abs_bound_by_length _ _ hb
      _ ≤ (w.length : ℝ)*B := mul_le_mul_of_nonneg_right (by exact_mod_cast (show (w.take n).length ≤ w.length by simp only [List.length_take]; exact min_le_right _ _)) hB
      _ ≤ _ := mul_le_mul_of_nonneg_right hlen hB

end FiniteTangentChains

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TangentWalkCenters
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section TangentWalkCenters

theorem tangentOffset_ordinary_bound (a : ℕ) (d : Fin 2) (w : CutRing) (j : Fin 2) :
    |ordinary (pointCoordinate (tangentOffset a d w) j)| ≤
      (1+|ordinary (cutTau^a)|)*|ordinary w| := by
  have h0 := abs_nonneg (ordinary w)
  have h1 := abs_nonneg (ordinary (cutTau^a))
  fin_cases d <;> fin_cases j
  · change |ordinary w| ≤ _
    nlinarith [mul_nonneg h0 h1]
  · change |ordinary (cutTau^a*w)| ≤ _
    rw [map_mul,abs_mul]
    nlinarith
  · change |ordinary (cutTau^a*w)| ≤ _
    rw [map_mul,abs_mul]
    nlinarith
  · change |ordinary w| ≤ _
    nlinarith [mul_nonneg h0 h1]

end TangentWalkCenters

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SymmetricCharts
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SymmetricCharts

theorem signedShortSteps_bound (u : CutRing) (e : Fin 5) :
    |ordinary (signedShortSteps u e)| ≤ |ordinary u|+|ordinary (cutTau*u)| := by
  have h₀ := abs_nonneg (ordinary u)
  have h₁ := abs_nonneg (ordinary (cutTau*u))
  fin_cases e
  · change |ordinary 0| ≤ _
    rw [map_zero,abs_zero]
    linarith
  · exact le_add_of_nonneg_right h₁
  · change |ordinary (-u)| ≤ _
    rw [map_neg,abs_neg]
    exact le_add_of_nonneg_right h₁
  · exact le_add_of_nonneg_left h₀
  · change |ordinary (-(cutTau*u))| ≤ _
    rw [map_neg,abs_neg]
    exact le_add_of_nonneg_left h₀

end SymmetricCharts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Homology_ClippedLineSlide
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ClippedLineSlide

theorem tangentCoefficient_pos (a : ℕ) (d j : Fin 2) : 0 < tangentCoefficient a d j := by
  fin_cases d <;> fin_cases j <;> simp [tangentCoefficient,pointCoordinate,tangentOffset,
    pow_pos Real.goldenRatio_pos]

theorem tangentCoefficient_bound (a : ℕ) (d j : Fin 2) :
    tangentCoefficient a d j ≤ 1+|ordinary (cutTau^a)| := by
  fin_cases d <;> fin_cases j <;> simp [tangentCoefficient,pointCoordinate,tangentOffset,
    abs_of_pos (pow_pos Real.goldenRatio_pos a)] <;> positivity

theorem tangentAllowed_iff (a : ℕ) (r : CutRing) (d : Fin 2)
    (z : CutRing × CutRing) (L V : Fin 2 → CutRing) (t : ℝ) :
    (tangentAllowedLower a r d z V ≤ t ∧ t ≤ tangentAllowedUpper a r d z L) ↔
      ∀ j : Fin 2, -ordinary r ≤ ordinary (L j)-(ordinary (pointCoordinate z j)+tangentCoefficient a d j*t) ∧
        ordinary (V j)-(ordinary (pointCoordinate z j)+tangentCoefficient a d j*t) ≤ ordinary r := by
  constructor
  · rintro ⟨hl,hu⟩ j
    have hl' : (ordinary (V j)-ordinary (pointCoordinate z j)-ordinary r)/tangentCoefficient a d j ≤ t := by
      fin_cases j
      · exact (le_max_left _ _).trans hl
      · exact (le_max_right _ _).trans hl
    have hu' : t ≤ (ordinary (L j)-ordinary (pointCoordinate z j)+ordinary r)/tangentCoefficient a d j := by
      fin_cases j
      · exact hu.trans (min_le_left _ _)
      · exact hu.trans (min_le_right _ _)
    have hlo := (div_le_iff₀ (tangentCoefficient_pos a d j)).mp hl'
    have hup := (le_div_iff₀ (tangentCoefficient_pos a d j)).mp hu'
    constructor <;> nlinarith
  · intro h
    have hlo (j : Fin 2) :
        (ordinary (V j)-ordinary (pointCoordinate z j)-ordinary r)/tangentCoefficient a d j ≤ t := by
      apply (div_le_iff₀ (tangentCoefficient_pos a d j)).mpr
      have hh := (h j).2
      nlinarith
    have hup (j : Fin 2) :
        t ≤ (ordinary (L j)-ordinary (pointCoordinate z j)+ordinary r)/tangentCoefficient a d j := by
      apply (le_div_iff₀ (tangentCoefficient_pos a d j)).mpr
      have hh := (h j).1
      nlinarith
    exact ⟨max_le (hlo 0) (hlo 1),le_min (hup 0) (hup 1)⟩

theorem tangentAllowed_wide (a : ℕ) (r u : CutRing) (hr : 0 < ordinary r)
    (d : Fin 2) (z : CutRing × CutRing) (L V : Fin 2 → CutRing) (c : ℝ)
    (hshort : 4*(1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) ≤ ordinary r)
    (hnear : ∀ j : Fin 2,
      |ordinary (L j)-(ordinary (pointCoordinate z j)+tangentCoefficient a d j*c)| ≤ ordinary r/4 ∧
      |ordinary (V j)-(ordinary (pointCoordinate z j)+tangentCoefficient a d j*c)| ≤ ordinary r/4) :
    4*(|ordinary u|+|ordinary (cutTau*u)|) ≤
      tangentAllowedUpper a r d z L-tangentAllowedLower a r d z V := by
  let b : ℝ := |ordinary u|+|ordinary (cutTau*u)|
  have hb : 0 ≤ b := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have he (j : Fin 2) : 2*tangentCoefficient a d j*b ≤ ordinary r/2 := by
    have hm := mul_le_mul_of_nonneg_right (tangentCoefficient_bound a d j) hb
    change 4*(1+|ordinary (cutTau^a)|)*b ≤ ordinary r at hshort
    nlinarith
  have hl := (tangentAllowed_iff a r d z L V (c-2*b)).mpr (by
    intro j
    have hn0 := abs_le.mp (hnear j).1
    have hn1 := abs_le.mp (hnear j).2
    have hh := he j
    have hp := mul_nonneg (tangentCoefficient_pos a d j).le hb
    constructor <;> nlinarith)
  have hu := (tangentAllowed_iff a r d z L V (c+2*b)).mpr (by
    intro j
    have hn0 := abs_le.mp (hnear j).1
    have hn1 := abs_le.mp (hnear j).2
    have hh := he j
    have hp := mul_nonneg (tangentCoefficient_pos a d j).le hb
    constructor <;> nlinarith)
  change 4*b ≤ _
  linarith

end ClippedLineSlide

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_IntervalTangentConnectivity
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section IntervalTangentConnectivity

theorem tangentIntervalStep_symm {u x y : CutRing} {L H : ℝ}
    (h : TangentIntervalStep u L H x y) : TangentIntervalStep u L H y x := by
  rcases h with ⟨h1,h2,h3,h4,h⟩
  refine ⟨h3,h4,h1,h2,?_⟩
  have he : x-y= -(y-x) := by abel
  rw [he]
  rcases h with h | h | h | h
  · exact Or.inr (Or.inl (congrArg Neg.neg h))
  · left; simpa using congrArg Neg.neg h
  · exact Or.inr (Or.inr (Or.inr (congrArg Neg.neg h)))
  · right; right; left; simpa using congrArg Neg.neg h

theorem tangentIntervalReach_symm {u x y : CutRing} {L H : ℝ}
    (h : TangentIntervalReach u L H x y) : TangentIntervalReach u L H y x := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.head (tangentIntervalStep_symm hstep)

theorem tangentInterval_natural (u v x : CutRing) (L H : ℝ) (n : ℕ)
    (hv : v=u ∨ v= -u)
    (hx : L ≤ ordinary x ∧ ordinary x ≤ H)
    (hy : L ≤ ordinary (x+(n:CutRing)*v) ∧ ordinary (x+(n:CutRing)*v) ≤ H) :
    TangentIntervalReach u L H x (x+(n:CutRing)*v) := by
  have hi (i : ℕ) (hin : i ≤ n) :
      L ≤ ordinary (x+(i:CutRing)*v) ∧ ordinary (x+(i:CutRing)*v) ≤ H := by
    have hi' : (i:ℝ) ≤ n := by exact_mod_cast hin
    simp only [map_add,map_mul,map_natCast] at hy ⊢
    by_cases hv0 : 0 ≤ ordinary v
    · have hm := mul_le_mul_of_nonneg_right hi' hv0
      have hp : 0 ≤ (i:ℝ)*ordinary v := mul_nonneg (Nat.cast_nonneg _) hv0
      constructor <;> linarith
    · have hm := mul_le_mul_of_nonpos_right hi' (le_of_not_ge hv0)
      have hp : (i:ℝ)*ordinary v ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
        (Nat.cast_nonneg _) (le_of_not_ge hv0)
      constructor <;> linarith
  have hpath i (hin : i ≤ n) : TangentIntervalReach u L H x (x+(i:CutRing)*v) := by
    induction i with
    | zero => simpa [TangentIntervalReach] using (Relation.ReflTransGen.refl (a := x) (r := TangentIntervalStep u L H))
    | succ i ih =>
      apply (ih (by omega)).tail
      refine ⟨(hi i (by omega)).1,(hi i (by omega)).2,(hi (i+1) hin).1,(hi (i+1) hin).2,?_⟩
      have he : x+((i+1:ℕ):CutRing)*v-(x+(i:CutRing)*v)=v := by push_cast; ring
      rw [he]
      rcases hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr (Or.inl hv)
  exact hpath n le_rfl

theorem tangentInterval_integer (u v x : CutRing) (L H : ℝ) (n : ℤ)
    (hv : v=u ∨ v= -u)
    (hx : L ≤ ordinary x ∧ ordinary x ≤ H)
    (hy : L ≤ ordinary (x+(n:CutRing)*v) ∧ ordinary (x+(n:CutRing)*v) ≤ H) :
    TangentIntervalReach u L H x (x+(n:CutRing)*v) := by
  by_cases hn : 0 ≤ n
  · have he : (n.toNat:CutRing)=(n:CutRing) := by exact_mod_cast Int.toNat_of_nonneg hn
    simpa only [he] using tangentInterval_natural u v x L H n.toNat hv hx (by simpa only [he] using hy)
  · have hev : -v=u ∨ -v= -u := by
      rcases hv with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (neg_neg u)
    have he : ((-n).toNat:CutRing)= -(n:CutRing) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ -n)
    simpa only [he,neg_mul_neg] using tangentInterval_natural u (-v) x L H (-n).toNat hev hx
      (by simpa only [he,neg_mul_neg] using hy)

theorem tangentInterval_list (u x : CutRing) (L H : ℝ) (w : List CutRing)
    (hw : ∀ e ∈ w, e=u ∨ e= -u ∨ e=cutTau*u ∨ e= -(cutTau*u))
    (hb : ∀ n, L ≤ ordinary (x+(w.take n).sum) ∧ ordinary (x+(w.take n).sum) ≤ H) :
    TangentIntervalReach u L H x (x+w.sum) := by
  have hp n (hn : n ≤ w.length) : TangentIntervalReach u L H x (x+(w.take n).sum) := by
    induction n with
    | zero => simpa [TangentIntervalReach] using (Relation.ReflTransGen.refl (a := x) (r := TangentIntervalStep u L H))
    | succ n ih =>
      have hn' : n < w.length := by omega
      apply (ih (by omega)).tail
      refine ⟨(hb n).1,(hb n).2,(hb (n+1)).1,(hb (n+1)).2,?_⟩
      have he : x+(w.take (n+1)).sum-(x+(w.take n).sum)=w[n] := by
        rw [List.take_add_one,List.getElem?_eq_getElem hn',Option.toList_some,List.sum_append,List.sum_singleton]
        abel
      rw [he]
      exact hw _ (List.getElem_mem hn')
  simpa using hp w.length le_rfl

theorem tangentInterval_recenter (u v : CutRing) (huv : u*v=1)
    (L H c : ℝ) (x : CutRing) (hx : L ≤ ordinary x ∧ ordinary x ≤ H)
    (hL : L ≤ c-|ordinary u|) (hH : c ≤ H) :
    ∃ y : CutRing, c-|ordinary u| < ordinary y ∧ ordinary y ≤ c ∧
      TangentIntervalReach u L H x y := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at huv
  have huo : ordinary u ≠ 0 := by simpa using ordinary_injective.ne hu0
  let u' : CutRing := if 0 ≤ ordinary u then u else -u
  have hu' : u'=u ∨ u'= -u := by dsimp [u']; split <;> simp
  have hpos : ordinary u'=|ordinary u| := by
    dsimp [u']; split_ifs with h
    · exact (abs_of_nonneg h).symm
    · rw [map_neg,abs_of_neg (lt_of_not_ge h)]
  have hα : 0 < ordinary u' := by rw [hpos]; exact abs_pos.mpr huo
  let n : ℤ := ⌊(c-ordinary x)/ordinary u'⌋
  let y : CutRing := x+(n:CutRing)*u'
  have hny : c-ordinary u' < ordinary y ∧ ordinary y ≤ c := by
    have hl := Int.floor_le ((c-ordinary x)/ordinary u')
    have hh := Int.lt_floor_add_one ((c-ordinary x)/ordinary u')
    have hl' := (le_div_iff₀ hα).mp hl
    have hh' := (div_lt_iff₀ hα).mp hh
    dsimp only [y]
    simp only [map_add,map_mul,map_intCast]
    dsimp only [n] at *
    constructor <;> linarith
  refine ⟨y,by simpa only [hpos] using hny.1,hny.2,?_⟩
  exact tangentInterval_integer u u' x L H n hu' hx
    ⟨hL.trans (by rw [← hpos]; exact hny.1.le),hny.2.trans hH⟩

theorem tangentInterval_connected (u v : CutRing) (huv : u*v=1)
    (L H : ℝ) (hwidth : 4*(|ordinary u|+|ordinary (cutTau*u)|) ≤ H-L)
    (x y : CutRing)
    (hx : L ≤ ordinary x ∧ ordinary x ≤ H)
    (hy : L ≤ ordinary y ∧ ordinary y ≤ H) : TangentIntervalReach u L H x y := by
  let c : ℝ := (L+H)/2
  let b : ℝ := |ordinary u|+|ordinary (cutTau*u)|
  have hb : 0 ≤ b := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hub : |ordinary u| ≤ b := le_add_of_nonneg_right (abs_nonneg _)
  have hlo : L ≤ c-|ordinary u| := by dsimp [c]; dsimp [b] at hub; linarith
  have hup : c ≤ H := by dsimp [c]; dsimp [b] at hb; linarith
  obtain ⟨x',hxL,hxH,hxx'⟩ := tangentInterval_recenter u v huv L H c x hx hlo hup
  obtain ⟨y',hyL,hyH,hyy'⟩ := tangentInterval_recenter u v huv L H c y hy hlo hup
  obtain ⟨w,hws,hwm,_,hwb,_⟩ := tangent_chain u v huv (y'-x')
  have hm : TangentIntervalReach u L H x' y' := by
    have he : x'+w.sum=y' := by rw [hws]; abel
    rw [← he]
    apply tangentInterval_list u x' L H w hwm
    intro n
    have hn := hwb n
    simp only [map_add,map_sub] at hn ⊢
    change min 0 (ordinary y'-ordinary x')-b ≤ ordinary (w.take n).sum ∧
      ordinary (w.take n).sum ≤ max 0 (ordinary y'-ordinary x')+b at hn
    have hw' : 4*b ≤ H-L := hwidth
    have hcL : L ≤ c-2*b := by dsimp [c]; linarith
    have hcH : c+2*b ≤ H := by dsimp [c]; linarith
    by_cases hh : ordinary x' ≤ ordinary y'
    · rw [min_eq_left (by linarith),max_eq_right (by linarith)] at hn
      constructor <;> linarith
    · rw [min_eq_right (by linarith),max_eq_left (by linarith)] at hn
      constructor <;> linarith
  exact hxx'.trans (hm.trans (tangentIntervalReach_symm hyy'))

end IntervalTangentConnectivity

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_ClippedLineSlideAction
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section ClippedLineSlideAction
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem tangent_line_slide (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (g : ∀ n, B.CoordinateWindowLaw n)
    (k : ℕ) (p : Fin 2 → ℤ) (u v : CutRing) (huv : u*v=1)
    (h : B.TangentChartLaws k p u)
    (hshort : 4*(1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) ≤ ordinary r)
    (hlabels : ∀ d e j,
      (p j ≤ endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) ∧
       endpointLabel (clippingOverlapLower r (tangentOffset a d (signedShortSteps u e)) j) < p j+k) ∧
      (p j ≤ endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) ∧
       endpointLabel (clippingOverlapUpper r (tangentOffset a d (signedShortSteps u e)) j) < p j+k))
    (d : Fin 2) (z : CutRing × CutRing) (w : CutRing) (L V : Fin 2 → CutRing)
    (hLV : ∀ j, ordinary (L j) ≤ ordinary (V j))
    (hz : ∀ j, -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate z j) ∧
      ordinary (V j)-ordinary (pointCoordinate z j) ≤ ordinary r)
    (hzw : ∀ j, -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate (z+tangentOffset a d w) j) ∧
      ordinary (V j)-ordinary (pointCoordinate (z+tangentOffset a d w) j) ≤ ordinary r)
    (c : ℝ)
    (hnear : ∀ j,
      |ordinary (L j)-(ordinary (pointCoordinate z j)+tangentCoefficient a d j*c)| ≤ ordinary r/4 ∧
      |ordinary (V j)-(ordinary (pointCoordinate z j)+tangentCoefficient a d j*c)| ≤ ordinary r/4)
    (n : ℕ) (q : Fin 2 → ℤ)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) (coordinateRectangle a L V).val)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (g n) q (coordinateRectangle a L V)))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (t : BoundedRelationCover M (alternatingGenerator a r m hm)) (ht : t ∈ f.range) :
    B.tangentSign (by omega) k p u h d z true (universalMap (subtypeAlternatingHom I.val) s)*t*
      (B.tangentSign (by omega) k p u h d z true (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    B.tangentSign (by omega) k p u h d (z+tangentOffset a d w) true
        (universalMap (subtypeAlternatingHom I.val) s)*t*
      (B.tangentSign (by omega) k p u h d (z+tangentOffset a d w) true
        (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  have hz' := (tangentAllowed_iff a r d z L V (ordinary (0:CutRing))).mpr
    (by simpa only [map_zero,mul_zero,add_zero] using hz)
  have hw' := (tangentAllowed_iff a r d z L V (ordinary w)).mpr
    (by simpa only [pointCoordinate_add,map_add,tangentOffset_coordinate] using hzw)
  have hpath := tangentInterval_connected u v huv _ _
    (tangentAllowed_wide a r u hr.1 d z L V c hshort hnear) 0 w hz' hw'
  have hsteps (e : Fin 5) (j : Fin 2) :
      |ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j)| ≤ 2*ordinary r := by
    have hh := (tangentOffset_ordinary_bound a d (signedShortSteps u e) j).trans
      (mul_le_mul_of_nonneg_left (signedShortSteps_bound u e) (by positivity : 0 ≤ 1+|ordinary (cutTau^a)|))
    nlinarith [hr.1]
  have heq := B.tangent_interval_action hlarge hr g k p u h d hsteps (hlabels d) z L V hLV
    (tangentAllowedLower a r d z V) (tangentAllowedUpper a r d z L) 0 w hpath
    (fun t h1 h2 j => by
      have hh := (tangentAllowed_iff a r d z L V (ordinary t)).mp ⟨h1,h2⟩ j
      simpa only [pointCoordinate_add,map_add,tangentOffset_coordinate] using hh)
    n q hW f hf hc I s t ht
  simpa only [tangentOffset_zero,add_zero] using heq

end InitialCoverSystem
end ClippedLineSlideAction

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_LocalChartDecisions
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section LineParameters

theorem slope_same_intercept (a : ℕ) (d : Fin 2) (z z' : CutRing × CutRing)
    (h : integralCutForm a (slopeDirection d) z = integralCutForm a (slopeDirection d) z') :
    ∃ w : CutRing, z'=z+tangentOffset a d w := by
  fin_cases d
  · refine ⟨z'.1-z.1,?_⟩
    change z.2-cutTau^a*z.1=z'.2-cutTau^a*z'.1 at h
    apply Prod.ext
    · simp [tangentOffset]
    · simp [tangentOffset]
      linear_combination -h
  · refine ⟨z'.2-z.2,?_⟩
    change z.1-cutTau^a*z.2=z'.1-cutTau^a*z'.2 at h
    apply Prod.ext
    · simp [tangentOffset]
      linear_combination -h
    · simp [tangentOffset]

theorem real_slope_parameter (a : ℕ) (d : Fin 2) (u : CutRing × CutRing) (z : ℝ × ℝ)
    (h : cutForm a (slopeDirection d) z=ordinary (integralCutForm a (slopeDirection d) u)) :
    ∃ c : ℝ, ∀ j : Fin 2,
      realCoordinate z j=ordinary (pointCoordinate u j)+tangentCoefficient a d j*c := by
  fin_cases d
  · refine ⟨z.1-ordinary u.1,?_⟩
    change z.2-Real.goldenRatio^a*z.1=ordinary (u.2-cutTau^a*u.1) at h
    simp only [map_sub,map_mul,map_pow,ordinary_cutTau] at h
    intro j; fin_cases j
    · simp [realCoordinate,pointCoordinate,tangentCoefficient,tangentOffset]
    · simp [realCoordinate,pointCoordinate,tangentCoefficient,tangentOffset]
      linear_combination h
  · refine ⟨z.2-ordinary u.2,?_⟩
    change z.1-Real.goldenRatio^a*z.2=ordinary (u.1-cutTau^a*u.2) at h
    simp only [map_sub,map_mul,map_pow,ordinary_cutTau] at h
    intro j; fin_cases j
    · simp [realCoordinate,pointCoordinate,tangentCoefficient,tangentOffset]
      linear_combination h
    · simp [realCoordinate,pointCoordinate,tangentCoefficient,tangentOffset]

end LineParameters

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_RectangularAtlas
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.BankEmbedding.instCoeFunForallPointTrackPoint _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PolygonPlacement.Configuration.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PolygonPlacement.instCoeFunForallGenericSquareTrackPoint _root_.OAI.SimpleAmenable.PolygonPlacement.instMulActionSubtypePermTrackPointMemSubgroupPolygonFullGroup _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section RectangularAtlas
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

namespace RectangularAtlas
variable {B} (A : B.RectangularAtlas)

theorem slope_line_action_oai (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (d : Fin 2) (z z' : CutRing × CutRing)
    (hline : integralCutForm a (slopeDirection d) z=integralCutForm a (slopeDirection d) z')
    (L V : Fin 2 → CutRing) (hLV : ∀ j, ordinary (L j) ≤ ordinary (V j))
    (hz : ∀ j, -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate z j) ∧
      ordinary (V j)-ordinary (pointCoordinate z j) ≤ ordinary r)
    (hz' : ∀ j, -ordinary r ≤ ordinary (L j)-ordinary (pointCoordinate z' j) ∧
      ordinary (V j)-ordinary (pointCoordinate z' j) ≤ ordinary r)
    (x : ℝ × ℝ) (hx : cutForm a (slopeDirection d) x=ordinary (integralCutForm a (slopeDirection d) z))
    (hnear : ∀ j, |ordinary (L j)-realCoordinate x j| ≤ ordinary r/4 ∧
      |ordinary (V j)-realCoordinate x j| ≤ ordinary r/4)
    (n : ℕ) (q : Fin 2 → ℤ)
    (hW : ResolvedBy (fun i => (primitiveTests (a := a) (r := r)
      (coordinateWindowPrimitives n q) i).val) (coordinateRectangle a L V).val)
    (f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm))
    (hf : B.AlignedSmallSupported f)
    (hc : SmallControlled B.c f (B.windowSector (by omega) n (A.rectangles n) q (coordinateRectangle a L V)))
    (I : ControlAlphabet (Fin (m+1))) (s : UniversalExtension (alternatingGroup I.val))
    (t : BoundedRelationCover M (alternatingGenerator a r m hm)) (ht : t ∈ f.range) :
    A.slope (by omega) d z (universalMap (subtypeAlternatingHom I.val) s)*t*
      (A.slope (by omega) d z (universalMap (subtypeAlternatingHom I.val) s))⁻¹ =
    A.slope (by omega) d z' (universalMap (subtypeAlternatingHom I.val) s)*t*
      (A.slope (by omega) d z' (universalMap (subtypeAlternatingHom I.val) s))⁻¹ := by
  obtain ⟨w,rfl⟩ := slope_same_intercept a d z z' hline
  obtain ⟨c,hc'⟩ := real_slope_parameter a d z x hx
  exact B.tangent_line_slide hlarge hr A.rectangles A.k A.p A.u A.v A.inverse A.charts A.short
    A.labels d z w L V hLV hz hz' c (by simpa only [← hc'] using hnear) n q hW f hf hc I s t ht

end RectangularAtlas
end InitialCoverSystem

end RectangularAtlas

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.slope_line_action_oai := @OAI.SimpleAmenable.InitialCoverSystem.RectangularAtlas.slope_line_action_oai
