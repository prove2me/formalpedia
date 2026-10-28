-- Prove2me | solution 1 for OAI.SimpleAmenable.InitialCoverSystem.tangent_transport_uniform_cover_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:04:26.213004+00:00
-- url     : https://prove2.me/submissions/17e585c6-7359-42a0-9ffb-b80e0874eac6

import Mathlib
import Definitions.Def_OAIQ65Sa010
import Definitions.Def_OAIQ65Sa011
import Theorems.Thm_OAI_SimpleAmenable_InitialCoverSystem_tangent_chart_chain_control_cover_uniform

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_PropagationArithmetic
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section PropagationArithmetic

theorem endpointLabel_mul (l d : CutRing) :
    (endpointLabel (l*d) : ℝ) = conjugate l * (endpointLabel d : ℝ) +
      (endpointLabel l : ℝ) * ordinary d := by
  simp only [endpointLabel, QuadraticAlgebra.im_mul, Int.cast_add, Int.cast_mul,
    Int.cast_one, ordinary_apply, conjugate_apply]
  rw [← Real.one_sub_goldenConj]
  ring

theorem endpointLabel_mul_bound (l d : CutRing) {N D : ℝ}
    (hq : |(endpointLabel d : ℝ)| ≤ N) (hd : |ordinary d| ≤ D) :
    |(endpointLabel (l*d) : ℝ)| ≤ |conjugate l| * N + |(endpointLabel l : ℝ)| * D := by
  rw [endpointLabel_mul]
  calc
    _ ≤ |conjugate l * (endpointLabel d : ℝ)| +
        |(endpointLabel l : ℝ) * ordinary d| := abs_add_le _ _
    _ = |conjugate l| * |(endpointLabel d : ℝ)| +
        |(endpointLabel l : ℝ)| * |ordinary d| := by rw [abs_mul, abs_mul]
    _ ≤ _ := by gcongr

end PropagationArithmetic

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
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_UniformPropagationBounds
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.TranslationFiltered.regular_filtered
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
section UniformPropagationBounds

theorem conjugate_eq_label (z : CutRing) :
    conjugate z = ordinary z - (endpointLabel z : ℝ) * Real.sqrt 5 := by
  have h := (eq_div_iff (by positivity : Real.sqrt 5 ≠ 0)).mp (endpointLabel_embedding z)
  linarith

theorem tangent_displacement_embeddings (d : CutRing) {A B : ℝ}
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (n : ℕ) (hn : 1 ≤ n)
    (hd : |ordinary d| ≤ A/(n:ℝ))
    (hq : |(endpointLabel d : ℝ)| ≤ B*(n:ℝ)) :
    |ordinary d| + |conjugate d| ≤ (2*A+3*B)*(n:ℝ) := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hdn : |ordinary d| ≤ A*(n:ℝ) := by
    calc
      _ ≤ A/(n:ℝ) := hd
      _ ≤ A := div_le_self hA hn1
      _ ≤ A*(n:ℝ) := le_mul_of_one_le_right hA hn1
  have hs : Real.sqrt 5 ≤ 3 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]
  have hc : |conjugate d| ≤ A*(n:ℝ)+3*B*(n:ℝ) := by
    rw [conjugate_eq_label]
    calc
      _ ≤ |ordinary d| + |(endpointLabel d : ℝ) * Real.sqrt 5| := abs_sub _ _
      _ = |ordinary d| + |(endpointLabel d : ℝ)| * Real.sqrt 5 := by
        rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg 5)]
      _ ≤ A*(n:ℝ) + (B*(n:ℝ))*3 := by gcongr
      _ = _ := by ring
  linarith

theorem tangent_chain_uniform (l u v : CutRing) (huv : u*v = 1)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → ∀ d : CutRing,
      |ordinary d| ≤ A/(n:ℝ) → |(endpointLabel d : ℝ)| ≤ B*(n:ℝ) →
      ∃ w : List CutRing,
        w.sum = d ∧
        (∀ e ∈ w, e = u ∨ e = -u ∨ e = cutTau*u ∨ e = -(cutTau*u)) ∧
        (w.length : ℝ) ≤ K*(n:ℝ) ∧
        (∀ k : ℕ, |ordinary (w.take k).sum| ≤
          A/(n:ℝ)+(|ordinary u|+|ordinary (cutTau*u)|)) ∧
        ∀ k : ℕ, |(endpointLabel (w.take k).sum : ℝ)| +
          |(endpointLabel (l*(w.take k).sum) : ℝ)| ≤ K*(n:ℝ) := by
  let M := 4*(|ordinary v|+|conjugate v|+1)
  let L := M*(2*A+3*B)
  let H := |(endpointLabel u : ℝ)|+|(endpointLabel (cutTau*u) : ℝ)|
  let σ := |ordinary u|+|ordinary (cutTau*u)|
  let J := L*H + |conjugate l| *(L*H) + |(endpointLabel l : ℝ)| *(A+σ)
  let K := L+J+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hL : 0 ≤ L := mul_nonneg hM (by positivity)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hσ : 0 ≤ σ := by dsimp [σ]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨K,by dsimp [K]; positivity,fun n hn d hd hq => ?_⟩
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) ≤ n := by positivity
  have he := tangent_displacement_embeddings d hA hB n hn hd hq
  obtain ⟨w,hw,hm,hlen,hwalk,hlab⟩ := tangent_chain u v huv d
  have hsize : M*(|ordinary d|+|conjugate d|) ≤ L*(n:ℝ) := by
    calc
      _ ≤ M*((2*A+3*B)*(n:ℝ)) := mul_le_mul_of_nonneg_left he hM
      _ = _ := by dsimp [L]; ring
  have hkL : L ≤ K := by dsimp [K]; linarith
  have hkJ : J ≤ K := by dsimp [K]; linarith
  have ho : ∀ k : ℕ, |ordinary (w.take k).sum| ≤ A/(n:ℝ)+σ := by
    intro k
    have hb := hwalk k
    have hleft : -|ordinary d| ≤ min 0 (ordinary d) :=
      le_min (by linarith [abs_nonneg (ordinary d)]) (neg_abs_le _)
    have hright : max 0 (ordinary d) ≤ |ordinary d| :=
      max_le (abs_nonneg _) (le_abs_self _)
    apply abs_le.mpr
    constructor <;> linarith [hd]
  refine ⟨w,hw,hm,(hlen.trans hsize).trans (mul_le_mul_of_nonneg_right hkL hn0),ho,?_⟩
  intro k
  have hx : |(endpointLabel (w.take k).sum : ℝ)| ≤ (L*H)*(n:ℝ) := by
    calc
      _ ≤ (M*(|ordinary d|+|conjugate d|))*H := hlab k
      _ ≤ (L*(n:ℝ))*H := mul_le_mul_of_nonneg_right hsize hH
      _ = _ := by ring
  have ho' : |ordinary (w.take k).sum| ≤ (A+σ)*(n:ℝ) := by
    calc
      _ ≤ A/(n:ℝ)+σ := ho k
      _ ≤ A+σ := add_le_add (div_le_self hA hn1) le_rfl
      _ ≤ (A+σ)*(n:ℝ) := le_mul_of_one_le_right (add_nonneg hA hσ) hn1
  have hy := endpointLabel_mul_bound l (w.take k).sum hx ho'
  calc
    _ ≤ (L*H)*(n:ℝ) +
        (|conjugate l| *((L*H)*(n:ℝ)) + |(endpointLabel l : ℝ)| *((A+σ)*(n:ℝ))) :=
      add_le_add hx hy
    _ = J*(n:ℝ) := by dsimp [J]; ring
    _ ≤ K*(n:ℝ) := mul_le_mul_of_nonneg_right hkJ hn0

end UniformPropagationBounds

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TangentWalkCenters
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

theorem tangentOffset_label_bound (a : ℕ) (d : Fin 2) (w : CutRing) (j : Fin 2) :
    |(pointLabel (tangentOffset a d w) j : ℝ)| ≤
      |(endpointLabel w : ℝ)|+|(endpointLabel (cutTau^a*w) : ℝ)| := by
  have h0 := abs_nonneg (endpointLabel w : ℝ)
  have h1 := abs_nonneg (endpointLabel (cutTau^a*w) : ℝ)
  fin_cases d <;> fin_cases j
  · exact le_add_of_nonneg_right h1
  · exact le_add_of_nonneg_left h0
  · exact le_add_of_nonneg_left h0
  · exact le_add_of_nonneg_right h1

theorem tangent_centers_uniform (a : ℕ) (u v : CutRing) (huv : u*v=1)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → ∀ w : CutRing,
      |ordinary w| ≤ A/(n:ℝ) → |(endpointLabel w : ℝ)| ≤ B*(n:ℝ) →
      ∀ (d : Fin 2) (z₀ : CutRing × CutRing),
      ∃ (T : ℕ) (z : ℕ → CutRing × CutRing) (e : ℕ → Fin 5),
        z 0 = z₀ ∧ z T = z₀+tangentOffset a d w ∧
        (∀ i, i < T → z (i+1) = z i+tangentOffset a d (signedShortSteps u (e i))) ∧
        (∀ i j, |ordinary (pointCoordinate (z i-z₀) j)| ≤
          (1+|ordinary (cutTau^a)|)*(A/(n:ℝ)+(|ordinary u|+|ordinary (cutTau*u)|))) ∧
        (∀ i j, |(pointLabel (z i-z₀) j : ℝ)| ≤ K*(n:ℝ)) := by
  obtain ⟨K,hK,hwalk⟩ := tangent_chain_uniform (cutTau^a) u v huv hA hB
  refine ⟨K,hK,fun n hn w hw hw' d z₀ => ?_⟩
  obtain ⟨xs,hxs,hm,_hlen,ho,hq⟩ := hwalk n hn w hw hw'
  have he : ∀ i : ℕ, ∃ e : Fin 5, ∀ hi : i < xs.length, xs[i]'hi = signedShortSteps u e := by
    intro i
    by_cases hi : i < xs.length
    · obtain hh | hh | hh | hh := hm xs[i] (List.getElem_mem hi)
      · exact ⟨1,fun _ => by simpa [signedShortSteps] using hh⟩
      · exact ⟨2,fun _ => by simpa [signedShortSteps] using hh⟩
      · exact ⟨3,fun _ => by simpa [signedShortSteps] using hh⟩
      · exact ⟨4,fun _ => by simpa [signedShortSteps] using hh⟩
    · exact ⟨0,fun h => (hi h).elim⟩
  choose e he using he
  let z := fun i => z₀+tangentOffset a d (xs.take i).sum
  refine ⟨xs.length,z,e,?_,?_,?_,?_,?_⟩
  · simp [z]
  · simp [z,hxs]
  · intro i hi
    have hs : (xs.take (i+1)).sum = (xs.take i).sum+xs[i] := by
      rw [List.take_add_one]
      simp only [List.getElem?_eq_getElem hi,Option.toList_some,List.sum_append,List.sum_singleton]
    dsimp [z]
    rw [hs,he i hi,tangentOffset_add,add_assoc]
  · intro i j
    have hh := tangentOffset_ordinary_bound a d (xs.take i).sum j
    have hh' := mul_le_mul_of_nonneg_left (ho i) (by positivity : 0 ≤ 1+|ordinary (cutTau^a)|)
    simpa only [z,add_sub_cancel_left] using hh.trans hh'
  · intro i j
    simpa only [z,add_sub_cancel_left] using (tangentOffset_label_bound a d (xs.take i).sum j).trans (hq i)

end TangentWalkCenters

section UniformChartGeometry

theorem uniform_tangent_chart_geometry (a : ℕ) (u v s : CutRing) (huv : u*v=1)
    (hs : 0 < ordinary s)
    (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) < ordinary s/4)
    {A B D E : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (_hD : 0 ≤ D) (hE : 0 ≤ E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∀ w : CutRing, |ordinary w| ≤ A/(n:ℝ) → |(endpointLabel w:ℝ)| ≤ B*(n:ℝ) →
      ∀ (d : Fin 2) (z₀ : CutRing × CutRing) (q p : Fin 2 → ℤ) (L V : Fin 2 → CutRing),
      (∀ j, |(pointLabel z₀ j+q j-p j:ℝ)| ≤ E*(n:ℝ)) →
      (∀ j, |ordinary (L j)-ordinary (pointCoordinate z₀ j)| ≤ D/(n:ℝ)) →
      (∀ j, |ordinary (V j)-ordinary (pointCoordinate z₀ j)| ≤ D/(n:ℝ)) →
      ∃ (T : ℕ) (z : ℕ → CutRing × CutRing) (e : ℕ → Fin 5),
        z 0 = z₀ ∧ z T = z₀+tangentOffset a d w ∧
        (∀ i, i < T → z (i+1) = z i+tangentOffset a d (signedShortSteps u (e i))) ∧
        (∀ i j, ((pointLabel (z i) j+q j-p j).natAbs:ℝ) ≤ (K+1)*(n:ℝ)) ∧
        (∀ i j, -ordinary s+ordinary (pointCoordinate (z i) j) ≤ ordinary (L j)-ordinary s/4) ∧
        (∀ i j, ordinary (V j)+ordinary s/4 ≤ ordinary s+ordinary (pointCoordinate (z i) j)) := by
  obtain ⟨K,hK,hwalk⟩ := tangent_centers_uniform a u v huv hA hB
  let H := (1+|ordinary (cutTau^a)|)*A+D
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (4*H/ordinary s))
  have hN1 : 1 ≤ N := by
    have hh := lt_of_le_of_lt (le_max_left _ _) hN
    exact_mod_cast (by linarith : (1:ℝ) ≤ N)
  refine ⟨K+E,by linarith,N,hN1,?_⟩
  intro n hn w hw hw' d z₀ q p L V hp hL hV
  have hn1 : 1 ≤ n := hN1.trans hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hn' : (N:ℝ) ≤ n := by exact_mod_cast hn
  have hbig : 4*H/ordinary s < (n:ℝ) := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hN) hn'
  have hfrac : H/(n:ℝ) < ordinary s/4 := by
    have hh := (div_lt_iff₀ hs).mp hbig
    apply (div_lt_iff₀ hn0).mpr
    nlinarith
  obtain ⟨T,z,e,hz0,hzT,hstep,ho,hq⟩ := hwalk n hn1 w hw hw' d z₀
  refine ⟨T,z,e,hz0,hzT,hstep,?_,?_,?_⟩
  · intro i j
    have he : ((pointLabel (z i) j+q j-p j:ℤ):ℝ) =
        (pointLabel (z i-z₀) j:ℝ)+(pointLabel z₀ j+q j-p j:ℝ) := by
      simp only [pointLabel_sub,Int.cast_sub,Int.cast_add]
      ring
    rw [Nat.cast_natAbs,Int.cast_abs,he]
    calc
      _ ≤ |(pointLabel (z i-z₀) j:ℝ)|+|(pointLabel z₀ j+q j-p j:ℝ)| := abs_add_le _ _
      _ ≤ K*(n:ℝ)+E*(n:ℝ) := add_le_add (hq i j) (hp j)
      _ ≤ (K+E+1)*(n:ℝ) := by nlinarith
  · intro i j
    have hz := (abs_le.mp (ho i j)).2
    have hl := (abs_le.mp (hL j)).1
    simp only [pointCoordinate_sub,map_sub] at hz
    have he : (1+|ordinary (cutTau^a)|)*(A/(n:ℝ)+(|ordinary u|+|ordinary (cutTau*u)|))+D/(n:ℝ) =
        H/(n:ℝ)+(1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) := by
      dsimp [H]
      ring
    linarith
  · intro i j
    have hz := (abs_le.mp (ho i j)).1
    have hv := (abs_le.mp (hV j)).2
    simp only [pointCoordinate_sub,map_sub] at hz
    have he : (1+|ordinary (cutTau^a)|)*(A/(n:ℝ)+(|ordinary u|+|ordinary (cutTau*u)|))+D/(n:ℝ) =
        H/(n:ℝ)+(1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) := by
      dsimp [H]
      ring
    linarith

end UniformChartGeometry

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Configurations_SymmetricCharts
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

theorem symmetricWindow_labels (s : CutRing) (j : Fin 2) :
    (symmetricWindowStart s j ≤ endpointLabel (-s) ∧
      endpointLabel (-s) < symmetricWindowStart s j+symmetricWindowLength s) ∧
    (symmetricWindowStart s j ≤ endpointLabel 0 ∧
      endpointLabel 0 < symmetricWindowStart s j+symmetricWindowLength s) ∧
    (symmetricWindowStart s j ≤ endpointLabel s ∧
      endpointLabel s < symmetricWindowStart s j+symmetricWindowLength s) := by
  have h₀ := Int.le_natAbs (a := endpointLabel s)
  have h₁ : -(endpointLabel s) ≤ ((endpointLabel s).natAbs:ℤ) := by
    simpa using (Int.le_natAbs (a := -endpointLabel s))
  simp only [symmetricWindowStart,symmetricWindowLength,endpointLabel_neg,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  change _ ∧ (_ ≤ (0:ℤ) ∧ (0:ℤ) < _) ∧ _
  omega

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

theorem symmetric_chart_overlap_boxes (a : ℕ) (r s u : CutRing)
    (hs : 0 < ordinary s) (hsr : ordinary s < ordinary r/2)
    (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) < ordinary s/4)
    (d : Fin 2) (e : Fin 5) (j : Fin 2) :
    (-ordinary r < ordinary (-s) ∧ ordinary s < ordinary r) ∧
    (-ordinary r < ordinary (-s)-ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) ∧
      ordinary s-ordinary (pointCoordinate (tangentOffset a d (signedShortSteps u e)) j) < ordinary r) := by
  have hh := (tangentOffset_ordinary_bound a d (signedShortSteps u e) j).trans
    (mul_le_mul_of_nonneg_left (signedShortSteps_bound u e) (by positivity : 0 ≤ 1+|ordinary (cutTau^a)|))
  have hh' := lt_of_le_of_lt hh hshort
  have hlim := abs_lt.mp hh'
  rw [map_neg]
  exact ⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩

end SymmetricCharts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_CentralCovers_CoverUniformBridges
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section CoverUniformBridges
namespace InitialCoverSystem
variable {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

theorem tangent_transport_uniform_cover_uniform_oai (hlarge : 20 ≤ m+1)
    (hr : 0 < ordinary r ∧ ordinary r < 1/2)
    (s u v : CutRing) (hs : 0 < ordinary s) (hsr : ordinary s < ordinary r/2)
    (huv : u*v=1)
    (hshort : (1+|ordinary (cutTau^a)|)*(|ordinary u|+|ordinary (cutTau*u)|) < ordinary s/4)
    {A C D E : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D) (hE : 0 ≤ E) :
    ∃ N : ℕ, 160 ≤ N ∧ ∀ (M : ℕ) (B : InitialCoverSystem a r m hm M)
      (h : B.TangentChartLaws (symmetricWindowLength s) (symmetricWindowStart s) u), ∀ n : ℕ, N ≤ n → ∀ g : B.CoordinateWindowLaw n,
      ∀ (t : Fin 2 → ℕ) (ht : ∀ j, t j ≤ n) (p : Fin 2 → ℤ) (L V : Fin 2 → CutRing),
      (∀ j, ordinary (L j) ≤ ordinary (V j)) →
      (∀ j, p j ≤ endpointLabel (L j) ∧ endpointLabel (L j) < p j+t j) →
      (∀ j, p j ≤ endpointLabel (V j) ∧ endpointLabel (V j) < p j+t j) →
      ∀ w : CutRing, |ordinary w| ≤ A/(n:ℝ) → |(endpointLabel w:ℝ)| ≤ C*(n:ℝ) →
      ∀ (d : Fin 2) (z₀ : CutRing × CutRing),
      (∀ j, |(pointLabel z₀ j+symmetricWindowStart s j-p j:ℝ)| ≤ E*(n:ℝ)) →
      (∀ j, |ordinary (L j)-ordinary (pointCoordinate z₀ j)| ≤ D/(n:ℝ)) →
      (∀ j, |ordinary (V j)-ordinary (pointCoordinate z₀ j)| ≤ D/(n:ℝ)) →
      ∀ f : TrackStar (Fin (m+1)) →* BoundedRelationCover M (alternatingGenerator a r m hm),
      B.AlignedSmallSupported f →
      (∀ j, SmallControlled B.c f
        (B.axisSector (by omega) n g j (t j) (ht j) (p j) (coordinateInterval a j (L j) (V j)))) →
      SmallControlled B.c f (B.tangentSign (by omega) (symmetricWindowLength s)
        (symmetricWindowStart s) u h d z₀ true) →
      SmallControlled B.c f (B.tangentSign (by omega) (symmetricWindowLength s)
        (symmetricWindowStart s) u h d (z₀+tangentOffset a d w) true) := by
  obtain ⟨K,hK,N₁,hN₁,hgeo⟩ := uniform_tangent_chart_geometry a u v s huv hs hshort hA hC hD hE
  have hl := fun j => (symmetricWindow_labels s j).1
  have hv := fun j => (symmetricWindow_labels s j).2.2
  have hlen : ∀ _ : Fin 2, ordinary s-ordinary (-s) < 1 := by
    intro j
    rw [map_neg]
    linarith [hr.2]
  have hbox (j : Fin 2) : -ordinary r < ordinary (-s) ∧ ordinary s < ordinary r := by
    rw [map_neg]
    constructor <;> linarith [hr.1]
  obtain ⟨N₂,hN₂,hchain⟩ := tangent_chart_chain_control_cover_uniform (m := m) (r := r) (hm := hm) hlarge hr hK
    (by linarith : 0 < ordinary s/4) (symmetricWindowLength s) (symmetricWindowStart s) u
    (fun _ => -s) (fun _ => s) hl hv (fun _ => by rw [map_neg]; linarith) hlen hbox
    (fun d e j => (symmetric_chart_overlap_boxes a r s u hs hsr hshort d e j).2)
  refine ⟨max N₁ N₂,hN₂.trans (le_max_right _ _),?_⟩
  intro M B h n hn g t ht p L V hLV hL hV w hw hw' d z₀ hp hLo hVo f hf hc hstart
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_right _ _).trans hn
  obtain ⟨T,z,e,hz0,hzT,hstep,hpq,hlo,hup⟩ := hgeo n hn₁ w hw hw' d z₀
    (symmetricWindowStart s) p L V hp hLo hVo
  have hh := hchain M B h n hn₂ g t ht p L V hLV hL hV d T z e hstep
    (fun i _ => hpq i) (fun i _ => by simpa only [map_neg] using hlo i)
    (fun i _ => hup i) f hf hc (by simpa only [hz0] using hstart)
  simpa only [hzT] using hh

end InitialCoverSystem
end CoverUniformBridges

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.InitialCoverSystem.tangent_transport_uniform_cover_uniform_oai := @OAI.SimpleAmenable.InitialCoverSystem.tangent_transport_uniform_cover_uniform_oai
