-- Prove2me | solution 1 for OAI.AllLatticeExclusion.no_cover
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T14:47:32.786733+00:00
-- url     : https://prove2.me/submissions/d11f1ef3-34c3-44ac-981e-d46dad91bc97

import Mathlib
import Definitions.Def_OAIQ16Cd000
import Definitions.Def_OAIQ16Cd001
import Theorems.Thm_OAI_LocalizationComplete_localize

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_LatticeAveraging
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace LatticeAveraging
open Set MeasureTheory
open scoped ENNReal BigOperators Pointwise

lemma measurable_field {n : ℕ} {I : Type u_2} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ]
    (p : I → Space n) {f : Space n → ℝ≥0∞} (hf : Measurable f) :
    Measurable (field Λ p f) := by
  let : Countable Λ := countable_of_Lindelof_of_discrete
  apply Finset.measurable_sum
  intro i _
  exact Measurable.tsum fun l => hf.comp ((measurable_id.sub_const _).sub_const _)

lemma one_coset {n : ℕ} (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ]
    {F : Set (Space n)} (hF : IsAddFundamentalDomain Λ F volume)
    (p : Space n) {f : Space n → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y in F,∑' l : Λ,f (y-p-l.val) = ∫⁻ x,f x := by
  let : Countable Λ := countable_of_Lindelof_of_discrete
  rw [lintegral_tsum (f := fun l : Λ => fun y => f (y-p-l.val))
    (fun l => (hf.comp ((measurable_id.sub_const p).sub_const l.val)).aemeasurable)]
  let : VAddInvariantMeasure Λ (Space n) volume :=
    inferInstanceAs (VAddInvariantMeasure Λ.toAddSubgroup (Space n) volume)
  have heq := hF.lintegral_eq_tsum' (fun x => f (x-p))
  rw [lintegral_sub_right_eq_self] at heq
  apply Eq.trans _ heq.symm
  apply tsum_congr
  intro l
  congr 1
  funext y
  congr 1
  change y-p-l.val = -l.val+y-p
  abel

lemma averaging {n : ℕ} {I : Type u_3} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ]
    {F : Set (Space n)} (hF : IsAddFundamentalDomain Λ F volume)
    (p : I → Space n) {f : Space n → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y in F,field Λ p f y = (Fintype.card I:ℝ≥0∞)*∫⁻ x,f x := by
  let : Countable Λ := countable_of_Lindelof_of_discrete
  unfold field
  rw [lintegral_finsetSum (f := fun i : I => fun y => ∑' l : Λ, f (y-p i-l.val))
    Finset.univ (fun i _ => Measurable.tsum
    fun l => hf.comp ((measurable_id.sub_const (p i)).sub_const l.val))]
  simp_rw [one_coset Λ hF _ hf]
  simp

lemma normalized_averaging {n : ℕ} {I : Type u_5} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {F : Set (Space n)} (hF : IsAddFundamentalDomain Λ F volume)
    (p : I → Space n) {f : Space n → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y,field Λ p f y ∂uniformWindow F =
      ((Fintype.card I:ℝ≥0∞)/volume F)*∫⁻ x,f x := by
  rw [uniformWindow,lintegral_smul_measure,averaging Λ hF p hf]
  simp only [div_eq_mul_inv]
  ac_rfl

lemma probability_window {n : ℕ} {F : Set (Space n)}
    (hF0 : volume F ≠ 0) (hFtop : volume F ≠ ∞) :
    IsProbabilityMeasure (uniformWindow F) := by
  constructor
  rw [uniformWindow,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hF0 hFtop

end LatticeAveraging

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_LocalizationRounding
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal

namespace LocalizationRounding
open Set Finset
open scoped BigOperators

lemma latticePoint_mem_box {n : ℕ} {h L : ℝ} (hh : 0 < h) (z : Fin n → ℤ)
    (hz : ‖latticePoint h z‖ ≤ L) : z ∈ integerBox n ⌊L/h⌋ := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro i
  have hcoord : h*|(z i:ℝ)| ≤ L := by
    have hp := (PiLp.norm_apply_le (latticePoint h z) i).trans hz
    simpa [latticePoint,Real.norm_eq_abs,abs_mul,abs_of_pos hh] using hp
  have hab : |(z i:ℝ)| ≤ L/h := (le_div_iff₀ hh).mpr (by linarith only [hcoord])
  have hu : z i ≤ ⌊L/h⌋ := Int.le_floor.mpr ((le_abs_self _).trans hab)
  have hl : -(z i) ≤ ⌊L/h⌋ := Int.le_floor.mpr (by
    push_cast
    exact (neg_le_abs _).trans hab)
  exact Finset.mem_Icc.mpr ⟨by linarith only [hl],hu⟩

lemma mem_alphabet {n : ℕ} {h L : ℝ} (hh : 0 < h) (x : Space n) :
    x ∈ alphabet n h L ↔ (∃ z : Fin n → ℤ,x = latticePoint h z) ∧ ‖x‖ ≤ L := by
  classical
  constructor
  · intro hx
    obtain ⟨hm,hL⟩ := Finset.mem_filter.mp hx
    obtain ⟨z,_,hz⟩ := Finset.mem_image.mp hm
    exact ⟨⟨z,hz.symm⟩,hL⟩
  · rintro ⟨⟨z,rfl⟩,hz⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨z,latticePoint_mem_box hh z hz,rfl⟩,hz⟩

end LocalizationRounding

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_LocalizationGood
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace LocalizationGood
open Set MeasureTheory Metric LatticeAveraging
open scoped BigOperators ENNReal

lemma measurable_weightedFn {n : ℕ} (a β : ℝ) : Measurable (weightedFn (n := n) a β) := by
  apply Measurable.indicator _ measurableSet_closedBall
  apply Measurable.ennreal_ofReal
  exact (continuous_const.add (continuous_const.mul
    ((continuous_const.sub (continuous_norm.pow 2 |>.div_const (a^2))).max continuous_const))).measurable

lemma term_le_field {n : ℕ} {I : Type u_1} [Fintype I] (Λ : Submodule ℤ (Space n))
    (p : I → Space n) (f : Space n → ℝ≥0∞) (y : Space n) (i : I) (l : Λ) :
    f (y-p i-l.val) ≤ field Λ p f y := by
  calc
    _ ≤ ∑' l : Λ,f (y-p i-l.val) := ENNReal.le_tsum l
    _ ≤ ∑ j,∑' l : Λ,f (y-p j-l.val) := Finset.single_le_sum (f := fun j : I => ∑' l : Λ,f (y-p j-l.val)) (fun _ _ => bot_le) (Finset.mem_univ i)

lemma inner_zero {n : ℕ} {I : Type u_2} [Fintype I] (Λ : Submodule ℤ (Space n))
    (p : I → Space n) (r : ℝ) (y : Space n) :
    field Λ p (countFn (ball (0 : Space n) r)) y = 0 ↔ ∀ (i : I) (l : Λ),r ≤ ‖y-p i-l.val‖ := by
  constructor
  · intro h i l
    by_contra hr
    have hmem : y-p i-l.val ∈ ball (0 : Space n) r := by simpa using lt_of_not_ge hr
    have hh := term_le_field Λ p (countFn (ball (0 : Space n) r)) y i l
    have he : countFn (ball (0 : Space n) r) (y-p i-l.val) = 1 := by simp [countFn,hmem]
    rw [he,h] at hh
    exact (by norm_num at hh)
  · intro h
    unfold field
    apply Finset.sum_eq_zero
    intro i _
    apply ENNReal.tsum_eq_zero.mpr
    intro l
    have hnot : y-p i-l.val ∉ ball (0 : Space n) r := by simpa using not_lt.mpr (h i l)
    simp [countFn,hnot]

lemma bad_bound {n : ℕ} {I : Type u_6} [Fintype I] (Λ : Submodule ℤ (Space n))
    [DiscreteTopology Λ] (p : I → Space n) (a r β : ℝ) (C : ℝ≥0∞)
    (hC : C ≠ 0) (hCtop : C ≠ ∞) (P : Measure (Space n)) [IsProbabilityMeasure P]
    (hinner : ∫⁻ y,field Λ p (countFn (ball (0 : Space n) r)) y ∂P ≤ 1/200)
    (houter : ∫⁻ y,field Λ p (countFn (closedBall (0 : Space n) β)) y ∂P ≤ C*(3/2000))
    (hweight : ∫⁻ y,field Λ p (weightedFn a β) y ∂P ≤ C*(5/2000)) :
    P (good Λ p a r β C)ᶜ ≤ 1/100 := by
  let A := field Λ p (countFn (ball (0 : Space n) r))
  let B := field Λ p (countFn (closedBall (0 : Space n) β))
  let W := field Λ p (weightedFn a β)
  have hA : Measurable A := measurable_field Λ p (measurable_const.indicator measurableSet_ball)
  have hB : Measurable B := measurable_field Λ p (measurable_const.indicator measurableSet_closedBall)
  have hW : Measurable W := measurable_field Λ p (measurable_weightedFn a β)
  have hsub : (good Λ p a r β C)ᶜ ⊆ {y | 1 ≤ A y} ∪ {y | C ≤ B y} ∪ {y | C ≤ W y} := by
    intro y hy
    by_cases hb : B y ≤ C
    · by_cases hw : W y ≤ C
      · have ha : A y ≠ 0 := fun hz => hy ⟨hz,hb,hw⟩
        have hnot : ¬∀ (i : I) (l : Λ),r ≤ ‖y-p i-l.val‖ := by
          intro hall; exact ha ((inner_zero Λ p r y).mpr hall)
        push Not at hnot
        obtain ⟨i,l,hl⟩ := hnot
        have hm : y-p i-l.val ∈ ball (0 : Space n) r := by simpa using hl
        have he := term_le_field Λ p (countFn (ball (0 : Space n) r)) y i l
        exact Or.inl (Or.inl (by
          change 1 ≤ field Λ p (countFn (ball (0 : Space n) r)) y
          convert he using 1
          all_goals try with_reducible_and_instances rfl
          simp [countFn,hm]))
      · exact Or.inr (le_of_not_ge hw)
    · exact Or.inl (Or.inr (le_of_not_ge hb))
  have ha := meas_ge_le_lintegral_div (μ := P) hA.aemeasurable (by norm_num : (1:ℝ≥0∞) ≠ 0) (by norm_num : (1:ℝ≥0∞) ≠ ∞)
  have hb := meas_ge_le_lintegral_div (μ := P) hB.aemeasurable hC hCtop
  have hw := meas_ge_le_lintegral_div (μ := P) hW.aemeasurable hC hCtop
  have hbb : P {y | C ≤ B y} ≤ 3/2000 := by
    apply hb.trans
    apply (ENNReal.div_le_div_right houter C).trans_eq
    rw [mul_comm,ENNReal.mul_div_cancel_right hC hCtop]
  have hww : P {y | C ≤ W y} ≤ 5/2000 := by
    apply hw.trans
    apply (ENNReal.div_le_div_right hweight C).trans_eq
    rw [mul_comm,ENNReal.mul_div_cancel_right hC hCtop]
  have haa : P {y | 1 ≤ A y} ≤ 1/200 := by simpa using ha.trans (ENNReal.div_le_div_right hinner 1)
  calc
    _ ≤ P ({y | 1 ≤ A y} ∪ {y | C ≤ B y} ∪ {y | C ≤ W y}) := measure_mono hsub
    _ ≤ (P {y | 1 ≤ A y}+P {y | C ≤ B y})+P {y | C ≤ W y} :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ (1/200+3/2000)+5/2000 := add_le_add (add_le_add haa hbb) hww
    _ ≤ 1/100 := by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness),ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num [ENNReal.toReal_div]

end LocalizationGood

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_RandomBody
attribute [-instance] _root_.OAI.CapCost.intensity_finite _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3

namespace RandomBody
open Set MeasureTheory Metric SphericalLaw
open scoped ENNReal NNReal

lemma body_closed {n : ℕ} (b t : ℝ) (U : PoissonConfig.Config (Sphere n)) :
    IsClosed (body b t U) := by
  apply isClosed_closedBall.inter
  exact isClosed_iInter fun i => isClosed_le ((continuous_const.inner continuous_id).abs) continuous_const

lemma body_compact {n : ℕ} (b t : ℝ) (U : PoissonConfig.Config (Sphere n)) :
    IsCompact (body b t U) :=
  (isCompact_closedBall (0 : Space n) b).of_isClosed_subset (body_closed b t U) inter_subset_left

end RandomBody

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_RadialIntegral
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace RadialIntegral
open Set MeasureTheory Metric
open scoped ENNReal

lemma deficit_indicator {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) :
    max (1-r^2/a^2) 0 = (Iio a).indicator (fun t : ℝ => 1-t^2/a^2) r := by
  by_cases h : r < a
  · rw [indicator_of_mem (show r ∈ Iio a from h),max_eq_left]
    apply sub_nonneg.mpr
    exact (div_le_one (sq_pos_of_pos ha)).mpr ((sq_le_sq₀ hr ha.le).mpr h.le)
  · rw [indicator_of_notMem (show r ∉ Iio a from h),max_eq_right]
    apply sub_nonpos.mpr
    exact (one_le_div (sq_pos_of_pos ha)).mpr ((sq_le_sq₀ ha.le hr).mpr (le_of_not_gt h))

lemma polynomial_integral {n : ℕ} (hn : 0 < n) {a : ℝ} (ha : 0 < a) :
    ∫ r in Ioo (0:ℝ) a,r^(n-1)*(1-r^2/a^2) = 2*a^n/((n:ℝ)*((n:ℝ)+2)) := by
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le ha.le]
  have he (r : ℝ) : r^(n-1)*(1-r^2/a^2) = r^(n-1)-r^(n+1)/a^2 := by
    rw [mul_sub,mul_one,← mul_div_assoc,← pow_add]
    rw [show n-1+2 = n+1 by omega]
  simp_rw [he]
  rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _),intervalIntegral.integral_div,
    integral_pow,integral_pow]
  have hn1 : n-1+1 = n := by omega
  rw [hn1]
  simp only [zero_pow (by omega : n ≠ 0),zero_pow (by omega : n+1+1 ≠ 0),sub_zero,
    Nat.cast_add,Nat.cast_one,Nat.cast_sub (show 1 ≤ n by omega)]
  rw [show n+1+1 = n+2 by omega,pow_add]
  have hnp : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [sub_add_cancel]
  field_simp
  ring

lemma deficit_integral {n : ℕ} [NeZero n] {a : ℝ} (ha : 0 < a) :
    ∫ x : Space n,max (1-‖x‖^2/a^2) 0 =
      2/((n:ℝ)+2)*volume.real (closedBall (0 : Space n) a) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  have : Nontrivial (Space n) := inferInstance
  have he (x : Space n) := deficit_indicator ha (norm_nonneg x)
  simp_rw [he]
  rw [integral_fun_norm_addHaar volume ((Iio a).indicator (fun r : ℝ => 1-r^2/a^2))]
  simp only [finrank_euclideanSpace, Fintype.card_fin,nsmul_eq_mul,smul_eq_mul]
  have hinside : (∫ r in Ioi (0:ℝ),r^(n-1)*(Iio a).indicator (fun t : ℝ => 1-t^2/a^2) r) =
      ∫ r in Ioo (0:ℝ) a,r^(n-1)*(1-r^2/a^2) := by
    have heq : (fun r : ℝ => r^(n-1)*(Iio a).indicator (fun t : ℝ => 1-t^2/a^2) r) =
        (Iio a).indicator (fun r : ℝ => r^(n-1)*(1-r^2/a^2)) := by
      funext r
      by_cases hr : r ∈ Iio a <;> simp [hr]
    rw [heq]
    rw [integral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
    rw [show Iio a ∩ Ioi (0:ℝ) = Ioo 0 a by ext r; exact and_comm]
  rw [hinside,polynomial_integral hn ha]
  rw [volume.addHaar_real_closedBall _ ha.le]
  simp only [finrank_euclideanSpace,Fintype.card_fin]
  field_simp

end RadialIntegral

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_WeightedVolume
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace WeightedVolume
open Set MeasureTheory Metric
open scoped ENNReal
lemma deficit_lintegral {n : ℕ} [NeZero n] {a : ℝ} (ha : 0<a) :
    ∫⁻ x : Space n,ENNReal.ofReal (max (1-‖x‖^2/a^2) 0) =
      ENNReal.ofReal (2/((n:ℝ)+2))*volume (closedBall (0:Space n) a) := by
  have hV : 0 < volume.real (closedBall (0:Space n) a) := by
    exact ENNReal.toReal_pos (measure_closedBall_pos volume (0:Space n) ha).ne'
      (isCompact_closedBall (0:Space n) a).measure_ne_top
  have hi := RadialIntegral.deficit_integral (n := n) ha
  have hint : Integrable (fun x : Space n => max (1-‖x‖^2/a^2) 0) volume :=
    Integrable.of_integral_ne_zero (by rw [hi]; positivity)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (fun x => le_max_right _ _)),hi,
    ENNReal.ofReal_mul (by positivity),Measure.real,ENNReal.ofReal_toReal (isCompact_closedBall (0:Space n) a).measure_ne_top]
lemma weighted_lintegral {n : ℕ} [NeZero n] {a β : ℝ} (ha : 0<a) :
    ∫⁻ x : Space n,LocalizationGood.weightedFn a β x ≤
      volume (closedBall (0:Space n) β)+2*volume (closedBall (0:Space n) a) := by
  let δ (x : Space n) := ENNReal.ofReal (max (1-‖x‖^2/a^2) 0)
  have hδ : Measurable δ := by dsimp [δ]; fun_prop
  have hpoint (x : Space n) : LocalizationGood.weightedFn a β x ≤
      LocalizationGood.countFn (closedBall (0:Space n) β) x+(n:ℝ≥0∞)*δ x := by
    by_cases hx : x ∈ closedBall (0:Space n) β
    · rw [LocalizationGood.weightedFn,Set.indicator_of_mem hx,
        LocalizationGood.countFn,Set.indicator_of_mem hx]
      change ENNReal.ofReal (1+(n:ℝ)*max (1-‖x‖^2/a^2) 0) ≤
        1+(n:ℝ≥0∞)*ENNReal.ofReal (max (1-‖x‖^2/a^2) 0)
      rw [ENNReal.ofReal_add (by norm_num : (0:ℝ)≤1)
        (mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (le_max_right _ _)),
        ENNReal.ofReal_one,ENNReal.ofReal_mul (Nat.cast_nonneg (α := ℝ) n),ENNReal.ofReal_natCast]
    · simp only [LocalizationGood.weightedFn,LocalizationGood.countFn,Set.indicator_of_notMem hx,zero_add]
      exact bot_le
  apply (lintegral_mono hpoint).trans
  unfold LocalizationGood.countFn
  rw [lintegral_add_left (measurable_const.indicator measurableSet_closedBall),
    lintegral_const_mul _ hδ]
  simp only [lintegral_indicator measurableSet_closedBall,lintegral_const,Measure.restrict_apply_univ,one_mul]
  change volume (closedBall (0:Space n) β)+(n:ℝ≥0∞)*(∫⁻ x : Space n,ENNReal.ofReal (max (1-‖x‖^2/a^2) 0)) ≤ _
  rw [deficit_lintegral ha]
  have hnum : (n:ℝ≥0∞)*ENNReal.ofReal (2/((n:ℝ)+2)) ≤ 2 := by
    rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg (α := ℝ) n)]
    have hh : (n:ℝ)*(2/((n:ℝ)+2)) ≤ 2 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+2)).mpr
      nlinarith only [Nat.cast_nonneg (α := ℝ) n]
    simpa using ENNReal.ofReal_le_ofReal hh
  calc
    _ = volume (closedBall (0:Space n) β)+((n:ℝ≥0∞)*ENNReal.ofReal (2/((n:ℝ)+2)))*volume (closedBall (0:Space n) a) := by rw [mul_assoc]
    _ ≤ _ := by gcongr
end WeightedVolume

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PatternEnumeration
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4

namespace PatternEnumeration
open Set Metric MeasureTheory PatternGeometry LocalizationRounding
open scoped BigOperators ENNReal Classical
lemma good_reindex {n : ℕ} {I : Type u_1} {J : Type u_2} [Fintype I] [Fintype J]
    (e : I ≃ J) (p : J → PatternGeometry.Space n) (a D r L C : ℝ) :
    roundedGood (p ∘ e) a D r L C = roundedGood p a D r L C := by
  ext y
  have hc : (relevant (p ∘ e) L y).card = (relevant p L y).card := by
    simp only [relevant,Finset.card_filter,Function.comp_apply]
    exact e.sum_comp (fun j => if ‖y-p j‖ ≤ L then 1 else 0)
  have hs : (∑ i ∈ relevant (p ∘ e) L y,weight n a ‖y-(p ∘ e) i‖) =
      ∑ j ∈ relevant p L y,weight n a ‖y-p j‖ := by
    simp only [relevant,Finset.sum_filter,Function.comp_apply]
    exact e.sum_comp (fun j => if ‖y-p j‖ ≤ L then weight n a ‖y-p j‖ else 0)
  have hall : (∀ i : I,r ≤ ‖y-(p ∘ e) i‖) ↔ (∀ j : J,r ≤ ‖y-p j‖) := by
    constructor
    · intro hh j
      obtain ⟨i,rfl⟩ := e.surjective j
      exact hh i
    · intro hh i
      exact hh (e i)
  simp only [roundedGood,mem_ofPred_eq,hc,hs,hall]

lemma encode {n N : ℕ} {h L : ℝ} {J : Type u_3} [Fintype J]
    (p : J → PatternGeometry.Space n) (hcard : Fintype.card J ≤ N) (hp : ∀ j,p j ∈ alphabet n h L) :
    ∃ P : BoundedLists n h L N,∃ e : Fin P.1.val ≃ J,points P = p ∘ e := by
  let P : BoundedLists n h L N := ⟨⟨Fintype.card J,by omega⟩,
    fun i => ⟨p ((Fintype.equivFin J).symm i),hp _⟩⟩
  exact ⟨P,(Fintype.equivFin J).symm,rfl⟩

lemma encode_retained {n N : ℕ} {h L a D r b C : ℝ} {J : Type u_4} [Fintype J]
    (p : J → PatternGeometry.Space n) (hcard : Fintype.card J ≤ N) (hp : ∀ j,p j ∈ alphabet n h L)
    (hg : volume (closedBall (0 : PatternGeometry.Space n) D) ≤ 4*volume (roundedGood p a D r b C)) :
    ∃ P : Retained n N h L a D r b C,∃ e : Fin P.val.1.val ≃ J,points P.val = p ∘ e := by
  obtain ⟨P,e,he⟩ := encode p hcard hp
  refine ⟨⟨P,?_⟩,e,he⟩
  rw [he,good_reindex]
  exact hg
end PatternEnumeration

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SourceParameters
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace SourceParameters
open Filter
open scoped Topology
lemma a_pos : 0 < a := by norm_num [a,ε]
lemma D_pos : 0 < D := by norm_num [D]
end SourceParameters

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_EntropyRates
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace EntropyRates
open Filter SourceParameters LocalizationRounding
open scoped Topology Classical
lemma mesh {n : ℕ} (hn : 0 < n) : h n = 1/(100*(n:ℝ)^5) := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp [h,RadialShell.η]
  field_simp
lemma mesh_pos {n : ℕ} (hn : 0 < n) : 0 < h n := by rw [mesh hn]; positivity
lemma error_bound {n : ℕ} (hn : 1 ≤ n) : Real.sqrt n*h n/2 ≤ RadialShell.η n := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0<n)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hs : Real.sqrt n ≤ (n:ℝ) := (Real.sqrt_le_iff).mpr ⟨hn0.le,by nlinarith only [hn1]⟩
  have he : (n:ℝ)*h n/2 = RadialShell.η n/200 := by dsimp [h]; field_simp ; ring
  calc
    _ ≤ (n:ℝ)*h n/2 := by gcongr; exact mesh_pos (by omega) |>.le
    _ = _ := he
    _ ≤ _ := by have hh : 0 ≤ RadialShell.η n := by unfold RadialShell.η; positivity
                linarith only [hh]
end EntropyRates

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_LocalizationRates
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace LocalizationRates
open Filter SourceParameters Metric MeasureTheory
open scoped Topology ENNReal
lemma ball_scale {n : ℕ} {a r : ℝ} (ha : 0<a) (hr : 0 ≤ r) :
    volume (closedBall (0:Space n) r) = ENNReal.ofReal ((r/a)^n)*volume (closedBall (0:Space n) a) := by
  rw [volume.addHaar_closedBall _ hr,volume.addHaar_closedBall _ ha.le]
  simp only [finrank_euclideanSpace,Fintype.card_fin]
  rw [← mul_assoc,← ENNReal.ofReal_mul (pow_nonneg (div_nonneg hr ha.le) _)]
  congr 2
  rw [div_pow,div_mul_cancel₀ _ (pow_ne_zero _ ha.ne')]
end LocalizationRates

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_LocalizationMeans
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2

namespace LocalizationMeans
open Set MeasureTheory Metric SourceParameters LocalizationRates LatticeAveraging LocalizationGood
open scoped ENNReal
lemma count_mean {n : ℕ} {I : Type u_1} [Fintype I] (Λ : Submodule ℤ (Space n))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (p : I → Space n) {F : Set (Space n)}
    (hF : IsAddFundamentalDomain Λ F volume) {r R : ℝ} (hr : 0 ≤ r) (_hR : 0≤R)
    (hρ : ((Fintype.card I:ℝ≥0∞)/volume F)*volume (closedBall (0:Space n) a) ≤ ENNReal.ofReal (R/(2*v))) :
    ∫⁻ y,field Λ p (countFn (closedBall (0:Space n) r)) y ∂uniformWindow F ≤
      ENNReal.ofReal ((r/a)^n*(R/(2*v))) := by
  unfold countFn
  rw [normalized_averaging Λ hF p (measurable_const.indicator measurableSet_closedBall)]
  simp only [lintegral_indicator measurableSet_closedBall,lintegral_const,
    Measure.restrict_apply_univ,one_mul]
  rw [ball_scale a_pos hr]
  calc
    _ = ENNReal.ofReal ((r/a)^n)*(((Fintype.card I:ℝ≥0∞)/volume F)*volume (closedBall (0:Space n) a)) := by ac_rfl
    _ ≤ ENNReal.ofReal ((r/a)^n)*ENNReal.ofReal (R/(2*v)) := by gcongr
    _ = _ := (ENNReal.ofReal_mul (pow_nonneg (div_nonneg hr a_pos.le) _)).symm

lemma bounds {n : ℕ} [NeZero n] {I : Type u_2} [Fintype I] (Λ : Submodule ℤ (Space n))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (p : I → Space n) {F : Set (Space n)}
    (hF : IsAddFundamentalDomain Λ F volume) (hF0 : volume F ≠ 0) (hFtop : volume F ≠ ∞)
    {R : ℝ} (hR : 1≤R) (hRn : R≤(n:ℝ)^2)
    (hr : 0 < rminus n) (hβ : 0<β n) (houter : (β n/a)^n≤3)
    (hinner : (n:ℝ)^2/(2*v)*(rminus n/a)^n≤1/200)
    (hρ : ((Fintype.card I:ℝ≥0∞)/volume F)*volume (closedBall (0:Space n) a) ≤ ENNReal.ofReal (R/(2*v))) :
    uniformWindow F (good Λ p a (rminus n) (β n) (ENNReal.ofReal (Cloc*R)))ᶜ ≤ 1/100 ∧
    (∫⁻ y,field Λ p (countFn (closedBall (0:Space n) (W n))) y ∂uniformWindow F) ≤ (N n R:ℝ≥0∞)/40 := by
  have hR0 : 0<R := lt_of_lt_of_le (by norm_num) hR
  have hv : 0<v := by norm_num [v]
  have hCloc : 0<Cloc := by norm_num [Cloc,v]
  have hC : 0<Cloc*R := mul_pos hCloc hR0
  let := probability_window hF0 hFtop
  have hnum (q : ℝ) (hq : 0≤q) : ENNReal.ofReal (q*(R/(2*v))) = ENNReal.ofReal (Cloc*R)*(ENNReal.ofReal (q/2000)) := by
    rw [← ENNReal.ofReal_mul hC.le]
    congr 1
    dsimp [Cloc]
    field_simp
    ring
  have hout : ∫⁻ y,field Λ p (countFn (closedBall (0:Space n) (β n))) y ∂uniformWindow F ≤ ENNReal.ofReal (Cloc*R)*(3/2000) := by
    calc
      _ ≤ ENNReal.ofReal ((β n/a)^n*(R/(2*v))) := count_mean Λ p hF hβ.le hR0.le hρ
      _ ≤ ENNReal.ofReal (3*(R/(2*v))) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right houter (by positivity))
      _ = _ := by rw [hnum 3 (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2000)]; norm_num
  have hin : ∫⁻ y,field Λ p (countFn (ball (0:Space n) (rminus n))) y ∂uniformWindow F ≤ 1/200 := by
    have hm : ∀ y,field Λ p (countFn (ball (0:Space n) (rminus n))) y ≤ field Λ p (countFn (closedBall (0:Space n) (rminus n))) y := by
      intro y
      apply Finset.sum_le_sum
      intro i _
      apply ENNReal.tsum_le_tsum
      intro l
      exact Set.indicator_le_indicator_of_subset ball_subset_closedBall (fun _ => bot_le) _
    calc
      _ ≤ ∫⁻ y,field Λ p (countFn (closedBall (0:Space n) (rminus n))) y ∂uniformWindow F := lintegral_mono hm
      _ ≤ ENNReal.ofReal ((rminus n/a)^n*(R/(2*v))) := count_mean Λ p hF hr.le hR0.le hρ
      _ ≤ ENNReal.ofReal (1/200) := ENNReal.ofReal_le_ofReal (by
        calc
          _ ≤ (rminus n/a)^n*((n:ℝ)^2/(2*v)) := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hRn (by positivity)) (pow_nonneg (div_nonneg hr.le a_pos.le) _)
          _ ≤ _ := by simpa only [mul_comm] using hinner)
      _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<200)]; norm_num
  have hweight : ∫⁻ y,field Λ p (weightedFn a (β n)) y ∂uniformWindow F ≤ ENNReal.ofReal (Cloc*R)*(5/2000) := by
    rw [normalized_averaging Λ hF p (measurable_weightedFn a (β n))]
    have hVβ : volume (closedBall (0:Space n) (β n)) ≤ 3*volume (closedBall (0:Space n) a) := by
      rw [ball_scale a_pos hβ.le]
      gcongr
      simpa using ENNReal.ofReal_le_ofReal houter
    calc
      _ ≤ ((Fintype.card I:ℝ≥0∞)/volume F)*(volume (closedBall (0:Space n) (β n))+2*volume (closedBall (0:Space n) a)) := by gcongr; exact WeightedVolume.weighted_lintegral a_pos
      _ ≤ ((Fintype.card I:ℝ≥0∞)/volume F)*(3*volume (closedBall (0:Space n) a)+2*volume (closedBall (0:Space n) a)) := by gcongr
      _ = 5*(((Fintype.card I:ℝ≥0∞)/volume F)*volume (closedBall (0:Space n) a)) := by ring
      _ ≤ 5*ENNReal.ofReal (R/(2*v)) := by gcongr
      _ = ENNReal.ofReal (5*(R/(2*v))) := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤5)]; norm_num
      _ = _ := by rw [hnum 5 (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2000)]; norm_num
  refine ⟨bad_bound Λ p a (rminus n) (β n) _ (ENNReal.ofReal_ne_zero_iff.mpr hC) ENNReal.ofReal_ne_top (uniformWindow F) hin hout hweight,?_⟩
  have hW0 : 0<W n := by simpa only [W,β,add_assoc] using add_pos D_pos hβ
  have hWL : W n≤L n := by
    have he : 0≤RadialShell.η n := by unfold RadialShell.η; positivity
    dsimp [W,L]; linarith only [he]
  have hceil : 20*R/v*(L n/a)^n≤(N n R:ℝ) := Nat.le_ceil _
  calc
    _ ≤ ENNReal.ofReal ((W n/a)^n*(R/(2*v))) := count_mean Λ p hF hW0.le hR0.le hρ
    _ ≤ ENNReal.ofReal ((N n R:ℝ)/40) := ENNReal.ofReal_le_ofReal (by
      have hh : (W n/a)^n≤(L n/a)^n := pow_le_pow_left₀ (div_nonneg hW0.le a_pos.le) (div_le_div_of_nonneg_right hWL a_pos.le) n
      have h1 := mul_le_mul_of_nonneg_right hh (show 0≤R/(2*v) by positivity)
      have he : (L n/a)^n*(R/(2*v)) = (20*R/v*(L n/a)^n)/40 := by ring
      rw [he] at h1
      exact h1.trans (div_le_div_of_nonneg_right hceil (by norm_num)))
    _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<40)]; norm_num
end LocalizationMeans

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SourceLocalization
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2

namespace SourceLocalization
open Set Metric MeasureTheory SourceParameters LocalizationRates LocalizationRounding PatternGeometry PatternEnumeration
open scoped ENNReal Classical
lemma good_mono_inner {n : ℕ} {J : Type u_1} [Fintype J] (p : J → Space n)
    {a D r r' b C : ℝ} (hr : r' ≤ r) : roundedGood p a D r b C ⊆ roundedGood p a D r' b C := by
  intro y hy
  exact ⟨hy.1,fun i => hr.trans (hy.2.1 i),hy.2.2⟩
lemma localize {n : ℕ} [NeZero n] {I : Type u_2} [Fintype I] (Λ : Submodule ℤ (Space n))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (p : I → Space n) {F : Set (Space n)}
    (hF : IsAddFundamentalDomain Λ F volume) (hF0 : volume F≠0) (hFtop : volume F≠∞)
    {R : ℝ} (hR : 1≤R) (hRn : R≤(n:ℝ)^2) (hn : 1≤n)
    (hr : 0 < rminus n) (hβ : 0<β n) (houter : (β n/a)^n≤3)
    (hinner : (n:ℝ)^2/(2*v)*(rminus n/a)^n≤1/200)
    (hlip : (2*(n:ℝ)/a)*(Real.sqrt n*h n/2)≤1)
    (hρ : ((Fintype.card I:ℝ≥0∞)/volume F)*volume (closedBall (0:Space n) a) ≤ ENNReal.ofReal (R/(2*v)))
    (U : PoissonConfig.Config (SphericalLaw.Sphere n))
    (hc : ∀ y,∃ (i:I) (l:Λ), y-p i-l.val ∈ RandomBody.body (b n) 1 U) :
    ∃ P : Patterns n R,U ∈ PatternTail.coverEvent (points P.val) a D := by
  have hm := LocalizationMeans.bounds Λ p hF hF0 hFtop hR hRn hr hβ houter hinner hρ
  have he := EntropyRates.error_bound hn
  have he0 : 0≤RadialShell.η n := by unfold RadialShell.η; positivity
  have hh := EntropyRates.mesh_pos (by omega : 0<n)
  have hC : 0≤Cloc*R := by
    have hCl : 0<Cloc := by norm_num [Cloc,v]
    exact mul_nonneg hCl.le (by linarith only [hR])
  have hN : 0<N n R := by
    apply Nat.ceil_pos.mpr
    have hL : 0<L n := by
      have ha := a_pos; have hD := D_pos
      dsimp [L,b]; positivity
    have hv : 0<v := by norm_num [v]
    have ha := a_pos
    positivity
  obtain ⟨S,q,hS,hq,hg,hcover⟩ := LocalizationComplete.localize Λ p hF hF0 hFtop a_pos D_pos hh hC
    (show D+b n≤W n by dsimp [W]; linarith only [he0])
    (show RadialShell.high a n+Real.sqrt n*h n/2≤β n by dsimp [RadialShell.high,β,b]; linarith only [he]) hlip hN hm.1 hm.2 U hc
  have hq' (j:S) : q j ∈ alphabet n (h n) (L n) := by
    obtain ⟨hz,hbound⟩ := (mem_alphabet hh _).mp (hq j)
    apply (mem_alphabet hh _).mpr ⟨hz,?_⟩
    apply hbound.trans
    dsimp [W,L]
    linarith only [he]
  have hg' : volume (closedBall (0:Space n) D) ≤ 4*volume (roundedGood q a D (rround n) (RadialShell.high a n) (2*Cloc*R)) := by
    have sub := good_mono_inner q (show rround n ≤ rminus n-Real.sqrt n*h n/2 by dsimp [rround]; linarith only [he,he0]) (a:=a) (D:=D) (b:=RadialShell.high a n) (C:=2*(Cloc*R))
    have hh := hg.trans (mul_le_mul_right (measure_mono sub) 2)
    have heq : 2*(Cloc*R)=2*Cloc*R := by ring
    rw [heq] at hh
    exact hh.trans (mul_le_mul_left (by norm_num : (2:ℝ≥0∞)≤4) _)
  obtain ⟨P,e,hp⟩ := encode_retained q (by simpa using hS) hq' hg'
  refine ⟨P,?_⟩
  intro y hy
  obtain ⟨j,hj⟩ := hcover y hy
  obtain ⟨i,rfl⟩ := e.surjective j
  rw [hp]
  refine ⟨i,?_,?_⟩
  · apply closedBall_subset_closedBall (show b n+Real.sqrt n*h n/2≤RadialShell.high a n by dsimp [RadialShell.high,b]; linarith only [he,he0]) hj.1
  · simp only [RandomBody.body,Set.mem_inter_iff,Set.mem_iInter,Set.mem_ofPred_eq] at hj ⊢
    intro u
    exact (hj.2 u).trans (by linarith only [he,he0])
end SourceLocalization

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_AllLatticeExclusion
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2

namespace AllLatticeExclusion
open Set Metric MeasureTheory SourceParameters LocalizationRates PatternEnumeration SourceLocalization
open scoped ENNReal Classical
lemma intensity_bound {n : ℕ} {I : Type u_1} [Fintype I] {F K : Set (Space n)}
    (hF0 : volume F≠0) (_hFtop : volume F≠∞) (_hKtop : volume K≠∞)
    {R : ℝ} (hR : 0≤R)
    (hvol : 2*v*volume.real (closedBall (0:Space n) a)<volume.real K)
    (hdensity : volume K*((Fintype.card I:ℝ≥0∞)/volume F)≤ENNReal.ofReal R) :
    ((Fintype.card I:ℝ≥0∞)/volume F)*volume (closedBall (0:Space n) a)≤ENNReal.ofReal (R/(2*v)) := by
  let ρ : ℝ≥0∞ := (Fintype.card I:ℝ≥0∞)/volume F
  have hρtop : ρ≠∞ := ENNReal.div_ne_top (by finiteness) hF0
  have hVtop : volume (closedBall (0:Space n) a)≠∞ := (isCompact_closedBall _ _).measure_ne_top
  have hv : 0<v := by norm_num [v]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hdensity
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hR] at hh
  have hp : ρ.toReal*volume.real (closedBall (0:Space n) a)≤R/(2*v) := by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<2*v)).mpr
    have hmul := mul_le_mul_of_nonneg_right hvol.le (ENNReal.toReal_nonneg (a:=ρ))
    change (volume K).toReal*ρ.toReal≤R at hh
    dsimp [Measure.real] at hmul ⊢
    nlinarith only [hmul,hh]
  apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top hρtop hVtop) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (div_nonneg hR (by positivity))]
  exact hp

theorem no_cover_oai {n : ℕ} [NeZero n] {R : ℝ} (hR : 1≤R) (hRn : R≤(n:ℝ)^2)
    (hn : 1≤n) (hr : 0 < rminus n) (hβ : 0<β n) (houter : (β n/a)^n≤3)
    (hinner : (n:ℝ)^2/(2*v)*(rminus n/a)^n≤1/200)
    (hlip : (2*(n:ℝ)/a)*(Real.sqrt n*h n/2)≤1)
    (U : PoissonConfig.Config (SphericalLaw.Sphere n))
    (hvol : 2*v*volume.real (closedBall (0:Space n) a)<volume.real (RandomBody.body (b n) 1 U))
    (hbad : U ∉ BodySelection.bad R)
    {I : Type u_2} [Fintype I] (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (p : I → Space n) {F : Set (Space n)}
    (hF : IsAddFundamentalDomain Λ F volume) (hF0 : volume F≠0) (hFtop : volume F≠∞)
    (hdensity : volume (RandomBody.body (b n) 1 U)*((Fintype.card I:ℝ≥0∞)/volume F)≤ENNReal.ofReal R) :
    ¬ (∀ y,∃ (i:I) (l:Λ), y-p i-l.val ∈ RandomBody.body (b n) 1 U) := by
  intro hc
  have hρ := intensity_bound hF0 hFtop (RandomBody.body_compact _ _ _).measure_ne_top (by linarith only [hR]) hvol hdensity
  obtain ⟨P,hP⟩ := SourceLocalization.localize Λ p hF hF0 hFtop hR hRn hn hr hβ houter hinner hlip hρ U hc
  exact hbad (Set.mem_iUnion.mpr ⟨P,hP⟩)
end AllLatticeExclusion

end OAI
end

theorem solution.{u_2} : type_of% @OAI.AllLatticeExclusion.no_cover_oai.{u_2} := @OAI.AllLatticeExclusion.no_cover_oai.{u_2}
