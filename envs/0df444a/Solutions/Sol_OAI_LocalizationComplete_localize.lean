-- Prove2me | solution 1 for OAI.LocalizationComplete.localize
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T14:51:26.787988+00:00
-- url     : https://prove2.me/submissions/1c5f488a-69b9-4021-8c21-ace53b6f9459

import Mathlib
import Definitions.Def_OAIQ16Cd000

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

lemma periodic {n : ℕ} {I : Type u_4} [Fintype I]
    (Λ : Submodule ℤ (Space n)) (p : I → Space n) (f : Space n → ℝ≥0∞)
    (y : Space n) (l : Λ) : field Λ p f (y+l.val) = field Λ p f y := by
  unfold field
  apply Finset.sum_congr rfl
  intro i _
  have hh := (Equiv.addRight l).tsum_eq (fun k : Λ => f (y+l.val-p i-k.val))
  change (∑' k : Λ, f (y+l.val-p i-(k.val+l.val))) = _ at hh
  simpa only [show ∀ k : Λ,
    y+l.val-p i-(k.val+l.val) = y-p i-k.val by intro k; abel] using hh.symm

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
-- module Solutions.OAIQ16_CD.TranslativeCovering_LocalizationWindow
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal

universe u_1 u_2

namespace LocalizationWindow
open Set MeasureTheory LatticeAveraging
open scoped ENNReal Pointwise BigOperators

lemma periodic_integral_translate {n : ℕ} (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ]
    {F : Set (Space n)} (hF : IsAddFundamentalDomain Λ F volume)
    (f : Space n → ℝ≥0∞) (hp : ∀ (l : Λ) y,f (y+l.val) = f y) (x : Space n) :
    ∫⁻ y in F,f (y+x) = ∫⁻ y in F,f y := by
  let : Countable Λ := countable_of_Lindelof_of_discrete
  let : VAddInvariantMeasure Λ (Space n) volume :=
    inferInstanceAs (VAddInvariantMeasure Λ.toAddSubgroup (Space n) volume)
  have htrans : ∫⁻ y in F,f (x+y) = ∫⁻ y in x +ᵥ F,f y := by
    exact (measurePreserving_add_left volume x).setLIntegral_comp_emb
      (Homeomorph.addLeft x).measurableEmbedding f F
  have ht := hF.setLIntegral_eq (hF.vadd_of_comm x) f (fun l y => by
    change f (l.val+y) = f y
    rw [add_comm]; exact hp l y)
  simpa only [add_comm] using htrans.trans ht.symm

lemma periodic_average_translate {n : ℕ} (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ]
    {F : Set (Space n)} (hF : IsAddFundamentalDomain Λ F volume)
    (f : Space n → ℝ≥0∞) (hp : ∀ (l : Λ) y,f (y+l.val) = f y) (x : Space n) :
    ∫⁻ y,f (y+x) ∂uniformWindow F = ∫⁻ y,f y ∂uniformWindow F := by
  simp only [uniformWindow,lintegral_smul_measure]
  rw [periodic_integral_translate Λ hF f hp x]

lemma overlapping_windows {n : ℕ} (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ]
    {F B : Set (Space n)} (hF : IsAddFundamentalDomain Λ F volume)
    (hF0 : volume F ≠ 0) (hFtop : volume F ≠ ∞)
    (f : Space n → ℝ≥0∞) (hf : Measurable f)
    (hp : ∀ (l : Λ) y,f (y+l.val) = f y) :
    ∫⁻ z,(∫⁻ y in B,f (z+y)) ∂uniformWindow F =
      volume B * ∫⁻ z,f z ∂uniformWindow F := by
  let := probability_window hF0 hFtop
  have hh : Measurable (fun p : Space n × Space n => f (p.1+p.2)) :=
    hf.comp (measurable_fst.add measurable_snd)
  rw [lintegral_lintegral_swap hh.aemeasurable]
  simp_rw [periodic_average_translate Λ hF f hp]
  rw [lintegral_const,Measure.restrict_apply_univ,mul_comm]

lemma slide {Ω : Type u_1} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M Z : Ω → ℝ≥0∞) (hM : Measurable M) (hZ : Measurable Z) {N L : ℝ≥0∞}
    (hN : N ≠ 0) (hNtop : N ≠ ∞) (hL : L ≠ 0) (hLtop : L ≠ ∞)
    (heM : ∫⁻ z,M z ∂P ≤ N/40) (heZ : ∫⁻ z,Z z ∂P ≤ L/100) :
    ∃ z,M z ≤ N ∧ Z z ≤ L/2 := by
  have hint : ∫⁻ z,(M z/N+2*(Z z/L)) ∂P < 1 := by
    rw [lintegral_add_left (hM.div_const N),lintegral_const_mul _ (hZ.div_const L)]
    simp_rw [div_eq_mul_inv,lintegral_mul_const _ hM,lintegral_mul_const _ hZ]
    change (∫⁻ z,M z ∂P)/N+2*((∫⁻ z,Z z ∂P)/L) < 1
    have hm := ENNReal.div_le_div_right heM N
    have hz : 2*((∫⁻ z,Z z ∂P)/L) ≤ 2*((L/100)/L) := by gcongr
    have hmn : (N/40)/N = 1/40 := by
      rw [ENNReal.div_right_comm,ENNReal.div_self hN hNtop]
    have hln : (L/100)/L = 1/100 := by
      rw [ENNReal.div_right_comm,ENNReal.div_self hL hLtop]
    rw [hmn] at hm
    rw [hln] at hz
    exact (add_le_add hm hz).trans_lt (by
      apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
      rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
      norm_num [ENNReal.toReal_mul,ENNReal.toReal_div])
  by_contra! hall
  have hone (z : Ω) : 1 ≤ M z/N+2*(Z z/L) := by
    by_cases hm : M z ≤ N
    · have hz := hall z hm
      have hz' : 1/2 < Z z/L := by
        apply (ENNReal.lt_div_iff_mul_lt (Or.inl hL) (Or.inl hLtop)).mpr
        simpa [div_eq_mul_inv,mul_comm] using hz
      have htwo : (2:ℝ≥0∞)*(1/2) ≤ 2*(Z z/L) := by gcongr
      have hh : (1:ℝ≥0∞) ≤ 2*(Z z/L) := by simpa only [one_div,ENNReal.mul_inv_cancel (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num : (2:ℝ≥0∞) ≠ ∞)] using htwo
      exact hh.trans (le_add_self)
    · have hh : 1 < M z/N := by
        apply (ENNReal.lt_div_iff_mul_lt (Or.inl hN) (Or.inl hNtop)).mpr
        simpa using lt_of_not_ge hm
      exact hh.le.trans (le_self_add)
  have hmono := lintegral_mono (μ := P) hone
  simp only [lintegral_const,measure_univ,mul_one] at hmono
  exact (not_lt_of_ge hmono) hint

lemma finite_occurrences {n : ℕ} {I : Type u_2} [Fintype I]
    (Λ : Submodule ℤ (Space n)) [DiscreteTopology Λ] (p : I → Space n)
    {B : Set (Space n)} (hB : Bornology.IsBounded B) :
    {q : I×Λ | p q.1+q.2.val ∈ B}.Finite := by
  have each (i : I) : {l : Λ | p i+l.val ∈ B}.Finite := by
    have hb : Bornology.IsBounded ((fun x : Space n => -p i+x) '' B) :=
      (isometry_add_left (-p i)).lipschitz.isBounded_image hB
    have hc : IsClosed (Λ : Set (Space n)) := AddSubgroup.isClosed_of_discrete (H := Λ.toAddSubgroup)
    have hf := Metric.finite_isBounded_inter_isClosed
      (s := (Λ : Set (Space n))) DiscreteTopology.isDiscrete hb hc
    apply Set.Finite.of_injOn (f := fun l : Λ => l.val) (t := _ ∩ (Λ : Set (Space n)))
      ?_ (Subtype.val_injective.injOn) hf
    intro l hl
    refine ⟨⟨p i+l.val,hl,by simp⟩,l.property⟩
  apply (Set.finite_iUnion (fun i => (each i).image (fun l => (i,l)))).subset
  intro q hq
  exact Set.mem_iUnion.mpr ⟨q.1,⟨q.2,hq,rfl⟩⟩

end LocalizationWindow

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

lemma truncated_square {a r s : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    max (a^2-s^2) 0 ≤ max (a^2-r^2) 0+2*a*|s-r| := by
  have hab : |r-s| = |s-r| := abs_sub_comm _ _
  have hzero : 0 ≤ 2*a*|s-r| := by positivity
  apply max_le _ (by have := le_max_right (a^2-r^2) 0; linarith)
  by_cases hsa : s ≤ a
  · by_cases hra : r ≤ a
    · have hsum : r+s ≤ 2*a := by linarith
      have hmul := mul_le_mul_of_nonneg_right (le_abs_self (r-s)) (add_nonneg hr hs)
      rw [hab] at hmul
      have hmul' := mul_le_mul_of_nonneg_left hsum (abs_nonneg (s-r))
      have hm := le_max_left (a^2-r^2) 0
      nlinarith only [hmul,hmul',hm]
    · have har : 0 ≤ r-a := by linarith [le_of_not_ge hra]
      have hdist : a-s ≤ |s-r| := by
        have hh := le_abs_self (r-s)
        rw [hab] at hh
        linarith only [hh,har]
      have hh := mul_le_mul_of_nonneg_right hdist (by linarith : 0 ≤ 2*a)
      have hm := le_max_right (a^2-r^2) 0
      nlinarith only [hh,hm,sq_nonneg (a-s)]
  · have hsq : a^2 ≤ s^2 := (sq_le_sq₀ ha.le hs).mpr (le_of_not_ge hsa)
    have hm := le_max_right (a^2-r^2) 0
    linarith only [hsq,hm,hzero]

lemma weight_lipschitz {n : ℕ} {a r s : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    weight n a s ≤ weight n a r+(2*(n:ℝ)/a)*|s-r| := by
  have hh := div_le_div_of_nonneg_right (truncated_square ha hr hs) (sq_nonneg a)
  have he (t : ℝ) : max (a^2-t^2) 0/a^2 = max (1-t^2/a^2) 0 := by
    rw [← max_div_div_right (sq_nonneg a),sub_div,div_self (pow_ne_zero _ ha.ne'),zero_div]
  rw [add_div,he s,he r] at hh
  have hm := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  dsimp [weight]
  have he2 : (n:ℝ)*(2*a*|s-r|/a^2) = (2*(n:ℝ)/a)*|s-r| := by field_simp
  rw [mul_add,he2] at hm
  linarith only [hm]

lemma rounded_coord {n : ℕ} {h : ℝ} (hh : 0 < h) (x : Space n) (i : Fin n) :
    |x i-rounded h x i| ≤ h/2 := by
  have hb := abs_sub_round (x i/h)
  have hb' := mul_le_mul_of_nonneg_left hb hh.le
  calc
    _ = |h*(x i/h-(round (x i/h):ℝ))| := by
      congr 1
      dsimp [rounded]
      field_simp
    _ = h*|x i/h-(round (x i/h):ℝ)| := by rw [abs_mul,abs_of_pos hh]
    _ ≤ h*(1/2) := hb'
    _ = _ := by ring

lemma rounding_error {n : ℕ} {h : ℝ} (hh : 0 < h) (x : Space n) :
    ‖x-rounded h x‖ ≤ Real.sqrt n*h/2 := by
  rw [EuclideanSpace.norm_eq]
  have hs : ∑ i : Fin n,‖(x-rounded h x).ofLp i‖^2 ≤ (n:ℝ)*(h/2)^2 := by
    calc
      _ ≤ ∑ _i : Fin n,(h/2)^2 := Finset.sum_le_sum fun i _ => by
        apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
        simpa only [PiLp.sub_apply,Real.norm_eq_abs] using rounded_coord hh x i
      _ = _ := by simp
  apply (Real.sqrt_le_sqrt hs).trans_eq
  rw [Real.sqrt_mul (Nat.cast_nonneg n),Real.sqrt_sq (by positivity)]
  ring

lemma residual_error {n : ℕ} {h : ℝ} (hh : 0 < h) (x y : Space n) :
    |‖y-rounded h x‖-‖y-x‖| ≤ Real.sqrt n*h/2 := by
  calc
    _ ≤ ‖(y-rounded h x)-(y-x)‖ := abs_norm_sub_norm_le _ _
    _ = ‖x-rounded h x‖ := by congr 1; abel
    _ ≤ _ := rounding_error hh x

lemma norm_buffer {n : ℕ} {h r : ℝ} (hh : 0 < h) (x y : Space n)
    (hr : ‖y-x‖ ≤ r) : ‖y-rounded h x‖ ≤ r+Real.sqrt n*h/2 := by
  have ht := residual_error hh x y
  have hx := le_abs_self (‖y-rounded h x‖-‖y-x‖)
  linarith only [hr,ht,hx]

lemma slab_buffer {n : ℕ} {h T : ℝ} (hh : 0 < h) (x y u : Space n)
    (hu : ‖u‖ = 1) (hslab : |inner ℝ u (y-x)| ≤ T) :
    |inner ℝ u (y-rounded h x)| ≤ T+Real.sqrt n*h/2 := by
  have hdecomp : y-rounded h x = (y-x)+(x-rounded h x) := by abel
  rw [hdecomp,inner_add_right]
  calc
    _ ≤ |inner ℝ u (y-x)|+|inner ℝ u (x-rounded h x)| := abs_add_le _ _
    _ ≤ T+‖u‖*‖x-rounded h x‖ := add_le_add hslab (abs_real_inner_le_norm _ _)
    _ ≤ _ := by rw [hu,one_mul]; exact add_le_add_right (rounding_error hh x) T

lemma weight_transfer {n : ℕ} {a h : ℝ} (ha : 0 < a) (hh : 0 < h) (x y : Space n) :
    weight n a ‖y-rounded h x‖ ≤
      (1+(2*(n:ℝ)/a)*(Real.sqrt n*h/2))*weight n a ‖y-x‖ := by
  have hLip := weight_lipschitz (n := n) ha (norm_nonneg (y-x)) (norm_nonneg (y-rounded h x))
  have herr := mul_le_mul_of_nonneg_left (residual_error hh x y) (by positivity : 0 ≤ 2*(n:ℝ)/a)
  have hw : 1 ≤ weight n a ‖y-x‖ := by
    dsimp [weight]; have := mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (le_max_right (1-‖y-x‖^2/a^2) 0); linarith
  have hm := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ (2*(n:ℝ)/a)*(Real.sqrt n*h/2))
  nlinarith only [hLip,herr,hm]

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

lemma rounded_mem_alphabet {n : ℕ} {h L : ℝ} (hh : 0 < h) (x : Space n)
    (hx : ‖x‖+Real.sqrt n*h/2 ≤ L) : rounded h x ∈ alphabet n h L := by
  apply (mem_alphabet hh _).mpr
  refine ⟨⟨fun i => round (x i/h),rfl⟩,?_⟩
  have hh' : ‖rounded h x‖ ≤ ‖x‖+‖x-rounded h x‖ := by
    have he : rounded h x = x-(x-rounded h x) := by abel
    conv_lhs => rw [he]
    exact norm_sub_le x (x-rounded h x)
  exact (hh'.trans (add_le_add_right (rounding_error hh x) ‖x‖)).trans hx

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

lemma measurable_good {n : ℕ} {I : Type u_4} [Fintype I] (Λ : Submodule ℤ (Space n))
    [DiscreteTopology Λ] (p : I → Space n) (a r β : ℝ) (C : ℝ≥0∞) :
    MeasurableSet (good Λ p a r β C) := by
  exact (measurableSet_eq_fun (measurable_field Λ p (measurable_const.indicator measurableSet_ball)) measurable_const).inter
    ((measurableSet_le (measurable_field Λ p (measurable_const.indicator measurableSet_closedBall)) measurable_const).inter
      (measurableSet_le (measurable_field Λ p (measurable_weightedFn a β)) measurable_const))

lemma periodic_good {n : ℕ} {I : Type u_5} [Fintype I] (Λ : Submodule ℤ (Space n))
    (p : I → Space n) (a r β : ℝ) (C : ℝ≥0∞) (y : Space n) (l : Λ) :
    y+l.val ∈ good Λ p a r β C ↔ y ∈ good Λ p a r β C := by
  simp only [good,mem_ofPred_eq,periodic]

end LocalizationGood

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PatternGeometry
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

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace PatternGeometry
open Set Metric MeasureTheory SphericalLaw PoissonConfig LocalizationRounding
open scoped BigOperators ENNReal Classical

lemma rounding_cover {n : ℕ} {I : Type u_7} [Fintype I] (p : I → Space n) {h : ℝ}
    (hh : 0 < h) (U : Config (Sphere n)) (b t D : ℝ)
    (hc : ∀ y ∈ closedBall (0 : Space n) D,∃ i,y-p i ∈ RandomBody.body b t U) :
    ∀ y ∈ closedBall (0 : Space n) D,∃ i,y-rounded h (p i) ∈
      RandomBody.body (b+Real.sqrt n*h/2) (t+Real.sqrt n*h/2) U := by
  intro y hy
  obtain ⟨i,hi⟩ := hc y hy
  refine ⟨i,mem_closedBall_zero_iff.mpr (norm_buffer hh (p i) y (mem_closedBall_zero_iff.mp hi.1)),?_⟩
  apply mem_iInter.mpr
  intro j
  exact slab_buffer hh (p i) y (U.2.val j).val (mem_sphere_zero_iff_norm.mp (U.2.val j).property)
    (mem_iInter.mp hi.2 j)

end PatternGeometry

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PatternRounding
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

universe u_1 u_2 u_3

namespace PatternRounding
open Set Metric MeasureTheory SphericalLaw LocalizationRounding PatternGeometry
open LatticeAveraging LocalizationGood
open scoped ENNReal BigOperators Classical

lemma finite_sum_le_field {n : ℕ} {I : Type u_1} [Fintype I] (Λ : Submodule ℤ (Space n))
    (p : I → Space n) (f : Space n → ℝ≥0∞) (y : Space n) (S : Finset (I×Λ)) :
    ∑ q ∈ S,f (y-p q.1-q.2.val) ≤ field Λ p f y := by
  calc
    _ ≤ ∑' q : I×Λ,f (y-p q.1-q.2.val) := ENNReal.sum_le_tsum S
    _ = _ := by rw [ENNReal.tsum_prod',tsum_fintype]; rfl

lemma finite_weight {n : ℕ} {I : Type u_2} [Fintype I] (Λ : Submodule ℤ (Space n))
    (p : I → Space n) (a β C : ℝ) (y : Space n) (S : Finset (I×Λ))
    (hS : ∀ q ∈ S,‖y-p q.1-q.2.val‖ ≤ β)
    (hW : field Λ p (weightedFn a β) y ≤ ENNReal.ofReal C) (hC : 0 ≤ C) :
    ∑ q ∈ S,weight n a ‖y-p q.1-q.2.val‖ ≤ C := by
  have hn (q : I×Λ) : 0 ≤ weight n a ‖y-p q.1-q.2.val‖ := by
    dsimp [weight]; positivity
  have hs := finite_sum_le_field Λ p (weightedFn a β) y S
  have he : (∑ q ∈ S,weightedFn a β (y-p q.1-q.2.val)) =
      ENNReal.ofReal (∑ q ∈ S,weight n a ‖y-p q.1-q.2.val‖) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun q _ => hn q)]
    apply Finset.sum_congr rfl
    intro q hq
    have hm : y-p q.1-q.2.val ∈ closedBall (0 : Space n) β := mem_closedBall_zero_iff.mpr (hS q hq)
    simp only [weightedFn,Set.indicator_of_mem hm,weight]
  rw [he] at hs
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp (hs.trans hW)

lemma good_transfer {n : ℕ} {I : Type u_3} [Fintype I] (Λ : Submodule ℤ (Space n))
    (p : I → Space n) (S : Finset (I×Λ)) (z y : Space n)
    {a D r L β h C : ℝ} (ha : 0 < a) (hh : 0 < h) (hC : 0 ≤ C)
    (hbuf : L+Real.sqrt n*h/2 ≤ β) (hlip : (2*(n:ℝ)/a)*(Real.sqrt n*h/2) ≤ 1)
    (hy : y ∈ closedBall (0 : Space n) D) (hg : y+z ∈ good Λ p a r β (ENNReal.ofReal C)) :
    y ∈ roundedGood (fun q : S => rounded h (p q.val.1+q.val.2.val-z))
      a D (r-Real.sqrt n*h/2) L (2*C) := by
  let c : S → Space n := fun q => p q.val.1+q.val.2.val-z
  let c' : S → Space n := fun q => rounded h (c q)
  have he (q : S) : y-c q = y+z-p q.val.1-q.val.2.val := by dsimp [c]; abel
  have hi (q : S) : r ≤ ‖y-c q‖ := by rw [he]; exact (inner_zero Λ p r (y+z)).mp hg.1 q.val.1 q.val.2
  have hr (q : S) : r-Real.sqrt n*h/2 ≤ ‖y-c' q‖ := by
    have herror := residual_error hh (c q) y
    have hh' := neg_le_of_abs_le herror
    change -(Real.sqrt n*h/2) ≤ ‖y-c' q‖-‖y-c q‖ at hh'
    linarith only [hi q,hh']
  let Q := relevant c' L y
  let T : Finset (I×Λ) := Q.image Subtype.val
  have hT (q : S) (hq : q ∈ Q) : ‖y-c q‖ ≤ β := by
    have hround := (Finset.mem_filter.mp hq).2
    have herror := residual_error hh (c q) y
    have hh' := neg_le_of_abs_le herror
    change -(Real.sqrt n*h/2) ≤ ‖y-c' q‖-‖y-c q‖ at hh'
    linarith only [hround,hh',hbuf]
  have hs : ∑ q ∈ Q,weight n a ‖y-c q‖ ≤ C := by
    have ht : ∀ q ∈ T,‖y+z-p q.1-q.2.val‖ ≤ β := by
      intro q hq
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hq
      rw [← he j]
      exact hT j hj
    have hh := finite_weight Λ p a β C (y+z) T ht hg.2.2 hC
    rw [Finset.sum_image (fun _ _ _ _ he => Subtype.ext he)] at hh
    simpa only [← he] using hh
  have hsw : ∑ q ∈ Q,weight n a ‖y-c' q‖ ≤ 2*C := by
    calc
      _ ≤ ∑ q ∈ Q,2*weight n a ‖y-c q‖ := Finset.sum_le_sum fun q _ =>
        (weight_transfer ha hh (c q) y).trans (by
          have hw : 0 ≤ weight n a ‖y-c q‖ := by dsimp [weight]; positivity
          exact mul_le_mul_of_nonneg_right (by linarith only [hlip]) hw)
      _ = 2*(∑ q ∈ Q,weight n a ‖y-c q‖) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by norm_num)
  refine ⟨hy,hr,?_,hsw⟩
  have hc : (Q.card:ℝ) ≤ ∑ q ∈ Q,weight n a ‖y-c' q‖ := by
    calc
      _ = ∑ _q ∈ Q,(1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun q _ => by
        dsimp [weight]
        have : 0 ≤ (n:ℝ)*max (1-‖y-c' q‖^2/a^2) 0 := by positivity
        linarith only [this]
  exact hc.trans hsw

end PatternRounding

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_LocalizationComplete
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

universe u_1 u_2

namespace LocalizationComplete
open Set Metric MeasureTheory LatticeAveraging LocalizationWindow LocalizationGood
open PatternGeometry PatternRounding LocalizationRounding
open scoped ENNReal BigOperators Classical

lemma window {n : ℕ} {I : Type u_1} [Fintype I] (Λ : Submodule ℤ (Space n))
    [DiscreteTopology Λ] (p : I → Space n) {F : Set (Space n)}
    (hF : IsAddFundamentalDomain Λ F volume) (hF0 : volume F ≠ 0) (hFtop : volume F ≠ ∞)
    {a r β C D L : ℝ} (hD : 0 < D) {N : ℕ} (hN : 0 < N)
    (hbad : uniformWindow F (good Λ p a r β (ENNReal.ofReal C))ᶜ ≤ 1/100)
    (hcount : ∫⁻ z,field Λ p (countFn (closedBall (0 : Space n) L)) z ∂uniformWindow F ≤ (N:ℝ≥0∞)/40) :
    ∃ z,field Λ p (countFn (closedBall (0 : Space n) L)) z ≤ (N:ℝ≥0∞) ∧
      volume (closedBall (0 : Space n) D) ≤ 2*volume
        {y | y ∈ closedBall (0 : Space n) D ∧ y+z ∈ good Λ p a r β (ENNReal.ofReal C)} := by
  let G := good Λ p a r β (ENNReal.ofReal C)
  have hG : MeasurableSet G := measurable_good Λ p a r β _
  let B := closedBall (0 : Space n) D
  let f : Space n → ℝ≥0∞ := Gᶜ.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hG.compl
  have hp (l : Λ) (y : Space n) : f (y+l.val) = f y := by
    simp only [f,G,Set.indicator_apply,Set.mem_compl_iff,periodic_good]
  let Z (z : Space n) : ℝ≥0∞ := ∫⁻ y in B,f (z+y)
  have hZ : Measurable Z := by
    apply Measurable.lintegral_prod_right
    exact hf.comp (measurable_fst.add measurable_snd)
  have hZint : ∫⁻ z,Z z ∂uniformWindow F ≤ volume B/100 := by
    rw [show (∫⁻ z,Z z ∂uniformWindow F) = volume B*∫⁻ z,f z ∂uniformWindow F from
      overlapping_windows Λ hF hF0 hFtop f hf hp]
    rw [lintegral_indicator hG.compl,lintegral_const,Measure.restrict_apply_univ,one_mul]

    calc
      _ ≤ volume B*(1/100) := by simpa only [mul_comm] using mul_le_mul_left hbad (volume B)
      _ = _ := by rw [mul_one_div]
  let := probability_window hF0 hFtop
  obtain ⟨z,hm,hz⟩ := slide (uniformWindow F)
    (field Λ p (countFn (closedBall (0 : Space n) L))) Z
    (measurable_field Λ p (measurable_const.indicator measurableSet_closedBall)) hZ
    (by exact_mod_cast hN.ne') (by finiteness) (measure_closedBall_pos volume (0 : Space n) hD).ne'
    (isCompact_closedBall (0 : Space n) D).measure_ne_top hcount hZint
  refine ⟨z,hm,?_⟩
  let Gz : Set (Space n) := {y | y+z ∈ G}
  have hGz : MeasurableSet Gz := hG.preimage (measurable_id.add_const z)
  have hzeq : Z z = volume (B \ Gz) := by
    have he : (fun y => f (z+y)) = Gzᶜ.indicator (fun _ => 1) := by
      funext y
      simp only [f,Gz,Set.indicator_apply,Set.mem_compl_iff,Set.mem_ofPred_eq,add_comm]
    change (∫⁻ y in B,f (z+y)) = _
    rw [he,lintegral_indicator hGz.compl,lintegral_const,Measure.restrict_restrict hGz.compl,
      Measure.restrict_apply_univ,one_mul,Set.inter_comm]
    rfl
  rw [hzeq] at hz
  have hsplit := measure_inter_add_sdiff (μ := (volume : Measure (Space n))) B hGz
  have hBfinite : volume B ≠ ∞ := (isCompact_closedBall (0 : Space n) D).measure_ne_top
  have hGoodf : volume (B∩Gz) ≠ ∞ := ne_top_of_le_ne_top hBfinite (measure_mono inter_subset_left)
  have hBadf : volume (B\Gz) ≠ ∞ := ne_top_of_le_ne_top hBfinite (measure_mono sdiff_subset)
  have hs := congrArg ENNReal.toReal hsplit
  rw [ENNReal.toReal_add hGoodf hBadf] at hs
  have hr := ENNReal.toReal_mono (by finiteness : volume B/2 ≠ ∞) hz
  rw [ENNReal.toReal_div] at hr
  norm_num only [ENNReal.toReal_ofNat] at hr
  apply (ENNReal.toReal_le_toReal hBfinite (by finiteness)).mp
  change (volume B).toReal ≤ (2*volume (B∩Gz)).toReal
  rw [ENNReal.toReal_mul]
  norm_num only [ENNReal.toReal_ofNat]
  linarith only [hs,hr]

theorem localize_oai {n : ℕ} {I : Type u_2} [Fintype I] (Λ : Submodule ℤ (Space n))
    [DiscreteTopology Λ] (p : I → Space n) {F : Set (Space n)}
    (hF : IsAddFundamentalDomain Λ F volume) (hF0 : volume F ≠ 0) (hFtop : volume F ≠ ∞)
    {a r β C D L h b t u : ℝ} (ha : 0 < a) (hD : 0 < D) (hh : 0 < h) (hC : 0 ≤ C)
    (hL : D+b ≤ L) (hbuf : u+Real.sqrt n*h/2 ≤ β)
    (hlip : (2*(n:ℝ)/a)*(Real.sqrt n*h/2) ≤ 1) {N : ℕ} (hN : 0 < N)
    (hbad : uniformWindow F (good Λ p a r β (ENNReal.ofReal C))ᶜ ≤ 1/100)
    (hcount : ∫⁻ z,field Λ p (countFn (closedBall (0 : Space n) L)) z ∂uniformWindow F ≤ (N:ℝ≥0∞)/40)
    (U : PoissonConfig.Config (SphericalLaw.Sphere n))
    (hcover : ∀ y,∃ (i : I) (l : Λ),y-p i-l.val ∈ RandomBody.body b t U) :
    ∃ (S : Finset (I×Λ)) (q : S → Space n), S.card ≤ N ∧
      (∀ i,q i ∈ alphabet n h (L+Real.sqrt n*h/2)) ∧
      volume (closedBall (0 : Space n) D) ≤ 2*volume
        (roundedGood q a D (r-Real.sqrt n*h/2) u (2*C)) ∧
      ∀ y ∈ closedBall (0 : Space n) D,∃ i,y-q i ∈
        RandomBody.body (b+Real.sqrt n*h/2) (t+Real.sqrt n*h/2) U := by
  obtain ⟨z,hm,hgood⟩ := window Λ p hF hF0 hFtop hD hN hbad hcount
  let S : Finset (I×Λ) := (finite_occurrences Λ p (B := closedBall z L) isBounded_closedBall).toFinset
  have hSmem (j : I×Λ) : j ∈ S ↔ ‖p j.1+j.2.val-z‖ ≤ L := by
    simp only [S,Set.Finite.mem_toFinset,mem_ofPred_eq,mem_closedBall,dist_eq_norm]
  let c (j : S) : Space n := p j.val.1+j.val.2.val-z
  let q (j : S) := rounded h (c j)
  have hc (j : S) : ‖c j‖ ≤ L := (hSmem j).mp j.property
  have hcard : S.card ≤ N := by
    have hs := finite_sum_le_field Λ p (countFn (closedBall (0 : Space n) L)) z S
    have he : ∑ j ∈ S,countFn (closedBall (0 : Space n) L) (z-p j.1-j.2.val) = (S.card:ℝ≥0∞) := by
      have hf (j : I×Λ) (hj : j ∈ S) : countFn (closedBall (0 : Space n) L) (z-p j.1-j.2.val) = 1 := by
        have hn : ‖z-p j.1-j.2.val‖ ≤ L := by
          rw [show z-p j.1-j.2.val = -(p j.1+j.2.val-z) by abel,norm_neg]
          exact (hSmem j).mp hj
        simp only [countFn,Set.indicator_of_mem (mem_closedBall_zero_iff.mpr hn)]
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using Finset.sum_congr rfl hf
    rw [he] at hs
    exact_mod_cast hs.trans hm
  have hsub : {y | y ∈ closedBall (0 : Space n) D ∧ y+z ∈ good Λ p a r β (ENNReal.ofReal C)} ⊆
      roundedGood q a D (r-Real.sqrt n*h/2) u (2*C) := by
    intro y hy
    exact good_transfer Λ p S z y ha hh hC hbuf hlip hy.1 hy.2
  refine ⟨S,q,hcard,(fun j => rounded_mem_alphabet hh (c j) (by linarith only [hc j])),
    hgood.trans (by gcongr),?_⟩
  apply rounding_cover c hh U b t D
  intro y hy
  obtain ⟨i,l,hl⟩ := hcover (y+z)
  have hres : ‖y+z-p i-l.val‖ ≤ b := mem_closedBall_zero_iff.mp hl.1
  have hm : (i,l) ∈ S := by
    apply (hSmem (i,l)).mpr
    calc
      ‖p i+l.val-z‖ = ‖y-(y+z-p i-l.val)‖ := by congr 1 ; abel
      _ ≤ ‖y‖+‖y+z-p i-l.val‖ := norm_sub_le _ _
      _ ≤ D+b := add_le_add (mem_closedBall_zero_iff.mp hy) hres
      _ ≤ L := hL
  refine ⟨⟨(i,l),hm⟩,?_⟩
  change y-(p i+l.val-z) ∈ RandomBody.body b t U
  rw [show y-(p i+l.val-z)=y+z-p i-l.val by abel]
  exact hl
end LocalizationComplete

end OAI
end

theorem solution.{u_2} : type_of% @OAI.LocalizationComplete.localize_oai.{u_2} := @OAI.LocalizationComplete.localize_oai.{u_2}
