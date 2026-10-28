-- Prove2me | solution 1 for OAI.PatternCross.fine
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T14:59:48.133657+00:00
-- url     : https://prove2.me/submissions/587cc1f6-f76c-4a7f-a29d-7c3bf4cf8854

import Mathlib
import Definitions.Def_OAIQ16Cd002
import Theorems.Thm_OAI_CapCost_clipped_cost
import Theorems.Thm_OAI_CapCost_raw_upper
import Theorems.Thm_OAI_SlotGeometry_ratio

section
-- module Solutions.OAIQ16_CD.Compat
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SphericalLaw
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

namespace SphericalLaw
open Set MeasureTheory Metric
open scoped ENNReal Pointwise

lemma cap_open {n : ℕ} (x : Space n) (t : ℝ) : IsOpen (cap x t) :=
  isOpen_lt continuous_const ((continuous_subtype_val.inner continuous_const).abs)

lemma positive_open {n : ℕ} [NeZero n] (U : Set (Sphere n))
    (hU : IsOpen U) (hne : U.Nonempty) : 0 < σ n U := by
  rw [σ, Measure.smul_apply, smul_eq_mul]
  apply ENNReal.mul_pos
  · exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  · exact hU.measure_ne_zero (volume : Measure (Space n)).toSphere hne

lemma cap_positive {n : ℕ} [NeZero n] (u : Sphere n) {t : ℝ} (ht : t < 1) :
    0 < σ n (cap u.val t) := by
  apply positive_open _ (cap_open _ _) ⟨u, ?_⟩
  change t < |inner ℝ u.val u.val|
  have hnorm : ‖u.val‖ = 1 := mem_sphere_zero_iff_norm.mp u.property
  simpa only [real_inner_self_eq_norm_sq, hnorm, one_pow, abs_one] using ht

end SphericalLaw

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_RadialShell
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

namespace RadialShell
open Filter
open scoped Topology

lemma inv_limit : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
lemma eta_limit : Tendsto η atTop (𝓝 0) := by
  unfold η
  simpa only [zero_pow (by norm_num : (4:ℕ) ≠ 0)] using inv_limit.pow 4
lemma log_div_limit : Tendsto (fun n : ℕ => Real.log n/(n:ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => Real.log x/x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  exact ht.comp tendsto_natCast_atTop_atTop
lemma low_limit (a : ℝ) : Tendsto (low a) atTop (𝓝 a) := by
  unfold low
  simpa using (((tendsto_const_nhds (x := (1:ℝ))).sub (log_div_limit.const_mul 10)).const_mul a).sub (eta_limit.const_mul 3)
lemma high_limit (a : ℝ) : Tendsto (high a) atTop (𝓝 a) := by
  unfold high
  simpa using (((tendsto_const_nhds (x := (1:ℝ))).add inv_limit).const_mul a).add (eta_limit.const_mul 3)

lemma n_eta {n : ℕ} (hn : 1 ≤ n) : (n:ℝ)*η n ≤ 1 := by
  have hnreal : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0:ℝ) < n := by linarith
  have hinv : (n:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hnreal
  have hinv0 : (0:ℝ) ≤ (n:ℝ)⁻¹ := inv_nonneg.mpr hnp.le
  have hpow : ((n:ℝ)⁻¹)^4 ≤ (n:ℝ)⁻¹ := by nlinarith [sq_nonneg ((n:ℝ)⁻¹),sq_nonneg (1-(n:ℝ)⁻¹),mul_le_mul_of_nonneg_left hinv hinv0, mul_le_mul_of_nonneg_right (pow_le_one₀ (n := 3) hinv0 hinv) hinv0]
  calc
    (n:ℝ)*η n ≤ (n:ℝ)*(n:ℝ)⁻¹ := mul_le_mul_of_nonneg_left hpow hnp.le
    _ = 1 := mul_inv_cancel₀ hnp.ne'

lemma thresholds {a l u : ℝ} (ha : 0 < a) (hl : l < 1/a) (hu : 1/a < u) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n → 2 ≤ n ∧ 1 ≤ Real.log n ∧
      a/2 ≤ low a n ∧ (n:ℝ)*η n ≤ 1 ∧
      ∀ r : ℝ,low a n ≤ r → r ≤ high a n →
        l ≤ (1+3*η n)/r ∧ (1+3*η n)/r ≤ u := by
  have hupper : Tendsto (fun n => (1+3*η n)/low a n) atTop (𝓝 (1/a)) := by
    convert ((tendsto_const_nhds (x := (1:ℝ))).add (eta_limit.const_mul 3)).div (low_limit a) ha.ne' using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | simp
  have hlower : Tendsto (fun n => (1+3*η n)/high a n) atTop (𝓝 (1/a)) := by
    convert ((tendsto_const_nhds (x := (1:ℝ))).add (eta_limit.const_mul 3)).div (high_limit a) ha.ne' using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | simp
  have hev : ∀ᶠ n : ℕ in atTop,2 ≤ n ∧ 1 ≤ Real.log n ∧ a/2 ≤ low a n ∧
      (1+3*η n)/low a n ≤ u ∧ l ≤ (1+3*η n)/high a n := by
    filter_upwards [eventually_ge_atTop 2,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1),
      (low_limit a).eventually_const_le (by linarith : a/2 < a),
      hupper.eventually_le_const hu,hlower.eventually_const_le hl] with n hn hlog hlo hup hdown
    exact ⟨hn,hlog,hlo,hup,hdown⟩
  obtain ⟨n₀,hn₀⟩ := eventually_atTop.mp hev
  refine ⟨n₀,?_⟩
  intro n hn
  obtain ⟨hn2,hlog,hlo,hup,hdown⟩ := hn₀ n hn
  refine ⟨hn2,hlog,hlo,n_eta (by omega),?_⟩
  intro r hr hrü
  have hlo0 : 0 < low a n := lt_of_lt_of_le (by linarith) hlo
  have hr0 : 0 < r := hlo0.trans_le hr
  have hnum : 0 ≤ 1+3*η n := by unfold η; positivity
  exact ⟨hdown.trans (div_le_div_of_nonneg_left hnum hr0 hrü),
    (div_le_div_of_nonneg_left hnum hlo0 hr).trans hup⟩

lemma weight_upper {n : ℕ} {a r : ℝ} (ha : 1 ≤ a)
    (hlog : 1 ≤ Real.log n) (_hr : 0 ≤ r) (hlo : low a n ≤ r)
    (hnη : (n:ℝ)*η n ≤ 1) :
    1+(n:ℝ)*max (1-r^2/a^2) 0 ≤ 27*Real.log n := by
  have hap : 0 < a := by linarith
  have hnpos : (0:ℝ) < n := by
    by_contra h
    have hz : n = 0 := by exact_mod_cast le_antisymm (le_of_not_gt h) (Nat.cast_nonneg n)
    simp [hz] at hlog
    norm_num at hlog
  have hx : a-r ≤ 10*a*(Real.log n/(n:ℝ))+3*η n := by
    dsimp [low] at hlo
    linarith only [hlo]
  have hq : max (1-r^2/a^2) 0 ≤ (20*Real.log n/(n:ℝ))+6*η n/a := by
    apply max_le _ (by unfold η; positivity)
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hap)).mp
    have hh := mul_le_mul_of_nonneg_left hx (by linarith : 0 ≤ 2*a)
    have hh2 : a^2-r^2 ≤ 2*a*(10*a*(Real.log n/(n:ℝ))+3*η n) := by
      nlinarith only [hh,sq_nonneg (a-r)]
    convert hh2 using 1 <;> (try field_simp [hap.ne'])
    all_goals first | rfl | ring
  have hh := mul_le_mul_of_nonneg_left hq hnpos.le
  have he : (n:ℝ)*(20*Real.log n/(n:ℝ)+6*η n/a) = 20*Real.log n+6*((n:ℝ)*η n)/a := by field_simp
  rw [he] at hh
  have hdiv : ((n:ℝ)*η n)/a ≤ 1 := (div_le_one hap).mpr (hnη.trans ha)
  rw [mul_div_assoc 6] at hh
  linarith only [hh,hdiv,hlog]

end RadialShell

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapCost
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

namespace CapCost
open MeasureTheory SphericalLaw CapGeometry CapAffinity
open scoped ENNReal NNReal

lemma intensity_real {n : ℕ} (e : Sphere n) (t : ℝ) (E : Set (Sphere n)) :
    (intensity e t).real E = (σ n).real E/(σ n).real (cap e.val t) := by
  change (((rate e t : ℝ≥0∞)*(σ n) E).toReal) = _
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal]
  change ((σ n).real (cap e.val t))⁻¹ * (σ n).real E = _
  ring

lemma cap_real_pos {n : ℕ} [NeZero n] (e : Sphere n) {t : ℝ} (ht : t < 1) :
    0 < (σ n).real (cap e.val t) :=
  ENNReal.toReal_pos (ne_of_gt (cap_positive e ht)) (measure_ne_top _ _)

end CapCost

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_MatchingBounds
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

universe u_1 u_2

namespace MatchingBounds
open CellMatching
open scoped Classical BigOperators
variable {I : Type u_1} {J : Type u_2} [Fintype I] [Fintype J]

lemma all_matchings_eq (w : I × J → ℝ) :
    (∑ M : Matching I J, ∏ e ∈ M.val, w e) =
    1 + ∑ M : Matching I J, if M.val.Nonempty then ∏ e ∈ M.val, w e else 0 := by
  have ht (M : Matching I J) : (∏ e ∈ M.val, w e) =
      (if M.val.Nonempty then ∏ e ∈ M.val, w e else 0) +
      (if M = emptyMatching then 1 else 0) := by
    by_cases he : M.val = ∅
    · have hM : M = emptyMatching := Subtype.ext he
      simp [hM, emptyMatching]
    · have hne := Finset.nonempty_iff_ne_empty.mpr he
      have hM : M ≠ emptyMatching := fun h => he (congrArg Subtype.val h)
      simp only [ite_eq_left hne, ite_eq_right hM, add_zero]
  conv_lhs => arg 2; ext M; rw [ht M]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

lemma all_matchings_le_product (w : I × J → ℝ) (hw : ∀ e, 0 ≤ w e) :
    (∑ M : Matching I J, ∏ e ∈ M.val, w e) ≤ ∏ e, (1+w e) := by
  rw [Finset.prod_one_add]
  let s := Finset.univ.image (Subtype.val : Matching I J → Finset (I × J))
  have hs : (∑ M : Matching I J, ∏ e ∈ M.val, w e) = ∑ M ∈ s, ∏ e ∈ M, w e := by
    dsimp only [s]
    rw [Finset.sum_image]
    intro M _ N _ h
    exact Subtype.ext h
  rw [hs]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (fun M _ => Finset.mem_powerset.mpr (Finset.subset_univ _))
    (fun M _ _ => Finset.prod_nonneg (fun e _ => hw e))

lemma cross_matching_bound (w : I × J → ℝ) (hw : ∀ e, 0 ≤ w e) :
    (∑ M : Matching I J, if M.val.Nonempty then ∏ e ∈ M.val, w e else 0) ≤
      Real.exp (∑ e, w e) - 1 := by
  have h := all_matchings_le_product w hw
  rw [all_matchings_eq] at h
  have hp : (∏ e, (1+w e)) ≤ Real.exp (∑ e, w e) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod
    · exact fun e _ => by linarith [hw e]
    · intro e _
      simpa only [add_comm] using Real.add_one_le_exp (w e)
  linarith

end MatchingBounds

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_DiagramCrossBounds
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

universe u_1 u_2 u_3

namespace PoissonDiagrams
open MeasureTheory CellMatching MatchingBounds
open scoped Classical BigOperators
variable {Ω : Type u_1} {I : Type u_2} {J : Type u_3} [MeasurableSpace Ω] [Fintype I] [Fintype J]

lemma cross_bound (μ : Measure Ω) (E : I → Set Ω) (F : J → Set Ω) :
    diagram μ E F ≤ (∏ i, μ.real (E i))*(∏ j, μ.real (F j)) *
      (Real.exp (∑ i, ∑ j, μ.real (E i ∩ F j)/(μ.real (E i)*μ.real (F j))) - 1) := by
  unfold diagram
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Fintype.sum_prod_type] using cross_matching_bound
    (fun e : I × J => μ.real (E e.1 ∩ F e.2)/(μ.real (E e.1)*μ.real (F e.2)))
    (fun e => by positivity)

end PoissonDiagrams

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_RadialCost
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

namespace RadialCost

lemma weight_ge_one (n : ℕ) (a r : ℝ) : 1 ≤ weight n a r := by
  unfold weight
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) (le_max_right _ _))

lemma radial_deficit {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) :
    a-r ≤ a*max (1-r^2/a^2) 0 := by
  by_cases h : r ≤ a
  · have haa : 0 < a^2 := sq_pos_of_pos ha
    have hr2 : r^2 ≤ a^2 := (sq_le_sq₀ hr ha.le).mpr h
    rw [max_eq_left (by exact sub_nonneg.mpr ((div_le_one haa).mpr hr2))]
    apply (mul_le_mul_iff_right₀ ha).mp
    field_simp
    nlinarith only [sq_nonneg (a-r),mul_nonneg hr (sub_nonneg.mpr h)]
  · have hq := mul_nonneg ha.le (le_max_right (1-r^2/a^2) 0)
    linarith only [hq,le_of_not_ge h]

lemma upper_threshold {n : ℕ} {a r η : ℝ} (ha : 1 ≤ a) (hr : a/2 ≤ r)
    (hη : 0 ≤ η) (hnη : (n:ℝ)*η ≤ 1) :
    (n:ℝ)*max ((1+3*η)/r-1/a) 0 ≤ (8/a)*weight n a r := by
  have hap : 0 < a := by linarith
  have hrp : 0 < r := by linarith
  let q := max (1-r^2/a^2) 0
  have hq : 0 ≤ q := le_max_right _ _
  have hd : a-r ≤ a*q := radial_deficit hap hrp.le
  have ht : (1+3*η)/r-1/a ≤ (2*q+6*η)/a := by
    apply (le_div_iff₀ hap).mpr
    rw [show ((1+3*η)/r-1/a)*a = ((1+3*η)*a-r)/r by field_simp]
    apply (div_le_iff₀ hrp).mpr
    have hh := mul_nonneg (sub_nonneg.mpr hr) (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hq) (mul_nonneg (by norm_num : (0:ℝ) ≤ 6) hη))
    nlinarith only [hd,hh]
  have ht0 : 0 ≤ (2*q+6*η)/a := by positivity
  have hh := mul_le_mul_of_nonneg_left (max_le ht ht0) (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hw : 0 ≤ (n:ℝ)*q := mul_nonneg (Nat.cast_nonneg n) hq
  calc
    _ ≤ (n:ℝ)*((2*q+6*η)/a) := hh
    _ = (2*((n:ℝ)*q)+6*((n:ℝ)*η))/a := by ring
    _ ≤ (2*((n:ℝ)*q)+6)/a := div_le_div_of_nonneg_right (by linarith only [hnη]) hap.le
    _ ≤ (8/a)*weight n a r := by
      change (2*((n:ℝ)*q)+6)/a ≤ (8/a)*(1+(n:ℝ)*q)
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (by linarith only [hw]) hap.le

lemma lower_threshold {n : ℕ} {a r η : ℝ} (hn : 0 < n) (ha : 1 ≤ a)
    (hr : a/2 ≤ r) (hη : 0 ≤ η) (hnη : (n:ℝ)*η ≤ 1)
    (hru : r ≤ a*(1+1/(n:ℝ))+3*η) :
    (n:ℝ)*max (1/a-(1+3*η)/r) 0 ≤ 8 := by
  have hap : 0 < a := by linarith
  have hrp : 0 < r := by linarith
  have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
  have hu : (n:ℝ)*(r-a) ≤ a+3 := by
    have h := mul_le_mul_of_nonneg_left hru hnp.le
    field_simp at h
    nlinarith only [h,hnη]
  have ht : (n:ℝ)*(1/a-(1+3*η)/r) ≤ 8 := by
    apply (mul_le_mul_iff_right₀ (mul_pos hap hrp)).mp
    field_simp
    have hp := mul_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) (mul_nonneg hap.le hη)
    have har := mul_le_mul_of_nonneg_left hr hap.le
    nlinarith only [hu,hp,har,ha,sq_nonneg (a-1)]
  rw [mul_max_of_nonneg _ _ hnp.le,mul_zero]
  exact max_le ht (by norm_num)

end RadialCost

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_ShellCaps
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

namespace ShellCaps
open Set MeasureTheory SphericalLaw CapCost
open scoped BigOperators

lemma A_pos {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) (hu : u < 1) : 0 < A l u := by
  have hu0 : 0 < u := hl.trans_le hlu
  have hsq : 0 < 1-u^2 := by nlinarith only [hu0,hu]
  unfold A
  positivity

lemma C_pos {a l u : ℝ} (ha : 0 < a) (hl : 0 < l) (hlu : l ≤ u) (hu : u < 1) : 0 < C a l u := by
  have hA := A_pos hl hlu hu
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold C
  positivity

lemma shell_cost {a l u : ℝ} (ha : 1 ≤ a) (hl : 0 < l) (hlt : l < 1/a)
    (hu : 1/a < u) (hu1 : u < 1) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n],
    ∀ (e f : Sphere n) (r : ℝ),RadialShell.low a n ≤ r → r ≤ RadialShell.high a n →
    let μ := intensity e (1/a)
    let E := cap f.val ((1+3*RadialShell.η n)/r)
    l ≤ (1+3*RadialShell.η n)/r ∧ (1+3*RadialShell.η n)/r ≤ u ∧
    μ.real E ≤ Real.exp (8*A l u) ∧
    -Real.log (min (μ.real E) (1/2)) ≤ C a l u*RadialCost.weight n a r ∧
    -Real.log (min (μ.real E) (1/2)) ≤ (27*C a l u)*Real.log n ∧
    Real.exp (-(27*C a l u)*Real.log n) ≤ min (μ.real E) (1/2) := by
  have hap : 0 < a := by linarith only [ha]
  have hA : 0 < A l u := A_pos hl (hlt.le.trans hu.le) hu1
  have hC : 0 < C a l u := C_pos hap hl (hlt.le.trans hu.le) hu1
  obtain ⟨n₀,hn₀⟩ := RadialShell.thresholds hap hlt hu
  refine ⟨n₀,?_⟩
  intro n hn _ e f r hlo hhi
  obtain ⟨hn2,hlog,hlow,hnη,hτ⟩ := hn₀ n hn
  obtain ⟨hτl,hτu⟩ := hτ r hlo hhi
  have hr : a/2 ≤ r := hlow.trans hlo
  have hr0 : 0 < r := lt_of_lt_of_le (by linarith only [hap]) hr
  have hη : 0 ≤ RadialShell.η n := by unfold RadialShell.η; positivity
  have htlo := RadialCost.lower_threshold (by omega : 0 < n) ha hr hη hnη (by simpa [RadialShell.high,one_div] using hhi)
  have hthi := RadialCost.upper_threshold ha hr hη hnη
  let μ := intensity e (1/a)
  let E := cap f.val ((1+3*RadialShell.η n)/r)
  have hraw : μ.real E ≤ Real.exp (8*A l u) := by
    apply (raw_upper e f hl hu1 hlt.le hu.le hτl hτu).trans
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left htlo hA.le
    dsimp [A] at hh ⊢
    nlinarith only [hh]
  have hcost : -Real.log (min (μ.real E) (1/2)) ≤ C a l u*RadialCost.weight n a r := by
    have hc := clipped_cost e f hl hu1 hlt.le hu.le hτl hτu
    have hh := mul_le_mul_of_nonneg_left hthi hA.le
    have hw := mul_le_mul_of_nonneg_left (RadialCost.weight_ge_one n a r)
      (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
    dsimp [C,A] at hh ⊢
    dsimp [μ,E]
    linear_combination hc+hh+hw
  have hcost' : -Real.log (min (μ.real E) (1/2)) ≤ (27*C a l u)*Real.log n := by
    have hw := mul_le_mul_of_nonneg_left (RadialShell.weight_upper ha hlog hr0.le hlo hnη) hC.le
    apply hcost.trans
    dsimp [RadialCost.weight]
    nlinarith only [hw]
  have hpos : 0 < min (μ.real E) (1/2) := by
    apply lt_min _ (by norm_num)
    rw [show μ.real E = (σ n).real E/(σ n).real (cap e.val (1/a)) from intensity_real e _ _]
    exact div_pos (cap_real_pos f (hτu.trans_lt hu1)) (cap_real_pos e (hu.trans hu1))
  refine ⟨hτl,hτu,hraw,hcost,hcost',?_⟩
  calc
    _ ≤ Real.exp (Real.log (min (μ.real E) (1/2))) := Real.exp_le_exp.mpr (by linarith only [hcost'])
    _ = _ := Real.exp_log hpos

end ShellCaps

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SlotGeometry
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

namespace SlotGeometry
open Set MeasureTheory SphericalLaw CapCost ProjectiveCaps
open scoped BigOperators

lemma decay {n : ℕ} {c K P C H α : ℝ} (hn : 2 ≤ n) (hlog : 0 ≤ Real.log n)
    (hc : 0 < c) (hC : 0 ≤ C) (hCn : C ≤ n) (hH : 0 ≤ H)
    (hHsq : 2*K+P+9 ≤ c*H^2) (hα : H*Real.sqrt (Real.log n/(n:ℝ)) ≤ α) :
    C*Real.exp ((2*K+P)*Real.log n-(n:ℝ)*c*α^2) ≤ (n:ℝ)⁻¹^8 := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0:ℝ) < n := by linarith only [hnR]
  have hs := Real.sq_sqrt (div_nonneg hlog hnp.le)
  have hα0 : 0 ≤ α := (mul_nonneg hH (Real.sqrt_nonneg _)).trans hα
  have hαsq := (sq_le_sq₀ (mul_nonneg hH (Real.sqrt_nonneg _)) hα0).mpr hα
  have hh : H^2*(Real.log n/(n:ℝ)) ≤ α^2 := by nlinarith only [hαsq,hs]
  have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg hnp.le hc.le)
  have heq : (n:ℝ)*c*(H^2*(Real.log n/(n:ℝ))) = (c*H^2)*Real.log n := by field_simp
  rw [heq] at hm
  have hb := mul_le_mul_of_nonneg_right hHsq hlog
  have he : (2*K+P)*Real.log n-(n:ℝ)*c*α^2 ≤ -9*Real.log n := by linarith only [hb,hm]
  have hp : Real.exp (-9*Real.log n) = (n:ℝ)⁻¹^9 := by
    rw [show -9*Real.log n = -(9*Real.log n) by ring,Real.exp_neg,show (9:ℝ) = (9:ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log hnp,inv_pow]
  calc
    _ ≤ C*Real.exp (-9*Real.log n) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hC
    _ = C*(n:ℝ)⁻¹^9 := by rw [hp]
    _ ≤ (n:ℝ)*(n:ℝ)⁻¹^9 := mul_le_mul_of_nonneg_right hCn (by positivity)
    _ = _ := by field_simp

end SlotGeometry

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_ResidualCaps
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

namespace ResidualCaps
open Set Metric SphericalLaw

lemma cap_unit {n : ℕ} (x : Space n) (hx : x ≠ 0) (t : ℝ) :
    cap (unit x hx).val (t/‖x‖) = cap x t := by
  ext u
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  simp only [cap,unit,mem_ofPred_eq,inner_smul_right,abs_mul,abs_inv,abs_of_nonneg (norm_nonneg x)]
  rw [mul_comm,← div_eq_mul_inv,div_lt_div_iff_of_pos_right hn]

lemma angle_unit {n : ℕ} (x y : Space n) (hx : x ≠ 0) (hy : y ≠ 0) :
    ProjectiveCaps.angle (unit x hx).val (unit y hy).val = ProjectiveCaps.angle x y := by
  have hnx : 0 < ‖x‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hx)
  have hny : 0 < ‖y‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hy)
  simp only [unit,ProjectiveCaps.angle,InnerProductGeometry.angle_smul_left_of_pos _ _ hnx,
    ← smul_neg,InnerProductGeometry.angle_smul_right_of_pos _ _ hny]

end ResidualCaps

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PatternWitness
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

universe u_1 u_2 u_3

namespace PatternWitness
open Set Metric MeasureTheory SphericalLaw PatternGeometry ResidualCaps PoissonDiagrams CapCost
open scoped BigOperators Classical

lemma separated {n : ℕ} {J : Type u_3} [Fintype J] (p : J → Space n)
    {x y : Space n} {L t r : ℝ} (hr : 0 < r)
    (hx : ∀ j,r ≤ ‖x-p j‖) (hy : ∀ j,r ≤ ‖y-p j‖)
    (hsep : (x,y) ∉ TargetGeometry.bad p L t)
    (i : relevant p L x) (j : relevant p L y) :
    t < ProjectiveCaps.angle (x-p i) (y-p j) := by
  by_contra h
  apply hsep
  apply mem_iUnion.mpr ⟨i.val,?_⟩
  apply mem_iUnion.mpr ⟨j.val,?_⟩
  exact ⟨norm_pos_iff.mp (hr.trans_le (hx i)),(Finset.mem_filter.mp i.property).2,
    norm_pos_iff.mp (hr.trans_le (hy j)),(Finset.mem_filter.mp j.property).2,le_of_not_gt h⟩
end PatternWitness

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CrossDeployment
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

namespace CrossDeployment
open Set MeasureTheory SphericalLaw CapCost ProjectiveCaps
open scoped BigOperators

theorem fine {a l u₀ u K : ℝ} (ha : 1 < a) (hl : 0 < l) (hlt : l < 1/a)
    (hu₀ : 1/a < u₀) (hu : u₀ < u) (hu1 : u < 1) (hK : 0 ≤ K) :
    ∃ H : ℝ,0 < H ∧ ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n],
    ∀ (e f g : Sphere n) (r s : ℝ),
    RadialShell.low a n ≤ r → r ≤ RadialShell.high a n →
    RadialShell.low a n ≤ s → s ≤ RadialShell.high a n →
    ∀ E F : Set (Sphere n),
    E ⊆ cap f.val ((1+3*RadialShell.η n)/r) →
    F ⊆ cap g.val ((1+3*RadialShell.η n)/s) →
    Real.exp (-K*Real.log n)*min ((intensity e (1/a)).real (cap f.val ((1+3*RadialShell.η n)/r))) (1/2) ≤ (intensity e (1/a)).real E →
    Real.exp (-K*Real.log n)*min ((intensity e (1/a)).real (cap g.val ((1+3*RadialShell.η n)/s))) (1/2) ≤ (intensity e (1/a)).real F →
    H*Real.sqrt (Real.log n/(n:ℝ)) ≤ angle f.val g.val →
    (intensity e (1/a)).real (E ∩ F)/((intensity e (1/a)).real E*(intensity e (1/a)).real F) ≤ (n:ℝ)⁻¹^8 := by
  have hap : 0 < a := lt_trans (by norm_num) ha
  have hlu : l ≤ u₀ := hlt.le.trans hu₀.le
  have hu₀1 : u₀ < 1 := hu.trans hu1
  let k := min (l/16) ((u-u₀)/4)
  have hk : 0 < k := lt_min (by positivity) (by positivity)
  let c := 2*l*k/Real.pi^2
  have hc : 0 < c := by dsimp [c]; positivity
  let V := Real.exp (8*ShellCaps.A l u₀)
  have hV : 1 ≤ V := Real.one_le_exp (by
    have := ShellCaps.A_pos hl hlu hu₀1
    positivity)
  let P := 27*ShellCaps.C a l u₀
  have hP : 0 < P := mul_pos (by norm_num) (ShellCaps.C_pos hap hl hlu hu₀1)
  let H := Real.sqrt ((2*K+P+9)/c)
  have hH : 0 < H := Real.sqrt_pos.mpr (div_pos (by linarith) hc)
  have hHsq : 2*K+P+9 ≤ c*H^2 := by
    dsimp [H]
    rw [Real.sq_sqrt (by positivity)]
    exact le_of_eq (by field_simp)
  obtain ⟨nS,hnS⟩ := ShellCaps.shell_cost ha.le hl hlt hu₀ hu₀1
  obtain ⟨nD,hnD⟩ := exists_nat_ge (max (4*V) (2*(1/l+1/(1-u^2))/l))
  refine ⟨H,hH,max nS (max nD 2),?_⟩
  intro n hn _ e f g r s hrl hrh hsl hsh E F hE hF he hf hangle
  have hn2 : 2 ≤ n := (le_max_right nD 2).trans ((le_max_right nS _).trans hn)
  have hnS' : nS ≤ n := (le_max_left _ _).trans hn
  have hnD' : nD ≤ n := (le_max_left nD 2).trans ((le_max_right nS _).trans hn)
  have hnd : (nD:ℝ) ≤ n := by exact_mod_cast hnD'
  have hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l := by
    exact (div_le_iff₀ hl).mp ((le_max_right _ _).trans (hnD.trans hnd))
  have hnV : 4*V ≤ (n:ℝ) := (le_max_left _ _).trans (hnD.trans hnd)
  have hr := hnS n hnS' e f r hrl hrh
  have hs := hnS n hnS' e g s hsl hsh
  have hratio := SlotGeometry.ratio e f g hl hu1 (by positivity : 0 ≤ 1/a)
    ((div_lt_one hap).mpr ha) hr.1 hr.2.1 hs.1 hs.2.1 hu.le hk.le
    (min_le_left _ _) (by have := min_le_right (l/16) ((u-u₀)/4); dsimp [k] at *; linarith)
    hdim hV hE hF hr.2.2.1 hs.2.2.1 hr.2.2.2.2.2 hs.2.2.2.2.2 he hf
  exact hratio.trans (SlotGeometry.decay hn2 (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega)))
    hc (by positivity : 0 ≤ 4*V) hnV hH.le hHsq hangle)

end CrossDeployment

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CrossDiagram
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

universe u_1 u_2 u_3

namespace CrossDiagram
open MeasureTheory PoissonDiagrams
open scoped BigOperators

lemma small {Ω : Type u_1} {I : Type u_2} {J : Type u_3} [MeasurableSpace Ω] [Fintype I] [Fintype J]
    {n : ℕ} (hn : 0 < n) (μ : Measure Ω) (E : I → Set Ω) (F : J → Set Ω)
    (hI : Fintype.card I ≤ n^2) (hJ : Fintype.card J ≤ n^2)
    (hsmall : ∀ i j,μ.real (E i ∩ F j)/(μ.real (E i)*μ.real (F j)) ≤ (n:ℝ)⁻¹^8) :
    diagram μ E F ≤ (∏ i,μ.real (E i))*(∏ j,μ.real (F j))*(Real.exp ((n:ℝ)⁻¹^4)-1) := by
  have hI' : (Fintype.card I:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast hI
  have hJ' : (Fintype.card J:ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast hJ
  have hprod := mul_le_mul hI' hJ' (Nat.cast_nonneg _) (sq_nonneg (n:ℝ))
  have hsum : ∑ i,∑ j,μ.real (E i ∩ F j)/(μ.real (E i)*μ.real (F j)) ≤ (n:ℝ)⁻¹^4 := by
    calc
      _ ≤ ∑ _i : I,∑ _j : J,(n:ℝ)⁻¹^8 := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hsmall i j
      _ = ((Fintype.card I:ℝ)*(Fintype.card J:ℝ))*(n:ℝ)⁻¹^8 := by simp; ring
      _ ≤ (((n:ℝ)^2)*((n:ℝ)^2))*(n:ℝ)⁻¹^8 := mul_le_mul_of_nonneg_right hprod (by positivity)
      _ = _ := by
        have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
        field_simp

  exact (cross_bound μ E F).trans (mul_le_mul_of_nonneg_left
    (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1) (by positivity))

lemma exp_small {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : Real.exp x-1 ≤ 2*x := by
  have hb := Real.norm_exp_sub_one_sub_id_le (x := x) (by simpa [Real.norm_of_nonneg hx] using hx1)
  have h := le_trans (le_abs_self (Real.exp x-1-x)) (by simpa [Real.norm_eq_abs,abs_of_nonneg hx] using hb)
  nlinarith only [h,mul_nonneg hx (sub_nonneg.mpr hx1)]

lemma inverse_scale {n : ℕ} (hn : 2 ≤ n) : Real.exp ((n:ℝ)⁻¹^4)-1 ≤ (n:ℝ)⁻¹^3 := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith only [hn']
  have h1 : (n:ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith only [hn'])
  have h0 : 0 ≤ (n:ℝ)⁻¹ := inv_nonneg.mpr hn0.le
  apply (exp_small (pow_nonneg h0 _) (pow_le_one₀ h0 h1)).trans
  have hi : 2*(n:ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one hn0).mpr hn'
  calc
    _ = (2*(n:ℝ)⁻¹)*((n:ℝ)⁻¹^3) := by ring
    _ ≤ 1*((n:ℝ)⁻¹^3) := mul_le_mul_of_nonneg_right hi (by positivity)
    _ = _ := one_mul _
end CrossDiagram

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PatternCross
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

universe u_1 u_2 u_3

namespace PatternCross
open Set MeasureTheory SphericalLaw CapCost PatternGeometry PatternWitness ResidualCaps PoissonDiagrams
open scoped BigOperators

theorem fine_oai {a l u₀ u K : ℝ} (ha : 1 < a) (hl : 0 < l) (hlt : l < 1/a)
    (hu₀ : 1/a < u₀) (hu : u₀ < u) (hu1 : u < 1) (hK : 0 ≤ K) :
    ∃ H : ℝ,0 < H ∧ ∃ n₀ : ℕ,∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n],
    ∀ {J : Type u_2} [Fintype J] (e : Sphere n) (p : J → Space n) (x y : Space n) (D A C : ℝ),
    0 < RadialShell.low a n →
    x ∈ roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C →
    y ∈ roundedGood p a D (RadialShell.low a n) (RadialShell.high a n) C →
    (x,y) ∉ TargetGeometry.bad p (RadialShell.high a n) (H*Real.sqrt (Real.log n/(n:ℝ))) →
    ∀ (W : Certificate e p x a K A C) (V : Certificate e p y a K A C),
    diagram (intensity e (1/a)) W.slot V.slot ≤ (n:ℝ)⁻¹^3*activity W*activity V := by
  obtain ⟨H,hH,n₀,hn₀⟩ := CrossDeployment.fine ha hl hlt hu₀ hu hu1 hK
  refine ⟨H,hH,max n₀ 2,?_⟩
  intro n hn _ J _ e p x y D A C hlo hx hy hsep W V
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hratio : ∀ S T,(intensity e (1/a)).real (W.slot S ∩ V.slot T)/
      ((intensity e (1/a)).real (W.slot S)*(intensity e (1/a)).real (V.slot T)) ≤ (n:ℝ)⁻¹^8 := by
    intro S T
    let i := W.anchor S
    let j := V.anchor T
    have hx0 : x-p i ≠ 0 := norm_pos_iff.mp (hlo.trans_le (hx.2.1 i))
    have hy0 : y-p j ≠ 0 := norm_pos_iff.mp (hlo.trans_le (hy.2.1 j))
    apply hn₀ n ((le_max_left _ _).trans hn) e (unit (x-p i) hx0) (unit (y-p j) hy0)
      ‖x-p i‖ ‖y-p j‖ (hx.2.1 i) (Finset.mem_filter.mp i.property).2
      (hy.2.1 j) (Finset.mem_filter.mp j.property).2 (W.slot S) (V.slot T)
    · rw [cap_unit]; exact W.subset_cap S
    · rw [cap_unit]; exact V.subset_cap T
    · rw [cap_unit]; exact W.thinned S
    · rw [cap_unit]; exact V.thinned T
    · rw [angle_unit]
      exact (separated p hlo hx.2.1 hy.2.1 hsep i j).le
  have hcross := CrossDiagram.small (by omega : 0 < n) (intensity e (1/a)) W.slot V.slot
    (by simpa using W.card_le) (by simpa using V.card_le) hratio
  apply hcross.trans
  have hprod : 0 ≤ activity W*activity V :=
    mul_nonneg (Finset.prod_nonneg fun S _ => (W.positive S).le)
      (Finset.prod_nonneg fun S _ => (V.positive S).le)
  have hh := mul_le_mul_of_nonneg_left (CrossDiagram.inverse_scale hn2) hprod
  simpa only [activity,mul_assoc,mul_comm,mul_left_comm] using hh

end PatternCross

end OAI
end

theorem solution.{u_2} : type_of% @OAI.PatternCross.fine_oai.{u_2} := @OAI.PatternCross.fine_oai.{u_2}
