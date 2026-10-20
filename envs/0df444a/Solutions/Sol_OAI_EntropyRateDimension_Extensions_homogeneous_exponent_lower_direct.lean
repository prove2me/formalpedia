-- Prove2me | solution 1 for OAI.EntropyRateDimension.Extensions.homogeneous_exponent_lower_direct
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T15:46:49.371985+00:00
-- url     : https://prove2.me/submissions/891e78f0-dba3-4c02-8dd3-94a78927e077

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/HomogeneousDimension.lean:L11-L30
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Extensions.homogeneous_exponent_lower_direct. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Model
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TailConvolution__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteVariance__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordAverage__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_EntropyBudget__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RetainedLoss__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairBands__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowCount__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowGain__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Main__SelfSimilarCorollaries
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_NoOverlaps

-- ---- from OAI.MeasureTheory.SelfSimilar.Basic ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace System
variable {ι : Type uι} [Fintype ι]

theorem affine_continuous (S : System ι) (i : ι) : Continuous (S.affine i) := by
  unfold affine
  fun_prop

theorem mapMass_nonneg (S : System ι) (n : ℕ) (g : ℝ × ℝ) :
    0 ≤ S.mapMass n g := by
  classical
  exact Finset.sum_nonneg (fun w _ => (S.wordWeight_pos w).le)

theorem mapMass_le_one (S : System ι) (n : ℕ) (g : ℝ × ℝ) :
    S.mapMass n g ≤ 1 := by
  classical
  rw [mapMass, ← S.wordWeight_sum n]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun w _ _ => (S.wordWeight_pos w).le)

theorem walkEntropy_nonneg (S : System ι) (n : ℕ) : 0 ≤ S.walkEntropy n := by
  apply div_nonneg _ (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  apply Finset.sum_nonneg
  intro g _
  exact Real.negMulLog_nonneg (S.mapMass_nonneg n g) (S.mapMass_le_one n g)

theorem entropyRate_le (S : System ι) (n : ℕ) :
    S.entropyRate ≤ S.walkEntropy (n + 1) / (n + 1 : ℕ) := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact div_nonneg (S.walkEntropy_nonneg _) (by positivity)
  · exact ⟨n, rfl⟩

theorem lyapunov_pos [Nonempty ι] (S : System ι) : 0 < S.lyapunov := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [lyapunov, neg_pos]
  apply Finset.sum_neg
  · intro i _
    exact mul_neg_of_pos_of_neg (S.weight_pos i)
      (div_neg_of_neg_of_pos (Real.log_neg (S.ratio_pos i) (S.ratio_lt_one i)) hlog)
  · exact Finset.univ_nonempty

end System

namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem selfSimilar_apply (S : System ι) (μ : Measure ℝ) (hμ : S.SelfSimilar μ)
    {E : Set ℝ} (hE : MeasurableSet E) :
    μ E = ∑ i, ENNReal.ofReal (S.weight i) * μ ((S.affine i) ⁻¹' E) := by
  classical
  conv_lhs => rw [hμ]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (S.affine_continuous _).measurable hE]

theorem selfSimilar_compact (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) : ∃ B : ℝ, 0 < B ∧ μ (Set.Icc (-B) B)ᶜ = 0 := by
  classical
  obtain ⟨c,T,hc,hc1,hT,hr,ht⟩ := S.exists_uniform_bounds
  let R := T/(1-c)
  have hR : 0 ≤ R := div_nonneg hT (sub_pos.mpr hc1).le
  have hRc : c*R+T = R := by
    dsimp only [R]
    field_simp [ne_of_gt (sub_pos.mpr hc1)]
    ring
  let a : ℕ → ℝ := fun n => R+(1/c)^n
  let E : ℕ → Set ℝ := fun n => {x | a n < |x|}
  have ha : ∀ n, c*a (n+1)+T = a n := by
    intro n
    dsimp only [a]
    rw [pow_succ]
    field_simp
    nlinarith [hRc]
  have hcInv : 1 < 1/c := (one_lt_div hc).mpr hc1
  have hm : Antitone E := by
    intro n m hnm x hx
    have hp := pow_le_pow_right₀ hcInv.le hnm
    change R+(1/c)^m < |x| at hx
    change R+(1/c)^n < |x|
    linarith
  have hE : ∀ n, MeasurableSet (E n) := fun n => measurableSet_lt measurable_const measurable_abs
  have hpre : ∀ n i, S.affine i ⁻¹' E n ⊆ E (n+1) := by
    intro n i x hx
    have hb : |S.affine i x| ≤ c*|x|+T := calc
      _ ≤ |S.ratio i*x|+|S.offset i| := abs_add_le _ _
      _ ≤ c*|x|+T := by rw [abs_mul]; exact add_le_add (mul_le_mul_of_nonneg_right (hr i) (abs_nonneg x)) (ht i)
    change a n < |S.affine i x| at hx
    change a (n+1) < |x|
    nlinarith [ha n]
  have hinc : ∀ n, μ (E n) ≤ μ (E (n+1)) := by
    intro n
    rw [S.selfSimilar_apply μ hμ (hE n)]
    calc
      _ ≤ ∑ i, ENNReal.ofReal (S.weight i)*μ (E (n+1)) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul' le_rfl (measure_mono (hpre n i)))
      _ = μ (E (n+1)) := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => S.weight_nonneg i), S.weight_sum,
          ENNReal.ofReal_one, one_mul]
  have hzero : (⋂ n, E n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hpow := (tendsto_pow_atTop_atTop_of_one_lt hcInv).eventually
      (Filter.eventually_gt_atTop (|x|-R))
    obtain ⟨n,hn⟩ := hpow.exists
    have he := Set.mem_iInter.mp hx n
    change R+(1/c)^n < |x| at he
    linarith
  have hlim := tendsto_measure_iInter_atTop (fun n => (hE n).nullMeasurableSet) hm
    ⟨0, measure_ne_top μ (E 0)⟩
  rw [hzero, measure_empty] at hlim
  have hb : ∀ n, μ (E 0) ≤ μ (E n) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => exact ih.trans (hinc n)
  have hz : μ (E 0) = 0 := le_antisymm (ge_of_tendsto' hlim hb) bot_le
  refine ⟨R+1, by linarith, ?_⟩
  have heq : (Set.Icc (-(R+1)) (R+1))ᶜ = E 0 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Icc, E, a, pow_zero, Set.mem_ofPred_eq,
      ← abs_le, not_le]
  rw [heq, hz]

end System

theorem binaryEntropy_quadratic_concave :
    ConcaveOn ℝ (Set.Icc 0 1) (fun x : ℝ => Real.binEntropy x+2*x^2) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := fun x =>
    Real.log (1-x)-Real.log x+4*x) (f'' := fun x => -(1-x)⁻¹-x⁻¹+4)
    (convex_Icc 0 1) (Real.binEntropy_continuous.add (by fun_prop)).continuousOn
  · intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    have hd := (Real.hasDerivAt_binEntropy (ne_of_gt hx.1) (ne_of_lt hx.2)).add
      (((hasDerivAt_id x).pow 2).const_mul 2)
    exact (hd.congr_deriv (by dsimp; ring)).hasDerivWithinAt
  · intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    have hd := (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).log (by linarith : 1-x ≠ 0)).sub
      ((hasDerivAt_id x).log (ne_of_gt hx.1))
    exact ((hd.add ((hasDerivAt_id x).const_mul 4)).congr_deriv (by dsimp; ring)).hasDerivWithinAt
  · intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    have hpos : 0 < x*(1-x) := mul_pos hx.1 (by linarith)
    have he : -(1-x)⁻¹-x⁻¹+4 = (4*x*(1-x)-1)/(x*(1-x)) := by
      field_simp [ne_of_gt hx.1, ne_of_gt (sub_pos.mpr hx.2)]
      ring
    rw [he]
    apply div_nonpos_of_nonpos_of_nonneg _ hpos.le
    nlinarith [sq_nonneg (2*x-1)]

theorem binaryEntropy_midpoint_gap (a b : ℝ) (ha : a ∈ Set.Icc 0 1)
    (hb : b ∈ Set.Icc 0 1) :
    (a-b)^2/2 ≤ Real.binEntropy ((a+b)/2)-
      (Real.binEntropy a+Real.binEntropy b)/2 := by
  have hh := binaryEntropy_quadratic_concave.2 ha hb
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)+1/2=1)
  simp only [smul_eq_mul] at hh
  have he : (1/2 : ℝ)*a+(1/2)*b=(a+b)/2 := by ring
  rw [he] at hh
  nlinarith [hh]

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteEntropy

theorem negMulLog_sum_le {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) :
    Real.negMulLog (∑ i ∈ s, p i) ≤ ∑ i ∈ s, Real.negMulLog (p i) := by
  have hterm : ∀ i ∈ s,
      -(p i) * Real.log (∑ j ∈ s, p j) ≤ Real.negMulLog (p i) := by
    intro i hi
    rcases eq_or_lt_of_le (hp i hi) with h | h
    · simp [← h]
    · exact mul_le_mul_of_nonpos_left
        (Real.log_le_log h (Finset.single_le_sum hp hi)) (neg_nonpos.mpr (hp i hi))
  have heq : (∑ i ∈ s, -(p i) * Real.log (∑ j ∈ s, p j)) =
      Real.negMulLog (∑ i ∈ s, p i) := by
    rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    rfl
  rw [← heq]
  exact Finset.sum_le_sum hterm

theorem observableEntropy_le {α : Type uα} {β : Type uβ} [DecidableEq β] (s : Finset α) (p : α → ℝ)
    (f : α → β) (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p f ≤ entropy s p := by
  classical
  calc
    observableEntropy s p f ≤
        ∑ b ∈ s.image f, ∑ a ∈ s.filter (fun a => f a = b), Real.negMulLog (p a) := by
      apply Finset.sum_le_sum
      intro b _
      exact negMulLog_sum_le _ _ (fun a ha => hp a (Finset.mem_filter.mp ha).1)
    _ = entropy s p :=
      Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem f ha) _

theorem entropy_scale {α : Type uα} (s : Finset α) (p : α → ℝ) (c : ℝ) :
    entropy s (fun a => c * p a) =
      (∑ a ∈ s, p a) * Real.negMulLog c + c * entropy s p := by
  simp only [entropy, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]

theorem entropy_nonneg {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∀ a ∈ s, p a ≤ 1) : 0 ≤ entropy s p :=
  Finset.sum_nonneg (fun a ha => Real.negMulLog_nonneg (hp a ha) (hp1 a ha))

theorem entropy_le_log_card {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hs : ∑ a ∈ s, p a = 1) :
    entropy s p ≤ Real.log s.card := by
  classical
  have hne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hs
    norm_num at hs
  have hn : (0 : ℝ) < s.card := by exact_mod_cast Finset.card_pos.mpr hne
  have hterm : ∀ a ∈ s, (s.card : ℝ) * Real.negMulLog (p a) ≤
      1 - (s.card : ℝ) * p a - p a * Real.negMulLog s.card := by
    intro a ha
    have h := Real.negMulLog_le_one_sub_self (mul_nonneg hn.le (hp a ha))
    rw [Real.negMulLog_mul] at h
    linarith
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    hs, mul_one, one_mul, Finset.sum_const, nsmul_eq_mul] at hsum
  change (s.card : ℝ) * entropy s p ≤ _ at hsum
  have hneg : Real.negMulLog (s.card : ℝ) = -(s.card : ℝ) * Real.log s.card := rfl
  rw [hneg] at hsum
  apply (mul_le_mul_iff_right₀ hn).mp
  nlinarith

theorem entropy_mixture {α : Type uα} {β : Type uβ} (s : Finset α) (t : Finset β)
    (w : β → ℝ) (p : β → α → ℝ)
    (hw : ∀ b ∈ t, 0 ≤ w b) (hw1 : ∑ b ∈ t, w b = 1)
    (hp : ∀ b ∈ t, ∀ a ∈ s, 0 ≤ p b a) :
    ∑ b ∈ t, w b * entropy s (p b) ≤
      entropy s (fun a => ∑ b ∈ t, w b * p b a) := by
  simp only [entropy, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  exact Real.concaveOn_negMulLog.le_map_sum hw hw1 (fun b hb => hp b hb a ha)

theorem entropy_normalize {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    entropy s p = Real.negMulLog (∑ a ∈ s, p a) +
      (∑ a ∈ s, p a) * entropy s (fun a => p a / ∑ b ∈ s, p b) := by
  let P := ∑ a ∈ s, p a
  by_cases hP : P = 0
  · have hz : ∀ a ∈ s, p a = 0 := by
      intro a ha
      have ha' := Finset.single_le_sum hp ha
      change p a ≤ P at ha'
      rw [hP] at ha'
      exact le_antisymm ha' (hp a ha)
    change entropy s p = Real.negMulLog P + P * _
    simp only [hP, Real.negMulLog_zero, zero_mul, add_zero]
    exact Finset.sum_eq_zero (fun a ha => by rw [hz a ha, Real.negMulLog_zero])
  · have heq : entropy s p = entropy s (fun a => P * (p a / P)) := by
      apply Finset.sum_congr rfl
      intro a _
      dsimp only
      rw [mul_div_cancel₀ _ hP]
    rw [heq, entropy_scale]
    have hsum : (∑ a ∈ s, p a / P) = 1 := by rw [← Finset.sum_div]; exact div_self hP
    rw [hsum, one_mul]

theorem entropy_joint_le {α : Type uα} {β : Type uβ} (s : Finset α) (t : Finset β)
    (p : α → β → ℝ) (hp : ∀ a ∈ s, ∀ b ∈ t, 0 ≤ p a b)
    (hp1 : ∑ a ∈ s, ∑ b ∈ t, p a b = 1) :
    entropy (s ×ˢ t) (fun ab => p ab.1 ab.2) ≤
      entropy s (fun a => ∑ b ∈ t, p a b) + entropy t (fun b => ∑ a ∈ s, p a b) := by
  let r := fun a => ∑ b ∈ t, p a b
  have hr : ∀ a ∈ s, 0 ≤ r a := fun a ha => Finset.sum_nonneg (hp a ha)
  have hterm : ∀ a ∈ s, ∀ b ∈ t, r a * (p a b / r a) = p a b := by
    intro a ha b hb
    by_cases h : r a = 0
    · have hl := Finset.single_le_sum (hp a ha) hb
      have hz : p a b = 0 := le_antisymm (h ▸ hl) (hp a ha b hb)
      simp [hz]
    · exact mul_div_cancel₀ _ h
  have hc := entropy_mixture t s r (fun a b => p a b / r a) hr hp1
    (fun a ha b hb => div_nonneg (hp a ha b hb) (hr a ha))
  have hmix : entropy t (fun b => ∑ a ∈ s, r a * (p a b / r a)) =
      entropy t (fun b => ∑ a ∈ s, p a b) := by
    apply Finset.sum_congr rfl
    intro b hb
    congr 1
    exact Finset.sum_congr rfl (fun a ha => hterm a ha b hb)
  rw [hmix] at hc
  calc
    entropy (s ×ˢ t) (fun ab => p ab.1 ab.2) =
        ∑ a ∈ s, entropy t (p a) := by simp only [entropy, Finset.sum_product]
    _ = entropy s r + ∑ a ∈ s, r a * entropy t (fun b => p a b / r a) := by
      simp only [entropy, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      exact entropy_normalize t (p a) (hp a ha)
    _ ≤ _ := add_le_add le_rfl hc

theorem observableEntropy_on_superset {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (t : Finset β) (p : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) : observableEntropy s p f = entropy t (mass s p f) := by
  classical
  apply Finset.sum_subset
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact hf a ha
  · intro b _ hb
    rw [mass_eq_zero_of_not_mem s p f hb, Real.negMulLog_zero]

theorem observableEntropy_comp_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : β → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p (g ∘ f) ≤ observableEntropy s p f := by
  rw [observableEntropy_comp]
  exact observableEntropy_le _ _ _ (fun b _ => mass_nonneg s p f hp b)

theorem mass_pair_fst {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (b : β) :
    ∑ c ∈ s.image g, mass s p (fun a => (f a, g a)) (b, c) = mass s p f b := by
  classical
  simp only [mass, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hg : g a ∈ s.image g := Finset.mem_image_of_mem g ha
  by_cases hf : f a = b
  · simp [hf, hg]
  · simp [hf]

theorem mass_pair_snd {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (c : γ) :
    ∑ b ∈ s.image f, mass s p (fun a => (f a, g a)) (b, c) = mass s p g c := by
  classical
  simp only [mass, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  have hf : f a ∈ s.image f := Finset.mem_image_of_mem f ha
  by_cases hg : g a = c
  · simp [hg, hf]
  · simp [hg]

theorem observableEntropy_pair_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1) :
    observableEntropy s p (fun a => (f a, g a)) ≤
      observableEntropy s p f + observableEntropy s p g := by
  classical
  rw [observableEntropy_on_superset s (s.image f ×ˢ s.image g) p _
    (fun a ha => Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem f ha, Finset.mem_image_of_mem g ha⟩)]
  have h := entropy_joint_le (s.image f) (s.image g)
    (fun b c => mass s p (fun a => (f a, g a)) (b, c))
    (fun b _ c _ => mass_nonneg s p _ hp _) ?_
  · simpa only [mass_pair_fst, mass_pair_snd, observableEntropy] using h
  · simpa only [mass_pair_fst, mass_sum] using hp1

theorem observableEntropy_fst_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p f ≤ observableEntropy s p (fun a => (f a, g a)) := by
  exact observableEntropy_comp_le s p (fun a => (f a, g a)) Prod.fst hp

theorem conditionalEntropy_nonneg {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) : 0 ≤ conditionalEntropy s p f g := by
  apply sub_nonneg.mpr
  exact observableEntropy_comp_le s p (fun a => (f a, g a)) Prod.snd hp

theorem conditionalEntropy_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1) :
    conditionalEntropy s p f g ≤ observableEntropy s p f := by
  dsimp only [conditionalEntropy]
  linarith [observableEntropy_pair_le s p f g hp hp1]

theorem observableEntropy_equiv {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (e : β ≃ γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p (e ∘ f) = observableEntropy s p f := by
  apply le_antisymm (observableEntropy_comp_le s p f e hp)
  have h := observableEntropy_comp_le s p (e ∘ f) e.symm hp
  simpa only [Function.comp_def, Equiv.symm_apply_apply] using h

theorem observableEntropy_swap {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p (fun a => (f a, g a)) =
      observableEntropy s p (fun a => (g a, f a)) := by
  exact (observableEntropy_equiv s p (fun a => (f a, g a)) (Equiv.prodComm β γ) hp).symm

theorem entropy_table_chain {α : Type uα} {β : Type uβ} (s : Finset α) (t : Finset β)
    (p : α → β → ℝ) (hp : ∀ a ∈ s, ∀ b ∈ t, 0 ≤ p a b) :
    entropy (s ×ˢ t) (fun ab => p ab.1 ab.2) =
      entropy s (fun a => ∑ b ∈ t, p a b) +
      ∑ a ∈ s, (∑ b ∈ t, p a b) * entropy t (fun b => p a b / ∑ c ∈ t, p a c) := by
  simp only [entropy, Finset.sum_product, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  exact entropy_normalize t (p a) (hp a ha)

theorem mass_filter_div {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (c : γ) (b : β) (P : ℝ) :
    mass (s.filter (fun a => g a = c)) (fun a => p a / P) f b =
      mass s p (fun a => (g a, f a)) (c, b) / P := by
  classical
  simp only [mass, ← Finset.sum_div, Finset.filter_filter, Prod.mk.injEq]

theorem conditionalEntropy_eq_sum {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    conditionalEntropy s p f g = ∑ c ∈ s.image g, mass s p g c *
      observableEntropy (s.filter (fun a => g a = c)) (fun a => p a / mass s p g c) f := by
  classical
  have hrect := observableEntropy_on_superset s (s.image g ×ˢ s.image f) p
    (fun a => (g a, f a)) (fun a ha => Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem g ha, Finset.mem_image_of_mem f ha⟩)
  rw [entropy_table_chain (s.image g) (s.image f)
    (fun c b => mass s p (fun a => (g a, f a)) (c, b))
    (fun c _ b _ => mass_nonneg s p _ hp _)] at hrect
  simp only [mass_pair_fst] at hrect
  have hinner : ∀ c ∈ s.image g,
      entropy (s.image f) (fun b => mass s p (fun a => (g a, f a)) (c, b) / mass s p g c) =
      observableEntropy (s.filter (fun a => g a = c)) (fun a => p a / mass s p g c) f := by
    intro c _
    rw [observableEntropy_on_superset _ (s.image f) _ f]
    · apply Finset.sum_congr rfl
      intro b _
      rw [mass_filter_div]
    · intro a ha
      exact Finset.mem_image_of_mem f (Finset.mem_filter.mp ha).1
  have hh : observableEntropy s p (fun a => (g a, f a)) = observableEntropy s p g +
      ∑ c ∈ s.image g, mass s p g c *
        observableEntropy (s.filter (fun a => g a = c)) (fun a => p a / mass s p g c) f := by
    rw [hrect]
    congr 1
    apply Finset.sum_congr rfl
    intro c hc
    rw [hinner c hc]
  rw [conditionalEntropy, observableEntropy_swap s p f g hp, hh, add_sub_cancel_left]

theorem conditionalEntropy_chain {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (h : α → δ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    conditionalEntropy s p (fun a => (f a, g a)) h =
      conditionalEntropy s p g h + conditionalEntropy s p f (fun a => (g a, h a)) := by
  have he := observableEntropy_equiv s p (fun a => ((f a, g a), h a))
    (Equiv.prodAssoc β γ δ) hp
  change observableEntropy s p (fun a => (f a, (g a, h a))) =
    observableEntropy s p (fun a => ((f a, g a), h a)) at he
  dsimp only [conditionalEntropy]
  linarith

theorem conditionalEntropy_reveal_le {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (h : α → δ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1) :
    conditionalEntropy s p f h ≤ observableEntropy s p g +
      conditionalEntropy s p f (fun a => (g a, h a)) := by
  have hm := observableEntropy_comp_le s p (fun a => ((f a, g a), h a))
    (fun x => (x.1.1, x.2)) hp
  have hr := conditionalEntropy_chain s p f g h hp
  have hg := conditionalEntropy_le s p g h hp hp1
  dsimp only [conditionalEntropy] at *
  change observableEntropy s p (fun a => (f a, h a)) ≤ _ at hm
  linarith

theorem observableEntropy_const_of {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (p : α → ℝ) (f : α → β) (b : β) (hf : ∀ a ∈ s, f a = b) :
    observableEntropy s p f = Real.negMulLog (∑ a ∈ s, p a) := by
  classical
  rw [observableEntropy_on_superset s {b} p f (fun a ha => Finset.mem_singleton.mpr (hf a ha))]
  simp only [entropy, Finset.sum_singleton, mass]
  rw [Finset.filter_eq_self.mpr hf]

theorem observableEntropy_le_log_on_superset {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (t : Finset β) (p : α → ℝ) (f : α → β)
    (hf : ∀ a ∈ s, f a ∈ t) (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1) :
    observableEntropy s p f ≤ Real.log t.card := by
  rw [observableEntropy_on_superset s t p f hf]
  apply entropy_le_log_card _ _ (fun b _ => mass_nonneg s p f hp b)
  have h := sum_mass_mul s t p f (fun _ => 1) hf
  simpa only [mul_one, hp1] using h

theorem conditionalEntropy_le_bad_mass {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (bad : γ → Prop) [DecidablePred bad] (hp : ∀ a ∈ s, 0 ≤ p a)
    (hgood : ∀ a ∈ s, ∀ b ∈ s, g a = g b → ¬bad (g a) → f a = f b) :
    conditionalEntropy s p f g ≤
      (∑ a ∈ s, if bad (g a) then p a else 0) * Real.log (s.image f).card := by
  classical
  let K := Real.log (s.image f).card
  rw [conditionalEntropy_eq_sum s p f g hp]
  calc
    _ ≤ ∑ c ∈ s.image g, mass s p g c * (if bad c then K else 0) := by
      apply Finset.sum_le_sum
      intro c hc
      let P := mass s p g c
      have hP : 0 ≤ P := mass_nonneg s p g hp c
      by_cases hP0 : P = 0
      · change P * _ ≤ P * _
        simp only [hP0, zero_mul, le_refl]
      have hn : ∑ a ∈ s.filter (fun a => g a = c), p a / P = 1 := by
        rw [← Finset.sum_div]
        exact div_self hP0
      have hq : ∀ a ∈ s.filter (fun a => g a = c), 0 ≤ p a / P :=
        fun a ha => div_nonneg (hp a (Finset.mem_filter.mp ha).1) hP
      apply mul_le_mul_of_nonneg_left _ hP
      by_cases hbad : bad c
      · rw [ite_eq_left hbad]
        exact observableEntropy_le_log_on_superset _ (s.image f) _ f
          (fun a ha => Finset.mem_image_of_mem f (Finset.mem_filter.mp ha).1) hq hn
      · rw [ite_eq_right hbad]
        obtain ⟨a₀, ha₀, hga₀⟩ := Finset.mem_image.mp hc
        have hconst : ∀ a ∈ s.filter (fun a => g a = c), f a = f a₀ := by
          intro a ha
          obtain ⟨has, hga⟩ := Finset.mem_filter.mp ha
          exact hgood a has a₀ ha₀ (hga.trans hga₀.symm) (hga ▸ hbad)
        rw [observableEntropy_const_of _ _ _ (f a₀) hconst, hn, Real.negMulLog_one]
    _ = ∑ a ∈ s, p a * (if bad (g a) then K else 0) :=
      sum_mass_mul s (s.image g) p g _ (fun a ha => Finset.mem_image_of_mem g ha)
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp [K]

theorem observableEntropy_bool {α : Type uα} (s : Finset α) (p : α → ℝ)
    (f : α → Bool) (hp1 : ∑ a ∈ s, p a = 1) :
    observableEntropy s p f = Real.binEntropy (mass s p f true) := by
  have hsum := sum_mass_mul s Finset.univ p f (fun _ => 1) (fun _ _ => Finset.mem_univ _)
  have hm : mass s p f false = 1 - mass s p f true := by
    simp only [mul_one, Fintype.sum_bool, hp1] at hsum
    linarith
  rw [observableEntropy_on_superset s Finset.univ p f (fun _ _ => Finset.mem_univ _)]
  simp only [entropy, Fintype.sum_bool, hm,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

theorem conditionalEntropy_rare_flag {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (C : α → β) (Y : α → γ) (E : α → Bool)
    (B : γ → Prop) [DecidablePred B] (c₀ : β)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a = 1)
    (hgood : ∀ a ∈ s, E a = false → ¬B (Y a) → C a = c₀) :
    conditionalEntropy s p C Y ≤ Real.binEntropy (mass s p E true) +
      (mass s p E true + ∑ a ∈ s.filter (fun a => B (Y a)), p a) *
        Real.log (s.image C).card := by
  classical
  let bad : Bool × γ → Prop := fun ey => ey.1 = true ∨ B ey.2
  have hc := conditionalEntropy_le_bad_mass s p C (fun a => (E a, Y a)) bad hp ?_
  · have hn : s.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hp1
      norm_num at hp1
    have hK : 0 ≤ Real.log (s.image C).card := Real.log_nonneg (by
      exact_mod_cast Finset.card_pos.mpr (hn.image C))
    have hb : (∑ a ∈ s, if bad (E a, Y a) then p a else 0) ≤
        mass s p E true + ∑ a ∈ s.filter (fun a => B (Y a)), p a := by
      simp only [mass, Finset.sum_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro a ha
      dsimp only [bad]
      split_ifs <;> first | linarith [hp a ha] | simp_all
    have hm := mul_le_mul_of_nonneg_right hb hK
    have hr := conditionalEntropy_reveal_le s p C E Y hp hp1
    rw [observableEntropy_bool s p E hp1] at hr
    linarith
  · intro a ha b hb he hbad
    have hEa : E a = false := by
      have : E a ≠ true := fun h => hbad (Or.inl h)
      cases h : E a <;> simp_all
    have hBa : ¬B (Y a) := fun h => hbad (Or.inr h)
    have hEb : E b = false := (congrArg Prod.fst he).symm.trans hEa
    have hBb : ¬B (Y b) := by
      simpa only [show Y b = Y a from (congrArg Prod.snd he).symm] using hBa
    rw [hgood a ha hEa hBa, hgood b hb hEb hBb]

theorem binEntropy_bits_le_three_sqrt {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Real.binEntropy q / Real.log 2 ≤ 3 * Real.sqrt q := by
  have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hs2 : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq
  have h1 := Real.negMulLog_le_one_sub_self hs
  have h2 := Real.negMulLog_le_one_sub_self (sub_nonneg.mpr hq1)
  have hmul := mul_le_mul_of_nonneg_left h1 hs
  have hident := Real.negMulLog_mul (Real.sqrt q) (Real.sqrt q)
  rw [hs2] at hident
  have hbound : Real.binEntropy q ≤ 2 * Real.sqrt q := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    nlinarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ hlog).mpr
  have hlog2 : (2 : ℝ) ≤ 3 * Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hlog2)]

theorem event_union_bound {α : Type uα} {ι : Type uι} [Fintype ι]
    (s : Finset α) (p : α → ℝ) (E : ι → α → Prop)
    [∀ i, DecidablePred (E i)] (hp : ∀ a ∈ s, 0 ≤ p a) :
    (∑ a ∈ s, if ∃ i, E i a then p a else 0) ≤
      ∑ i, ∑ a ∈ s, if E i a then p a else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a ha
  by_cases he : ∃ i, E i a
  · rw [ite_eq_left he]
    obtain ⟨i, hi⟩ := he
    apply le_trans _ (Finset.single_le_sum (fun j _ => by
      split_ifs <;> first | exact hp a ha | exact le_rfl) (Finset.mem_univ i))
    simp only [ite_eq_left hi, le_refl]
  · rw [ite_eq_right he]
    exact Finset.sum_nonneg (fun j _ => by
      split_ifs <;> first | exact hp a ha | exact le_rfl)

theorem two_exceptions_bound {α : Type uα} {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (s : Finset α) (p : α → ℝ) (E : ι → α → Prop)
    [∀ i, DecidablePred (E i)] (hp : ∀ a ∈ s, 0 ≤ p a)
    (hind : ∀ i j, i ≠ j →
      (∑ a ∈ s, if E i a ∧ E j a then p a else 0) =
        (∑ a ∈ s, if E i a then p a else 0) *
        (∑ a ∈ s, if E j a then p a else 0)) :
    let t := ∑ i, ∑ a ∈ s, if E i a then p a else 0
    let q := ∑ a ∈ s, if ∃ i j, i ≠ j ∧ E i a ∧ E j a then p a else 0
    q ≤ t ^ 2 ∧ q ≤ t := by
  classical
  dsimp only
  have hPi : ∀ i, 0 ≤ ∑ a ∈ s, if E i a then p a else 0 := by
    intro i
    apply Finset.sum_nonneg
    intro a ha
    split_ifs <;> first | exact hp a ha | exact le_rfl
  constructor
  · have hU := event_union_bound s p
      (fun ij : ι × ι => fun a => ij.1 ≠ ij.2 ∧ E ij.1 a ∧ E ij.2 a) hp
    have he : (∑ a ∈ s, if ∃ i j, i ≠ j ∧ E i a ∧ E j a then p a else 0) =
        ∑ a ∈ s, if ∃ ij : ι × ι, ij.1 ≠ ij.2 ∧ E ij.1 a ∧ E ij.2 a then p a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      exact propext ⟨fun ⟨i,j,h⟩ => ⟨(i,j),h⟩, fun ⟨⟨i,j⟩,h⟩ => ⟨i,j,h⟩⟩
    rw [he]
    apply le_trans hU
    rw [Fintype.sum_prod_type, sq, Finset.sum_mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i = j
    · subst j
      simp only [ne_eq, not_true_eq_false, false_and, ite_false, Finset.sum_const_zero]
      exact mul_nonneg (hPi i) (hPi i)
    · simpa only [ne_eq, hij, not_false_eq_true, true_and] using (hind i j hij).le
  · apply le_trans _ (event_union_bound s p E hp)
    apply Finset.sum_le_sum
    intro a ha
    by_cases h : ∃ i j, i ≠ j ∧ E i a ∧ E j a
    · obtain ⟨i,j,hij,hi,hj⟩ := h
      rw [ite_eq_left ⟨i,j,hij,hi,hj⟩, ite_eq_left (show ∃ i, E i a from ⟨i,hi⟩)]
    · rw [ite_eq_right h]
      split_ifs <;> first | exact hp a ha | exact le_rfl

theorem no_large_coordinate {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) {a : ℝ} (ha : 0 < a)
    (hE : ¬∃ i j, i ≠ j ∧ a / (4 * Fintype.card ι) ≤ |x i| ∧
      a / (4 * Fintype.card ι) ≤ |x j|)
    (hB : |∑ i, x i| < a / 2) (i : ι) : |x i| < a := by
  by_contra hn
  have hi : a ≤ |x i| := le_of_not_gt hn
  have hk : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  have hka : a / (4 * Fintype.card ι) ≤ a := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Fintype.card ι)).mpr
    have : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
    nlinarith
  have hsmall : ∀ j ∈ Finset.univ.erase i, |x j| < a / (4 * Fintype.card ι) := by
    intro j hj
    by_contra hn
    exact hE ⟨i,j,Ne.symm (Finset.mem_erase.mp hj).1,hka.trans hi,le_of_not_gt hn⟩
  have habs : |∑ j ∈ Finset.univ.erase i, x j| ≤ a / 4 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      (∑ j ∈ Finset.univ.erase i, |x j|) ≤
          ∑ _j ∈ Finset.univ.erase i, a / (4 * Fintype.card ι) :=
        Finset.sum_le_sum (fun j hj => (hsmall j hj).le)
      _ ≤ ∑ _j : ι, a / (4 * Fintype.card ι) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
          (fun _ _ _ => by positivity)
      _ = a / 4 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp
  have hiabs : |x i| ≤ |∑ j, x j| + |∑ j ∈ Finset.univ.erase i, x j| := by
    have he := Finset.sum_erase_add Finset.univ x (Finset.mem_univ i)
    have hx : x i = (∑ j, x j) - ∑ j ∈ Finset.univ.erase i, x j := by linarith
    rw [hx]
    exact abs_sub _ _
  linarith

theorem mass_subset {α : Type uα} {β : Type uβ} [DecidableEq β] {s t : Finset α}
    (p : α → ℝ) (f : α → β) (hst : s ⊆ t)
    (hp : ∀ x ∈ t, x ∉ s → p x = 0) (b : β) : mass s p f b = mass t p f b := by
  classical
  apply Finset.sum_subset (Finset.filter_subset_filter _ hst)
  intro x hx hn
  exact hp x (Finset.mem_filter.mp hx).1 (fun hs => hn (Finset.mem_filter.mpr ⟨hs,(Finset.mem_filter.mp hx).2⟩))

theorem observableEntropy_congr {α : Type uα} {β : Type uβ} [DecidableEq β]
    (s : Finset α) (p q : α → ℝ) (f g : α → β)
    (hp : ∀ x ∈ s, p x = q x) (hf : ∀ x ∈ s, f x = g x) :
    observableEntropy s p f = observableEntropy s q g := by
  classical
  have hi : s.image f = s.image g := Finset.image_congr hf
  have hm : ∀ b, mass s p f b = mass s q g b := by
    intro b
    simp only [mass, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hp x hx, hf x hx]
  simp only [observableEntropy, hi]
  rw [show mass s p f = mass s q g from funext hm]

theorem observableEntropy_le_of_fibers {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq β] [DecidableEq γ] [Nonempty β]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ x ∈ s, 0 ≤ p x)
    (hfg : ∀ x ∈ s, ∀ y ∈ s, g x = g y → f x = f y) :
    observableEntropy s p f ≤ observableEntropy s p g := by
  classical
  let h : γ → β := fun c => if hc : ∃ x ∈ s, g x = c then f hc.choose else Classical.choice inferInstance
  have hf : ∀ x ∈ s, (h ∘ g) x = f x := by
    intro x hx
    dsimp only [Function.comp_apply,h]
    rw [dite_eq_left ⟨x,hx,rfl⟩]
    exact hfg _ (Exists.choose_spec (show ∃ y ∈ s, g y = g x from ⟨x,hx,rfl⟩)).1
      x hx (Exists.choose_spec (show ∃ y ∈ s, g y = g x from ⟨x,hx,rfl⟩)).2
  rw [← observableEntropy_congr s p p (h ∘ g) f (fun _ _ => rfl) hf]
  exact observableEntropy_comp_le s p g h hp

theorem observableEntropy_id {α : Type uα} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) : observableEntropy s p id = entropy s p := by
  simp only [observableEntropy, Finset.image_id, entropy, mass, id_eq]
  apply Finset.sum_congr rfl
  intro a ha
  simp [Finset.filter_eq',ha]

theorem conditionalEntropy_disintegrate {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (h : α → δ)
    (hp : ∀ x ∈ s, 0 ≤ p x) :
    conditionalEntropy s p f (fun x => (h x,g x)) =
      ∑ c ∈ s.image g, mass s p g c * conditionalEntropy
        (s.filter (fun x => g x = c)) (fun x => p x / mass s p g c) f h := by
  have hc := conditionalEntropy_chain s p f h g hp
  rw [conditionalEntropy_eq_sum s p (fun x => (f x,h x)) g hp,
      conditionalEntropy_eq_sum s p h g hp] at hc
  simp only [conditionalEntropy, mul_sub, Finset.sum_sub_distrib]
  dsimp only [conditionalEntropy] at hc
  linarith

theorem observableEntropy_eq_of_fibers {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq β] [DecidableEq γ] [Nonempty β] [Nonempty γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ x ∈ s, 0 ≤ p x)
    (hfg : ∀ x ∈ s, ∀ y ∈ s, f x = f y ↔ g x = g y) :
    observableEntropy s p f = observableEntropy s p g :=
  le_antisymm (observableEntropy_le_of_fibers s p f g hp
    (fun x hx y hy => (hfg x hx y hy).mpr))
    (observableEntropy_le_of_fibers s p g f hp
    (fun x hx y hy => (hfg x hx y hy).mp))

theorem observableEntropy_of_injective {α : Type uα} {β : Type uβ} [DecidableEq β] [Nonempty β]
    [Nonempty α] (s : Finset α) (p : α → ℝ) (f : α → β)
    (hp : ∀ x ∈ s, 0 ≤ p x) (hf : Function.Injective f) :
    observableEntropy s p f = entropy s p := by
  classical
  rw [← observableEntropy_id s p]
  exact observableEntropy_eq_of_fibers s p f id hp (fun _ _ _ _ => hf.eq_iff)

theorem conditionalEntropy_eq_of_fibers {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    [Nonempty β] [Nonempty γ] [Nonempty δ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (h : α → δ)
    (hp : ∀ x ∈ s, 0 ≤ p x)
    (hfg : ∀ x ∈ s, ∀ y ∈ s, f x = f y ↔ g x = g y) :
    conditionalEntropy s p f h = conditionalEntropy s p g h := by
  unfold conditionalEntropy
  congr 1
  apply observableEntropy_eq_of_fibers _ _ _ _ hp
  intro x hx y hy
  simp only [Prod.mk.injEq, hfg x hx y hy]

theorem conditionalEntropy_condition_swap {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    [Nonempty β] [Nonempty γ] [Nonempty δ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (h : α → δ)
    (hp : ∀ x ∈ s, 0 ≤ p x) :
    conditionalEntropy s p f (fun x => (g x,h x)) =
      conditionalEntropy s p f (fun x => (h x,g x)) := by
  unfold conditionalEntropy
  rw [observableEntropy_swap s p g h hp]
  congr 1
  apply observableEntropy_eq_of_fibers _ _ _ _ hp
  intro x _ y _
  simp only [Prod.mk.injEq, and_comm (a := g x = g y)]

theorem conditionalEntropy_condition_le {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
    [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : α → γ) (h : α → δ)
    (hp : ∀ x ∈ s, 0 ≤ p x) :
    conditionalEntropy s p f (fun x => (h x,g x)) ≤ conditionalEntropy s p f g := by
  classical
  rw [conditionalEntropy_disintegrate s p f g h hp, conditionalEntropy_eq_sum s p f g hp]
  apply Finset.sum_le_sum
  intro c _
  have hP := mass_nonneg s p g hp c
  by_cases hc : mass s p g c = 0
  · simp only [hc, zero_mul, le_refl]
  apply mul_le_mul_of_nonneg_left _ hP
  apply conditionalEntropy_le
  · intro a ha
    exact div_nonneg (hp a (Finset.mem_filter.mp ha).1) hP
  · rw [← Finset.sum_div]
    exact div_self hc

theorem observableEntropy_mixture_marginal {ι : Type uι} {α : Type uα} {β : Type uβ} [DecidableEq β]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β) :
    observableEntropy (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => f ia.2) =
      observableEntropy s (fun a => ∑ i ∈ t, w i*p i a) f := by
  classical
  rw [observableEntropy_on_superset (t ×ˢ s) (s.image f) _ _ (by
    intro x hx; exact Finset.mem_image_of_mem f (Finset.mem_product.mp hx).2)]
  unfold observableEntropy entropy
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  simp only [mass, Finset.sum_filter, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hf : f a = b <;> simp [hf]

theorem observableEntropy_mixture_joint {ι : Type uι} {α : Type uα} {β : Type uβ} [DecidableEq ι] [DecidableEq β]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β)
    (hp : ∀ i ∈ t, ∑ a ∈ s, p i a = 1) :
    observableEntropy (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => (ia.1,f ia.2)) =
      entropy t w + ∑ i ∈ t, w i*observableEntropy s (p i) f := by
  classical
  rw [observableEntropy_on_superset (t ×ˢ s) (t ×ˢ s.image f) _ _ (by
    intro x hx
    exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hx).1,
      Finset.mem_image_of_mem f (Finset.mem_product.mp hx).2⟩)]
  have hm : ∀ i ∈ t, ∀ b : β,
      mass (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => (ia.1,f ia.2)) (i,b) =
        w i * mass s (p i) f b := by
    intro i hi b
    simp only [mass, Finset.sum_filter, Finset.sum_product, Prod.mk.injEq]
    simp_rw [ite_and]
    rw [Finset.sum_eq_single i]
    · simp [Finset.mul_sum, mul_ite]
    · intro j _ hji
      simp [hji]
    · exact fun h => (h hi).elim
  calc
    _ = ∑ i ∈ t, entropy (s.image f) (fun b => w i*mass s (p i) f b) := by
      simp only [entropy, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_congr rfl (fun b _ => congrArg Real.negMulLog (hm i hi b))
    _ = _ := by
      change (∑ i ∈ t, entropy (s.image f) (fun b => w i*mass s (p i) f b)) =
        (∑ i ∈ t, Real.negMulLog (w i)) + ∑ i ∈ t, w i*observableEntropy s (p i) f
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [entropy_scale, mass_sum, hp i hi, one_mul]
      rfl

theorem conditionalEntropy_mixture {ι : Type uι} {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq ι] [DecidableEq β] [DecidableEq γ]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β) (g : α → γ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hp : ∀ i ∈ t, ∀ a ∈ s, 0 ≤ p i a)
    (hp1 : ∀ i ∈ t, ∑ a ∈ s, p i a = 1) :
    (∑ i ∈ t, w i*conditionalEntropy s (p i) f g) ≤
      conditionalEntropy s (fun a => ∑ i ∈ t, w i*p i a) f g := by
  classical
  let q : ι × α → ℝ := fun ia => w ia.1*p ia.1 ia.2
  have hq : ∀ x ∈ t ×ˢ s, 0 ≤ q x := by
    intro x hx
    exact mul_nonneg (hw x.1 (Finset.mem_product.mp hx).1)
      (hp x.1 (Finset.mem_product.mp hx).1 x.2 (Finset.mem_product.mp hx).2)
  have hh := conditionalEntropy_condition_le (t ×ˢ s) q
    (fun ia => f ia.2) (fun ia => g ia.2) Prod.fst hq
  have he : observableEntropy (t ×ˢ s) q (fun x => (f x.2,(x.1,g x.2))) =
      observableEntropy (t ×ˢ s) q (fun x => (x.1,(f x.2,g x.2))) := by
    let e : ι × (β × γ) ≃ β × (ι × γ) :=
      { toFun := fun x => (x.2.1,(x.1,x.2.2))
        invFun := fun x => (x.2.1,(x.1,x.2.2))
        left_inv := by rintro ⟨i,b,c⟩; rfl
        right_inv := by rintro ⟨b,i,c⟩; rfl }
    exact observableEntropy_equiv (t ×ˢ s) q (fun x => (x.1,(f x.2,g x.2))) e hq
  dsimp only [conditionalEntropy] at hh ⊢
  rw [he, observableEntropy_mixture_joint t s w p (fun a => (f a,g a)) hp1,
    observableEntropy_mixture_joint t s w p g hp1,
    observableEntropy_mixture_marginal t s w p (fun a => (f a,g a)),
    observableEntropy_mixture_marginal t s w p g] at hh
  simpa only [mul_sub, Finset.sum_sub_distrib, add_sub_add_left_eq_sub] using hh

theorem observableEntropy_mixture_joint_general {ι : Type uι} {α : Type uα} {β : Type uβ} [DecidableEq ι] [DecidableEq β]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β) :
    observableEntropy (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => (ia.1,f ia.2)) =
      ∑ i ∈ t, ((∑ a ∈ s, p i a)*Real.negMulLog (w i)+
        w i*observableEntropy s (p i) f) := by
  classical
  rw [observableEntropy_on_superset (t ×ˢ s) (t ×ˢ s.image f) _ _ (by
    intro x hx
    exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hx).1,
      Finset.mem_image_of_mem f (Finset.mem_product.mp hx).2⟩)]
  have hm : ∀ i ∈ t, ∀ b : β,
      mass (t ×ˢ s) (fun ia => w ia.1*p ia.1 ia.2) (fun ia => (ia.1,f ia.2)) (i,b) =
        w i * mass s (p i) f b := by
    intro i hi b
    simp only [mass, Finset.sum_filter, Finset.sum_product, Prod.mk.injEq]
    simp_rw [ite_and]
    rw [Finset.sum_eq_single i]
    · simp [Finset.mul_sum, mul_ite]
    · intro j _ hji
      simp [hji]
    · exact fun h => (h hi).elim
  calc
    _ = ∑ i ∈ t, entropy (s.image f) (fun b => w i*mass s (p i) f b) := by
      simp only [entropy, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_congr rfl (fun b _ => congrArg Real.negMulLog (hm i hi b))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [entropy_scale, mass_sum]
      rfl

theorem conditionalEntropy_mixture_general {ι : Type uι} {α : Type uα} {β : Type uβ} {γ : Type uγ}
    [DecidableEq ι] [DecidableEq β] [DecidableEq γ]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (f : α → β) (g : α → γ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hp : ∀ i ∈ t, ∀ a ∈ s, 0 ≤ p i a)
    :
    (∑ i ∈ t, w i*conditionalEntropy s (p i) f g) ≤
      conditionalEntropy s (fun a => ∑ i ∈ t, w i*p i a) f g := by
  classical
  let q : ι × α → ℝ := fun ia => w ia.1*p ia.1 ia.2
  have hq : ∀ x ∈ t ×ˢ s, 0 ≤ q x := by
    intro x hx
    exact mul_nonneg (hw x.1 (Finset.mem_product.mp hx).1)
      (hp x.1 (Finset.mem_product.mp hx).1 x.2 (Finset.mem_product.mp hx).2)
  have hh := conditionalEntropy_condition_le (t ×ˢ s) q
    (fun ia => f ia.2) (fun ia => g ia.2) Prod.fst hq
  have he : observableEntropy (t ×ˢ s) q (fun x => (f x.2,(x.1,g x.2))) =
      observableEntropy (t ×ˢ s) q (fun x => (x.1,(f x.2,g x.2))) := by
    let e : ι × (β × γ) ≃ β × (ι × γ) :=
      { toFun := fun x => (x.2.1,(x.1,x.2.2))
        invFun := fun x => (x.2.1,(x.1,x.2.2))
        left_inv := by rintro ⟨i,b,c⟩; rfl
        right_inv := by rintro ⟨b,i,c⟩; rfl }
    exact observableEntropy_equiv (t ×ˢ s) q (fun x => (x.1,(f x.2,g x.2))) e hq
  dsimp only [conditionalEntropy] at hh ⊢
  rw [he, observableEntropy_mixture_joint_general t s w p (fun a => (f a,g a)),
    observableEntropy_mixture_joint_general t s w p g,
    observableEntropy_mixture_marginal t s w p (fun a => (f a,g a)),
    observableEntropy_mixture_marginal t s w p g] at hh
  simpa only [mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib, add_sub_add_left_eq_sub] using hh

theorem conditionalEntropy_mono {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p q : α → ℝ) (f : α → β) (g : α → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hpq : ∀ a ∈ s, p a ≤ q a) :
    conditionalEntropy s p f g ≤ conditionalEntropy s q f g := by
  let P : Bool → α → ℝ := fun b => if b then p else fun a => q a-p a
  have hh := conditionalEntropy_mixture_general Finset.univ s (fun _ : Bool => (1 : ℝ))
    P f g (by intros; exact zero_le_one) (by
      intro b _ a ha
      cases b
      · exact sub_nonneg.mpr (hpq a ha)
      · exact hp a ha)
  have he : (fun a => ∑ b : Bool, (1 : ℝ)*P b a)=q := by
    funext a
    simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte, one_mul]
    ring
  rw [he] at hh
  simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte, one_mul] at hh
  have hn := conditionalEntropy_nonneg s (fun a => q a-p a) f g
    (fun a ha => sub_nonneg.mpr (hpq a ha))
  linarith

theorem mixture_information_common {ι : Type uι} {α : Type uα} [DecidableEq ι] [DecidableEq α]
    (t : Finset ι) (s : Finset α) (w : ι → ℝ) (p : ι → α → ℝ) (r : α → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hw1 : ∑ i ∈ t, w i=1)
    (hp1 : ∀ i ∈ t, ∑ a ∈ s, p i a=1)
    (hr : ∀ a ∈ s, 0 ≤ r a) (hrp : ∀ i ∈ t, ∀ a ∈ s, r a ≤ p i a) :
    entropy s (fun a => ∑ i ∈ t, w i*p i a) - (∑ i ∈ t, w i*entropy s (p i)) ≤
      (1-∑ a ∈ s, r a)*entropy t w := by
  have hh := conditionalEntropy_mono (t ×ˢ s)
    (fun ia => w ia.1*r ia.2) (fun ia => w ia.1*p ia.1 ia.2) Prod.fst Prod.snd
    (by
      intro x hx
      exact mul_nonneg (hw x.1 (Finset.mem_product.mp hx).1)
        (hr x.2 (Finset.mem_product.mp hx).2))
    (by
      intro x hx
      exact mul_le_mul_of_nonneg_left
        (hrp x.1 (Finset.mem_product.mp hx).1 x.2 (Finset.mem_product.mp hx).2)
        (hw x.1 (Finset.mem_product.mp hx).1))
  dsimp only [conditionalEntropy] at hh
  have hjr := observableEntropy_mixture_joint_general t s w (fun _ => r) id
  have hjp := observableEntropy_mixture_joint t s w p id hp1
  have hmr := observableEntropy_mixture_marginal t s w (fun _ => r) id
  have hmp := observableEntropy_mixture_marginal t s w p id
  simp only [id_eq] at hjr hjp hmr hmp
  rw [hjr, hjp, hmr, hmp] at hh
  simp_rw [observableEntropy_id, ← Finset.sum_mul, hw1, one_mul] at hh
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hw1, one_mul] at hh
  change (∑ a ∈ s, r a)*entropy t w+entropy s r-entropy s r ≤
    entropy t w+(∑ i ∈ t, w i*entropy s (p i))-
      entropy s (fun a => ∑ i ∈ t, w i*p i a) at hh
  nlinarith

theorem conditionalEntropy_id {α : Type uα} {β : Type uβ} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (p : α → ℝ) (g : α → β) (hp : ∀ a ∈ s, 0 ≤ p a) :
    conditionalEntropy s p id g = entropy s p-observableEntropy s p g := by
  have hh := observableEntropy_comp_le s p (fun a => (a,g a)) Prod.fst hp
  change observableEntropy s p id ≤ _ at hh
  rw [observableEntropy_id] at hh
  have he := le_antisymm (observableEntropy_le s p (fun a => (a,g a)) hp) hh
  exact congrArg (fun x => x-observableEntropy s p g) he

theorem conditionalEntropy_midpoint {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) (f : α → β) (g : α → γ) :
    (conditionalEntropy s p f g+conditionalEntropy s q f g)/2 ≤
      conditionalEntropy s (fun a => (p a+q a)/2) f g := by
  let P : Bool → α → ℝ := fun b => if b then p else q
  have hh := conditionalEntropy_mixture Finset.univ s (fun _ : Bool => (1/2 : ℝ))
    P f g (by intros; positivity) (by intro b _; cases b <;> assumption)
      (by intro b _; cases b <;> assumption)
  have he : (fun a => ∑ b : Bool, (1/2 : ℝ)*P b a) = fun a => (p a+q a)/2 := by
    funext a
    simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte]
    ring
  rw [he] at hh
  simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte] at hh
  linarith

theorem js_observable_le {α : Type uα} {β : Type uβ} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) (g : α → β) :
    observableEntropy s (fun a => (p a+q a)/2) g-
      (observableEntropy s p g+observableEntropy s q g)/2 ≤ js s p q := by
  have hh := conditionalEntropy_midpoint s p q hp hq hp1 hq1 id g
  rw [conditionalEntropy_id s p g hp, conditionalEntropy_id s q g hq,
    conditionalEntropy_id s _ g (fun a ha => div_nonneg (add_nonneg (hp a ha) (hq a ha)) (by norm_num))] at hh
  unfold js
  linarith

theorem js_nonneg {α : Type uα} [DecidableEq α]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) : 0 ≤ js s p q := by
  have hh := js_observable_le s p q hp hq hp1 hq1 (fun _ => ())
  have hm1 : (∑a∈s, (p a+q a)/2)=1 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, hp1, hq1]
    norm_num
  rw [observableEntropy_const_of s p (fun _ => ()) () (by intros; rfl),
    observableEntropy_const_of s q (fun _ => ()) () (by intros; rfl),
    observableEntropy_const_of s _ (fun _ => ()) () (by intros; rfl), hp1, hq1, hm1] at hh
  simpa only [Real.negMulLog_one, add_zero, zero_div, sub_zero] using hh

theorem event_sq_le_two_js {α : Type uα} [DecidableEq α]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) (f : α → Bool) :
    (mass s p f true-mass s q f true)^2 ≤ 2*js s p q := by
  have hh := js_observable_le s p q hp hq hp1 hq1 f
  have hm1 : (∑a∈s, (p a+q a)/2)=1 := by
    rw [← Finset.sum_div, Finset.sum_add_distrib, hp1, hq1]
    norm_num
  rw [observableEntropy_bool s p f hp1, observableEntropy_bool s q f hq1,
    observableEntropy_bool s _ f hm1] at hh
  have hm : mass s (fun a => (p a+q a)/2) f true =
      (mass s p f true+mass s q f true)/2 := by
    simp only [mass, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [hm] at hh
  have hple : mass s p f true ≤ 1 := by
    rw [mass, ← hp1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) (fun a ha _ => hp a ha)
  have hqle : mass s q f true ≤ 1 := by
    rw [mass, ← hq1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..) (fun a ha _ => hq a ha)
  have hg := binaryEntropy_midpoint_gap (mass s p f true) (mass s q f true)
    ⟨mass_nonneg s p f hp true,hple⟩ ⟨mass_nonneg s q f hq true,hqle⟩
  linarith

theorem totalVariation_eq_event {α : Type uα} (s : Finset α) (p q : α → ℝ)
    (hp1 : ∑ a ∈ s, p a=1) (hq1 : ∑ a ∈ s, q a=1) :
    totalVariation s p q = mass s p (fun a => decide (q a ≤ p a)) true-
      mass s q (fun a => decide (q a ≤ p a)) true := by
  classical
  have he (a : α) : |p a-q a|=2*(if q a ≤ p a then p a-q a else 0)-(p a-q a) := by
    split_ifs with h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; ring
    · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt (lt_of_not_ge h)))]; ring
  simp_rw [totalVariation, he]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hp1, hq1]
  simp only [sub_self, sub_zero, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [mass, Finset.sum_filter, decide_eq_true_eq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring

theorem totalVariation_sq_le_two_js {α : Type uα} [DecidableEq α]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) :
    (totalVariation s p q)^2 ≤ 2*js s p q := by
  rw [totalVariation_eq_event s p q hp1 hq1]
  exact event_sq_le_two_js s p q hp hq hp1 hq1 _

theorem sum_min_eq_one_sub_tv {α : Type uα} (s : Finset α) (p q : α → ℝ)
    (hp1 : ∑ a ∈ s, p a=1) (hq1 : ∑ a ∈ s, q a=1) :
    (∑ a ∈ s, min (p a) (q a))=1-totalVariation s p q := by
  have he (a : α) : min (p a) (q a)=(p a+q a-|p a-q a|)/2 := by
    rcases le_total (p a) (q a) with h|h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  simp_rw [he]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, hp1, hq1]
  unfold totalVariation
  ring

theorem js_le_tv {α : Type uα} [DecidableEq α]
    (s : Finset α) (p q : α → ℝ) (hp : ∀ a∈s, 0 ≤ p a) (hq : ∀ a∈s, 0 ≤ q a)
    (hp1 : ∑a∈s, p a=1) (hq1 : ∑a∈s, q a=1) :
    js s p q ≤ totalVariation s p q*Real.log 2 := by
  let P : Bool → α → ℝ := fun b => if b then p else q
  have hh := mixture_information_common Finset.univ s (fun _ : Bool => (1/2 : ℝ))
    P (fun a => min (p a) (q a)) (by intros; positivity)
    (by norm_num [Fintype.sum_bool]) (by intro b _; cases b <;> assumption)
    (fun a ha => le_min (hp a ha) (hq a ha)) (by
      intro b _ a _
      cases b
      · exact min_le_right _ _
      · exact min_le_left _ _)
  have he : (fun a => ∑ b : Bool, (1/2 : ℝ)*P b a)=fun a => (p a+q a)/2 := by
    funext a
    simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte]
    ring
  rw [he, sum_min_eq_one_sub_tv s p q hp1 hq1] at hh
  have hb : entropy Finset.univ (fun _ : Bool => (1/2 : ℝ))=Real.log 2 := by
    simp only [entropy, Fintype.sum_bool]
    change -(1/2 : ℝ)*Real.log (1/2)+(-(1/2 : ℝ)*Real.log (1/2))=_
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  rw [hb] at hh
  simp only [Fintype.sum_bool, P, Bool.false_eq_true, ↓reduceIte] at hh
  unfold js
  linarith

theorem totalVariation_triangle {α : Type uα} (s : Finset α) (p q r : α → ℝ) :
    totalVariation s p r ≤ totalVariation s p q+totalVariation s q r := by
  unfold totalVariation
  rw [← add_div, ← Finset.sum_add_distrib]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => abs_sub_le _ _ _)) (by norm_num)

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteDistribution ----
namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension

namespace FiniteDistribution

attribute [local instance] Classical.propDecidable

theorem entropy_on {α : Type uα} (p : FiniteDistribution α) (s : Finset α)
    (hs : p.support ⊆ s) : p.entropy=FiniteEntropy.entropy s p.weight := by
  apply tsum_eq_sum
  intro a ha
  rw [p.vanish a (fun h => ha (hs h)), Real.negMulLog_zero]

theorem tv_on {α : Type uα} (p q : FiniteDistribution α) (s : Finset α)
    (hp : p.support ⊆ s) (hq : q.support ⊆ s) : p.tv q=FiniteEntropy.totalVariation s p.weight q.weight := by
  unfold tv FiniteEntropy.totalVariation
  congr 1
  apply tsum_eq_sum
  intro a ha
  rw [p.vanish a (fun h => ha (hp h)), q.vanish a (fun h => ha (hq h)), sub_self, abs_zero]

theorem js_on {α : Type uα} (p q : FiniteDistribution α) (s : Finset α)
    (hp : p.support ⊆ s) (hq : q.support ⊆ s) : p.js q=FiniteEntropy.js s p.weight q.weight := by
  classical
  rw [js, (p.mix q).entropy_on s (Finset.union_subset hp hq), p.entropy_on s hp, q.entropy_on s hq]
  rfl

theorem js_nonneg {α : Type uα} (p q : FiniteDistribution α) : 0 ≤ p.js q := by
  classical
  rw [p.js_on q (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right]
  exact FiniteEntropy.js_nonneg _ _ _ (fun a _ => p.nonneg a) (fun a _ => q.nonneg a)
    (p.sum_on _ Finset.subset_union_left) (q.sum_on _ Finset.subset_union_right)

theorem tv_nonneg {α : Type uα} (p q : FiniteDistribution α) : 0 ≤ p.tv q :=
  div_nonneg (tsum_nonneg (fun a => abs_nonneg _)) (by norm_num)

theorem tv_sq_le_two_js {α : Type uα} (p q : FiniteDistribution α) : (p.tv q)^2 ≤ 2*p.js q := by
  classical
  rw [p.tv_on q (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right,
    p.js_on q (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right]
  exact FiniteEntropy.totalVariation_sq_le_two_js _ _ _ (fun a _ => p.nonneg a) (fun a _ => q.nonneg a)
    (p.sum_on _ Finset.subset_union_left) (q.sum_on _ Finset.subset_union_right)

theorem js_le_tv {α : Type uα} (p q : FiniteDistribution α) : p.js q ≤ p.tv q*Real.log 2 := by
  classical
  rw [p.tv_on q (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right,
    p.js_on q (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right]
  exact FiniteEntropy.js_le_tv _ _ _ (fun a _ => p.nonneg a) (fun a _ => q.nonneg a)
    (p.sum_on _ Finset.subset_union_left) (q.sum_on _ Finset.subset_union_right)

theorem tv_triangle {α : Type uα} (p q r : FiniteDistribution α) : p.tv r ≤ p.tv q+q.tv r := by
  classical
  let s := p.support ∪ q.support ∪ r.support
  have hp : p.support ⊆ s := Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  have hq : q.support ⊆ s := Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  have hr : r.support ⊆ s := Finset.subset_union_right
  rw [p.tv_on r s hp hr, p.tv_on q s hp hq, q.tv_on r s hq hr]
  exact FiniteEntropy.totalVariation_triangle _ _ _ _

theorem map_weight_on {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f : α → β)
    (s : Finset α) (hs : p.support ⊆ s) (b : β) :
    (p.map f).weight b=FiniteEntropy.mass s p.weight f b := by
  classical
  exact FiniteEntropy.mass_subset p.weight f hs (fun a _ ha => p.vanish a ha) b

theorem entropy_map_on {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f : α → β)
    (s : Finset α) (hs : p.support ⊆ s) :
    (p.map f).entropy=FiniteEntropy.observableEntropy s p.weight f := by
  classical
  rw [(p.map f).entropy_on (s.image f) (Finset.image_subset_image hs)]
  unfold FiniteEntropy.observableEntropy FiniteEntropy.entropy
  exact Finset.sum_congr rfl (fun b _ => congrArg Real.negMulLog (p.map_weight_on f s hs b))

theorem mix_map_entropy {α : Type uα} {β : Type uβ} (p q : FiniteDistribution α) (f : α → β)
    (s : Finset α) (hp : p.support ⊆ s) (hq : q.support ⊆ s) :
    ((p.map f).mix (q.map f)).entropy=
      FiniteEntropy.observableEntropy s (fun a => (p.weight a+q.weight a)/2) f := by
  classical
  rw [((p.map f).mix (q.map f)).entropy_on (s.image f)
    (Finset.union_subset (Finset.image_subset_image hp) (Finset.image_subset_image hq))]
  unfold FiniteEntropy.observableEntropy FiniteEntropy.entropy
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  change ((p.map f).weight b+(q.map f).weight b)/2=_
  rw [p.map_weight_on f s hp, q.map_weight_on f s hq]
  simp only [FiniteEntropy.mass, ← Finset.sum_div, Finset.sum_add_distrib]

theorem js_map_le {α : Type uα} {β : Type uβ} (p q : FiniteDistribution α) (f : α → β) :
    (p.map f).js (q.map f) ≤ p.js q := by
  classical
  let s := p.support ∪ q.support
  have hp : p.support ⊆ s := Finset.subset_union_left
  have hq : q.support ⊆ s := Finset.subset_union_right
  rw [js, mix_map_entropy p q f s hp hq, p.entropy_map_on f s hp,
    q.entropy_map_on f s hq, p.js_on q s hp hq]
  exact FiniteEntropy.js_observable_le s _ _ (fun a _ => p.nonneg a) (fun a _ => q.nonneg a)
    (p.sum_on s hp) (q.sum_on s hq) f

theorem entropy_congr {α : Type uα} (p q : FiniteDistribution α) (h : p.weight=q.weight) :
    p.entropy=q.entropy := by
  unfold entropy
  rw [h]

theorem tv_congr {α : Type uα} (p q p' q' : FiniteDistribution α)
    (hp : p.weight=p'.weight) (hq : q.weight=q'.weight) : p.tv q=p'.tv q' := by
  unfold tv
  rw [hp,hq]

theorem js_congr {α : Type uα} (p q p' q' : FiniteDistribution α)
    (hp : p.weight=p'.weight) (hq : q.weight=q'.weight) : p.js q=p'.js q' := by
  unfold js
  rw [p.entropy_congr p' hp,q.entropy_congr q' hq]
  congr 1
  apply entropy_congr
  funext a
  change (p.weight a+q.weight a)/2=(p'.weight a+q'.weight a)/2
  rw [hp,hq]

theorem map_weight_comp {α : Type uα} {β : Type uβ} {γ : Type uγ} (p : FiniteDistribution α) (f : α → β) (g : β → γ) :
    ((p.map f).map g).weight=(p.map (g ∘ f)).weight := by
  funext c
  exact FiniteEntropy.mass_comp p.support p.weight f g c

theorem map_weight_of_injective {α : Type uα} {β : Type uβ} (p : FiniteDistribution α)
    (f : α → β) (hf : Function.Injective f) (a : α) :
    (p.map f).weight (f a)=p.weight a := by
  change FiniteEntropy.mass p.support p.weight f (f a)=p.weight a
  simp only [FiniteEntropy.mass, Finset.sum_filter, hf.eq_iff]
  rw [Finset.sum_ite_eq']
  by_cases ha : a ∈ p.support
  · simp only [ha, ↓reduceIte]
  · simp only [ha, ↓reduceIte, p.vanish a ha]

theorem entropy_map_injective {α : Type uα} {β : Type uβ} (p : FiniteDistribution α)
    (f : α → β) (hf : Function.Injective f) : (p.map f).entropy=p.entropy := by
  have hn : p.support.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hh := p.sum_one
    simp only [he, Finset.sum_empty] at hh
    norm_num at hh
  obtain ⟨a,_⟩ := hn
  let : Nonempty α := ⟨a⟩
  let : Nonempty β := ⟨f a⟩
  rw [p.entropy_map_on f p.support (fun _ h => h), p.entropy_on p.support (fun _ h => h)]
  exact FiniteEntropy.observableEntropy_of_injective _ _ _ (fun a _ => p.nonneg a) hf

theorem tv_map_injective {α : Type uα} {β : Type uβ} (p q : FiniteDistribution α)
    (f : α → β) (hf : Function.Injective f) : (p.map f).tv (q.map f)=p.tv q := by
  let s := p.support ∪ q.support
  have hp : p.support ⊆ s := Finset.subset_union_left
  have hq : q.support ⊆ s := Finset.subset_union_right
  rw [(p.map f).tv_on (q.map f) (s.image f)
    (Finset.image_subset_image hp) (Finset.image_subset_image hq), p.tv_on q s hp hq]
  unfold FiniteEntropy.totalVariation
  rw [Finset.sum_image (fun a _ b _ hab => hf hab)]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [p.map_weight_of_injective f hf, q.map_weight_of_injective f hf]

theorem translate_weight (p : FiniteDistribution ℤ) (j a : ℤ) :
    (p.translate j).weight a=p.weight (a-j) := by
  change (p.map (fun a => a+j)).weight a=p.weight (a-j)
  convert p.map_weight_of_injective (fun a => a+j) (add_left_injective j) (a-j) using 1; simp

theorem tv_translate (p q : FiniteDistribution ℤ) (j : ℤ) :
    (p.translate j).tv (q.translate j)=p.tv q :=
  p.tv_map_injective q _ (add_left_injective j)

theorem translate_add (p : FiniteDistribution ℤ) (i j : ℤ) :
    ((p.translate i).translate j).weight=(p.translate (i+j)).weight := by
  funext a
  rw [translate_weight,translate_weight,translate_weight]
  congr 1
  omega

theorem tv_translate_two (p : FiniteDistribution ℤ) :
    p.tv (p.translate 2) ≤ 2*p.tv (p.translate 1) := by
  have hh := tv_triangle p (p.translate 1) (p.translate 2)
  have he : (p.translate 1).tv (p.translate 2)=p.tv (p.translate 1) := by
    rw [← p.tv_translate (p.translate 1) 1]
    exact tv_congr _ _ _ _ rfl (p.translate_add 1 1).symm
  rw [he] at hh
  linarith

theorem js_two_step_coarsen (p : FiniteDistribution ℤ) (f : ℤ → ℤ) :
    ((p.map f).js ((p.translate 2).map f))^2 ≤
      8*(Real.log 2)^2*p.js (p.translate 1) := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h0 := js_nonneg (p.map f) ((p.translate 2).map f)
  have h1 := (js_map_le p (p.translate 2) f).trans (js_le_tv p (p.translate 2))
  have h2 := mul_le_mul_of_nonneg_right (tv_translate_two p) hlog
  have h3 := tv_sq_le_two_js p (p.translate 1)
  have htv := tv_nonneg p (p.translate 1)
  have hh : ((p.map f).js ((p.translate 2).map f))^2 ≤
      (2*p.tv (p.translate 1)*Real.log 2)^2 := by
    exact sq_le_sq₀ h0 (by positivity) |>.mpr (h1.trans h2)
  nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg (Real.log 2))]

theorem tv_le_one {α : Type uα} (p q : FiniteDistribution α) : p.tv q ≤ 1 := by
  let s := p.support ∪ q.support
  have hp : p.support ⊆ s := Finset.subset_union_left
  have hq : q.support ⊆ s := Finset.subset_union_right
  rw [p.tv_on q s hp hq]
  unfold FiniteEntropy.totalVariation
  have hh : (∑ a ∈ s, |p.weight a-q.weight a|) ≤ 2 := by
    calc
      _ ≤ ∑ a ∈ s, (p.weight a+q.weight a) := by
        apply Finset.sum_le_sum
        intro a _
        exact abs_sub_le_iff.mpr ⟨by linarith [q.nonneg a], by linarith [p.nonneg a]⟩
      _ = 2 := by rw [Finset.sum_add_distrib, p.sum_on s hp, q.sum_on s hq]; norm_num
  linarith

theorem js_le_log_two {α : Type uα} (p q : FiniteDistribution α) : p.js q ≤ Real.log 2 := by
  calc
    _ ≤ p.tv q*Real.log 2 := js_le_tv p q
    _ ≤ 1*Real.log 2 := mul_le_mul_of_nonneg_right (tv_le_one p q) (Real.log_nonneg (by norm_num))
    _ = _ := one_mul _

theorem map_translate_div_two (p : FiniteDistribution ℤ) :
    ((p.translate 2).map (fun n => n/2)).weight=
      ((p.map (fun n => n/2)).translate 1).weight := by
  change ((p.map (fun n => n+2)).map (fun n => n/2)).weight=
    ((p.map (fun n => n/2)).map (fun n => n+1)).weight
  rw [map_weight_comp, map_weight_comp]
  congr 2
  funext n
  dsimp only [Function.comp_apply]
  omega

end FiniteDistribution

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.MeasureEntropy ----
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace MeasureEntropy

theorem mass_le_one {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → β) (b : β) : mass μ f b ≤ 1 := by
  exact (measureReal_mono (Set.subset_univ _)).trans_eq (by simp)

theorem entropy_nonneg {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → β) : 0 ≤ entropy μ f :=
  tsum_nonneg (fun b => Real.negMulLog_nonneg (mass_nonneg μ f b) (mass_le_one μ f b))

theorem entropy_eq_sum {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) :
    entropy μ f = ∑ b ∈ s, Real.negMulLog (mass μ f b) := by
  apply tsum_eq_sum
  intro b hb
  rw [mass_eq_zero_of_ae μ f s hs hb, Real.negMulLog_zero]

theorem label_joint_measurable (s : ℝ) : Measurable (fun ux : ℝ × ℝ => label s ux.1 ux.2) :=
  ((measurable_snd.div_const s).add measurable_fst).floor

theorem measurable_mass_label (μ : Measure ℝ) [IsFiniteMeasure μ] (s : ℝ) (b : ℤ) :
    Measurable (fun u => mass μ (label s u) b) := by
  have h := measurable_measure_prodMk_left (ν := μ)
    ((measurableSet_singleton b).preimage (label_joint_measurable s))
  exact h.ennreal_toReal

theorem measurable_grid (μ : Measure ℝ) [IsFiniteMeasure μ] (s : ℝ) :
    Measurable (grid μ s) :=
  Measurable.tsum (fun b => Real.continuous_negMulLog.measurable.comp (measurable_mass_label μ s b))

theorem label_ae_uniform (μ : Measure ℝ) {B s u : ℝ} (hs : 0 < s)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ x ∂μ, label s u x ∈ Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋ := by
  filter_upwards [label_ae_finite μ hs hB] with x hx
  obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hx
  exact Finset.mem_Icc.mpr ⟨(Int.floor_le_floor (by linarith [hu.1] : -B/s ≤ -B/s+u)).trans hlo,
    hhi.trans (Int.floor_le_floor (by linarith [hu.2] : B/s+u ≤ B/s+1))⟩

theorem grid_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (s u : ℝ) : 0 ≤ grid μ s u :=
  entropy_nonneg μ _

theorem grid_le_card (μ : Measure ℝ) [IsProbabilityMeasure μ] {B s u : ℝ} (hs : 0 < s)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    grid μ s u ≤ (Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card := by
  rw [grid, entropy_eq_sum μ _ _ (label_ae_uniform μ hs hB hu)]
  calc
    _ ≤ ∑ b ∈ Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro b _
      exact (Real.negMulLog_le_one_sub_self (mass_nonneg μ _ b)).trans
        (sub_le_self _ (mass_nonneg μ _ b))
    _ = _ := by simp

theorem grid_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    {s : ℝ} (hs : 0 < s) : Integrable (grid μ s) (volume.restrict (Set.Icc 0 1)) := by
  obtain ⟨B,_,hB⟩ := hμ
  apply (integrable_const ((Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card : ℝ)).mono'
    (measurable_grid μ s).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (grid_nonneg μ s u)]
  exact grid_le_card μ hs hB hu

theorem mass_comp {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq γ]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) (g : β → γ) (c : γ) :
    mass μ (g ∘ f) c = FiniteEntropy.mass s (mass μ f) g c := by
  classical
  let t := s.filter (fun b => g b = c)
  have hd : (↑t : Set β).PairwiseDisjoint (fun b => {x | f x = b}) := by
    intro b _ d _ hbd
    exact Set.disjoint_left.mpr (fun _ hx hy => hbd (hx.symm.trans hy))
  have he : {x | g (f x) = c} =ᵐ[μ] ⋃ b ∈ t, {x | f x = b} := by
    filter_upwards [hs] with x hx
    apply propext
    change (g (f x) = c) ↔ x ∈ ⋃ b ∈ t, {x | f x = b}
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨f x,Finset.mem_filter.mpr ⟨hx,h⟩,rfl⟩
    · rintro ⟨b,hb,he⟩
      exact he ▸ (Finset.mem_filter.mp hb).2
  unfold mass
  change μ.real {x | g (f x) = c} = _
  rw [measureReal_congr he, measureReal_biUnion_finset hd]
  · rfl
  · intro b _
    exact (measurableSet_singleton b).preimage hf

theorem entropy_comp {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq γ]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) (g : β → γ) :
    entropy μ (g ∘ f) = FiniteEntropy.observableEntropy s (mass μ f) g := by
  classical
  rw [entropy_eq_sum μ (g ∘ f) (s.image g) (hs.mono (fun _ hx => Finset.mem_image_of_mem g hx))]
  exact Finset.sum_congr rfl (fun b _ => congrArg Real.negMulLog (mass_comp μ f hf s hs g b))

theorem entropy_comp_injective {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq γ] [Nonempty β] [Nonempty γ]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) (g : β → γ) (hg : Function.Injective g) :
    entropy μ (g ∘ f) = entropy μ f := by
  rw [entropy_comp μ f hf s hs g, FiniteEntropy.observableEntropy_of_injective s _ g
    (fun b _ => mass_nonneg μ f b) hg, entropy_eq_sum μ f s hs]
  rfl

theorem mass_map {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : Measure α) (f : α → β) (hf : Measurable f) (g : β → γ) (hg : Measurable g) (c : γ) :
    mass (μ.map f) g c = mass μ (g ∘ f) c := by
  unfold mass Measure.real
  change ((μ.map f) (g ⁻¹' {c})).toReal = _
  rw [Measure.map_apply hf ((measurableSet_singleton c).preimage hg)]
  rfl

theorem entropy_map {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ]
    (μ : Measure α) (f : α → β) (hf : Measurable f) (g : β → γ) (hg : Measurable g) :
    entropy (μ.map f) g = entropy μ (g ∘ f) := by
  exact tsum_congr (fun c => congrArg Real.negMulLog (mass_map μ f hf g hg c))

theorem grid_periodic (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) : Function.Periodic (grid μ s) 1 := by
  intro u
  obtain ⟨B,_,hB⟩ := hμ
  have he : label s (u+1) = (fun b : ℤ => b+1) ∘ label s u := by
    funext x
    simp only [label, Function.comp_apply]
    rw [← add_assoc, Int.floor_add_one]
  rw [grid, he, entropy_comp_injective μ (label s u) (label_measurable s u)
    _ (label_ae_finite μ hs hB) _ (add_left_injective 1)]
  rfl

theorem grid_translate (μ : Measure ℝ) (s u b : ℝ) :
    grid (μ.map (fun x => x+b)) s u = grid μ s (u+b/s) := by
  rw [grid, entropy_map μ (fun x => x+b) (measurable_id.add_const b) _ (label_measurable s u)]
  congr 1
  funext x
  simp only [Function.comp_apply, label, add_div]
  congr 1
  ring

theorem grid_scale_pos (μ : Measure ℝ) {a s : ℝ} (_ha : 0 < a) (u : ℝ) :
    grid (μ.map (fun x => a*x)) s u = grid μ (s/a) u := by
  rw [grid, entropy_map μ (fun x => a*x) (measurable_const.mul measurable_id) _ (label_measurable s u)]
  congr 1
  funext x
  simp only [Function.comp_apply, label]
  congr 2
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem entropy_comp_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq γ]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
    (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) (g : β → γ) :
    entropy μ (g ∘ f) ≤ entropy μ f := by
  rw [entropy_comp μ f hf s hs g, entropy_eq_sum μ f s hs]
  exact FiniteEntropy.observableEntropy_le s _ g (fun b _ => mass_nonneg μ f b)

theorem entropy_pair_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass β] [MeasurableSingletonClass γ]
    [DecidableEq β] [DecidableEq γ]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → β) (hf : Measurable f)
    (g : α → γ) (hg : Measurable g) (s : Finset β) (t : Finset γ)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (ht : ∀ᵐ x ∂μ, g x ∈ t) :
    entropy μ (fun x => (f x,g x)) ≤ entropy μ f + entropy μ g := by
  classical
  let F := fun x => (f x,g x)
  have hF : Measurable F := hf.prodMk hg
  have hst : ∀ᵐ x ∂μ, F x ∈ s ×ˢ t := by
    filter_upwards [hs,ht] with x hx hy
    exact Finset.mem_product.mpr ⟨hx,hy⟩
  have h := FiniteEntropy.observableEntropy_pair_le (s ×ˢ t) (mass μ F) Prod.fst Prod.snd
    (fun b _ => mass_nonneg μ F b) (mass_sum μ F hF (s ×ˢ t) hst)
  have hid : (fun b : β × γ => (b.1,b.2)) = id := rfl
  rw [hid, FiniteEntropy.observableEntropy_id] at h
  have hfst := entropy_comp μ F hF (s ×ˢ t) hst Prod.fst
  have hsnd := entropy_comp μ F hF (s ×ˢ t) hst Prod.snd
  change entropy μ f = _ at hfst
  change entropy μ g = _ at hsnd
  rw [hfst, hsnd, entropy_eq_sum μ F (s ×ˢ t) hst]
  exact h

theorem averaged_eq_intervalIntegral (μ : Measure ℝ) (s : ℝ) :
    averaged μ s = ∫ u in (0 : ℝ)..1, grid μ s u := by
  rw [averaged, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

theorem grid_intervalIntegrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (a b : ℝ) :
    IntervalIntegrable (grid μ s) volume a b := by
  apply (grid_periodic μ hμ hs).intervalIntegrable₀ one_ne_zero
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr (grid_integrable μ hμ hs)

theorem averaged_translate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (b : ℝ) :
    averaged (μ.map (fun x => x+b)) s = averaged μ s := by
  simp only [averaged_eq_intervalIntegral, grid_translate]
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm (1 : ℝ)] using
    (grid_periodic μ hμ hs).intervalIntegral_add_eq (b/s) 0

theorem averaged_scale_pos (μ : Measure ℝ) {a s : ℝ} (ha : 0 < a) :
    averaged (μ.map (fun x => a*x)) s = averaged μ (s/a) := by
  unfold averaged
  exact integral_congr_ae (Filter.Eventually.of_forall (grid_scale_pos μ ha))

theorem averaged_grid_nsmul (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    (∫ u in (0 : ℝ)..1, grid μ s ((N : ℝ)*u)) = averaged μ s := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [intervalIntegral.integral_comp_mul_left _ hNr, mul_zero, mul_one]
  have he := (grid_periodic μ hμ hs).intervalIntegral_add_zsmul_eq (N : ℤ) 0
    (grid_intervalIntegrable μ hμ hs)
  simp only [zsmul_eq_mul, zero_add, Int.cast_natCast, mul_one] at he
  rw [he, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hNr, one_mul, averaged_eq_intervalIntegral]

theorem label_nested (s u x : ℝ) {N : ℕ} (hN : 0 < N) :
    label ((N : ℝ)*s) u x = label s ((N : ℝ)*u) x / (N : ℤ) := by
  simp only [label]
  rw [← Int.floor_div_natCast]
  congr 1
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [add_div, mul_div_cancel_left₀ u hn]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem entropy_congr_ae {α : Type uα} {β : Type uβ} [MeasurableSpace α]
    (μ : Measure α) {f g : α → β} (h : f =ᵐ[μ] g) : entropy μ f = entropy μ g := by
  apply tsum_congr
  intro b
  congr 1
  apply measureReal_congr
  filter_upwards [h] with x hx
  exact congrArg (fun y => y = b) hx

theorem ae_label_reflect (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : ℝ) :
    ∀ᵐ u ∂volume, ∀ᵐ x ∂μ, label s (-u) (-x) = -label s u x - 1 := by
  have hm : MeasurableSet {ux : ℝ × ℝ | ux.2/s+ux.1 ∉ Set.range (Int.cast : ℤ → ℝ)} :=
    ((Set.countable_range (Int.cast : ℤ → ℝ)).measurableSet.preimage
      ((measurable_snd.div_const s).add measurable_fst)).compl
  have he : ∀ᵐ u ∂volume, ∀ᵐ x ∂μ, x/s+u ∉ Set.range (Int.cast : ℤ → ℝ) := by
    apply (Measure.ae_ae_comm hm).mpr
    apply Filter.Eventually.of_forall
    intro x
    have h := (Set.countable_range (fun n : ℤ => (n : ℝ)-x/s)).ae_notMem volume
    filter_upwards [h] with u hu
    rintro ⟨n,hn⟩
    apply hu
    exact ⟨n,by linarith⟩
  filter_upwards [he] with u hu
  filter_upwards [hu] with x hx
  unfold label
  rw [neg_div, ← neg_add, Int.floor_neg, (Int.ceil_eq_floor_add_one_iff_notMem _).mpr hx]
  omega

theorem grid_reflect_ae (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    (fun u => grid (μ.map Neg.neg) s (-u)) =ᵐ[volume] grid μ s := by
  filter_upwards [ae_label_reflect μ s] with u hu
  obtain ⟨B,_,hB⟩ := hμ
  rw [grid, entropy_map μ Neg.neg measurable_neg _ (label_measurable s (-u))]
  have hh : (label s (-u) ∘ Neg.neg) =ᵐ[μ] (fun b : ℤ => -b-1) ∘ label s u := hu
  rw [entropy_congr_ae μ hh, entropy_comp_injective μ (label s u)
    (label_measurable s u) _ (label_ae_finite μ hs hB) (fun b : ℤ => -b-1)]
  · rfl
  · intro a b hab
    change -a-1 = -b-1 at hab
    omega

theorem averaged_reflect (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    averaged (μ.map Neg.neg) s = averaged μ s := by
  rw [averaged_eq_intervalIntegral, averaged_eq_intervalIntegral]
  have he := intervalIntegral.integral_comp_neg (a := (-1 : ℝ)) (b := 0)
    (grid (μ.map Neg.neg) s)
  simp only [neg_zero, neg_neg] at he
  rw [← he]
  calc
    _ = ∫ u in (-1 : ℝ)..0, grid μ s u := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [grid_reflect_ae μ hμ hs] with u hu
      exact fun _ => hu
    _ = _ := by simpa only [neg_add_cancel, zero_add] using
      (grid_periodic μ hμ hs).intervalIntegral_add_eq (-1) 0

theorem CompactlyCarried.map_affine {μ : Measure ℝ} (hμ : CompactlyCarried μ) (a b : ℝ) :
    CompactlyCarried (μ.map (fun x => a*x+b)) := by
  obtain ⟨B,hB,hμB⟩ := hμ
  let C := |a| * B + |b|
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  rw [Measure.map_apply (f := fun x : ℝ => a*x+b) (by fun_prop) measurableSet_Icc.compl]
  apply measure_mono_null _ hμB
  intro x hx hxin
  apply hx
  have hxb : |x| ≤ B := abs_le.mpr hxin
  have hax : |a*x+b| ≤ C := (abs_add_le _ _).trans (by
    rw [abs_mul]
    exact add_le_add_left (mul_le_mul_of_nonneg_left hxb (abs_nonneg a)) _)
  exact abs_le.mp hax

theorem averaged_scale (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s a : ℝ} (hs : 0 < s) (ha : a ≠ 0) :
    averaged (μ.map (fun x => a*x)) s = averaged μ (s/|a|) := by
  rcases ha.lt_or_gt with ha | ha
  · have hn : 0 < -a := neg_pos.mpr ha
    have hp : IsProbabilityMeasure (μ.map Neg.neg) := (Measure.isProbabilityMeasure_map_iff measurable_neg.aemeasurable).2 inferInstance
    let := hp
    have hc : CompactlyCarried (μ.map Neg.neg) := by
      convert hμ.map_affine (-1) 0 using 1; simp
    have hm : μ.map (fun x => a*x) = (μ.map Neg.neg).map (fun x => (-a)*x) := by
      rw [Measure.map_map (g := fun x : ℝ => (-a)*x) (by fun_prop) measurable_neg]
      congr 1
      funext x
      simp only [Function.comp_apply, neg_mul_neg]
    rw [hm, averaged_scale_pos _ hn, averaged_reflect μ hμ (div_pos hs hn), abs_of_neg ha]
  · rw [averaged_scale_pos μ ha, abs_of_pos ha]

theorem averaged_affine (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s a : ℝ} (hs : 0 < s) (ha : a ≠ 0) (b : ℝ) :
    averaged (μ.map (fun x => a*x+b)) s = averaged μ (s/|a|) := by
  have hp : IsProbabilityMeasure (μ.map (fun x => a*x)) := (Measure.isProbabilityMeasure_map_iff (measurable_const.mul measurable_id).aemeasurable).2 inferInstance
  let := hp
  have hc : CompactlyCarried (μ.map (fun x => a*x)) := by
    simpa only [add_zero] using hμ.map_affine a 0
  have he : μ.map (fun x => a*x+b) = (μ.map (fun x => a*x)).map (fun x => x+b) := by
    rw [Measure.map_map (g := fun x : ℝ => x+b) (f := fun x : ℝ => a*x) (by fun_prop) (by fun_prop)]
    rfl
  rw [he, averaged_translate _ hc hs b, averaged_scale μ hμ hs ha]

theorem entropy_le_add_of_reconstruct {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSingletonClass β]
    [MeasurableSingletonClass γ] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → δ) (g : α → β) (h : α → γ)
    (hg : Measurable g) (hh : Measurable h) (s : Finset β) (t : Finset γ)
    (hs : ∀ᵐ x ∂μ, g x ∈ s) (ht : ∀ᵐ x ∂μ, h x ∈ t)
    (q : β × γ → δ) (hq : ∀ᵐ x ∂μ, f x = q (g x,h x)) :
    entropy μ f ≤ entropy μ g + entropy μ h := by
  have hst : ∀ᵐ x ∂μ, (g x,h x) ∈ s ×ˢ t := by
    filter_upwards [hs,ht] with x hx hy
    exact Finset.mem_product.mpr ⟨hx,hy⟩
  calc
    entropy μ f = entropy μ (q ∘ fun x => (g x,h x)) := entropy_congr_ae μ hq
    _ ≤ entropy μ (fun x => (g x,h x)) := entropy_comp_le μ _ (hg.prodMk hh) _ hst q
    _ ≤ entropy μ g + entropy μ h := entropy_pair_le μ g hg h hh s t hs ht

theorem entropy_le_log_card {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s) :
    entropy μ f ≤ Real.log s.card := by
  rw [entropy_eq_sum μ f s hs]
  exact FiniteEntropy.entropy_le_log_card s _ (fun b _ => mass_nonneg μ f b)
    (mass_sum μ f hf s hs)

theorem floor_relative_bounds {a z b : ℝ} (ha : 0 < a) (hz : 0 ≤ z) (hz' : z < 1) :
    ⌊b+a*z⌋-⌊b⌋ ∈ Finset.Icc (0 : ℤ) ⌈a⌉ := by
  apply Finset.mem_Icc.mpr
  constructor
  · have h := Int.floor_le_floor (show b ≤ b+a*z by nlinarith)
    omega
  · have hlt : b+a*z < ((⌊b⌋+⌈a⌉+1 : ℤ) : ℝ) := by
      push_cast
      nlinarith [Int.lt_floor_add_one b, Int.le_ceil a]
    have hh := Int.floor_lt.mpr hlt
    omega

theorem relativeLabel_measurable (s t u v : ℝ) : Measurable (relativeLabel s t u v) := by
  unfold relativeLabel
  exact (label_measurable s u).sub
    (((((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp (label_measurable t v)).const_mul (t/s)).add_const u).sub_const ((t/s)*v)).floor

theorem relativeLabel_mem {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (u v x : ℝ) :
    relativeLabel s t u v x ∈ Finset.Icc (0 : ℤ) ⌈t/s⌉ := by
  let z := x/t+v-(label t v x : ℝ)
  have hz : 0 ≤ z := sub_nonneg.mpr (Int.floor_le _)
  have hz' : z < 1 := by
    change x/t+v-(⌊x/t+v⌋ : ℝ) < 1
    linarith [Int.lt_floor_add_one (x/t+v)]
  have he : (t/s)*(label t v x : ℝ)+u-(t/s)*v+(t/s)*z = x/s+u := by
    dsimp [z]
    field_simp; ring
  have h := floor_relative_bounds (b := (t/s)*(label t v x : ℝ)+u-(t/s)*v)
    (div_pos ht hs) hz hz'
  rw [he] at h
  exact h

theorem grid_le_grid_add_log (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (u v : ℝ) :
    grid μ s u ≤ grid μ t v + Real.log (⌈t/s⌉+1 : ℝ) := by
  obtain ⟨B,_,hB⟩ := hμ
  have hrel : ∀ᵐ x ∂μ, relativeLabel s t u v x ∈ Finset.Icc (0 : ℤ) ⌈t/s⌉ :=
    Filter.Eventually.of_forall (relativeLabel_mem hs ht u v)
  have he := entropy_le_add_of_reconstruct μ (label s u) (label t v) (relativeLabel s t u v)
    (label_measurable t v) (relativeLabel_measurable s t u v) _ _
    (label_ae_finite μ ht hB) hrel
    (fun p : ℤ × ℤ => ⌊(t/s)*(p.1 : ℝ)+u-(t/s)*v⌋+p.2)
    (Filter.Eventually.of_forall (fun x => by dsimp [relativeLabel]; omega))
  have hc := entropy_le_log_card μ _ (relativeLabel_measurable s t u v) _ hrel
  have hn : 0 ≤ ⌈t/s⌉+1 := by have hh := (Int.ceil_pos.mpr (div_pos ht hs)); omega
  have hcard : ((Finset.Icc (0 : ℤ) ⌈t/s⌉).card : ℝ) = (⌈t/s⌉ : ℝ)+1 := by
    rw [Int.card_Icc]
    have he := congrArg (fun k : ℤ => (k : ℝ)) (Int.toNat_of_nonneg hn)
    simpa only [sub_zero, Int.cast_natCast, Int.cast_add, Int.cast_one] using he
  rw [hcard] at hc
  exact he.trans (add_le_add_right hc _)

theorem grid_le_grid_add_log_two (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hts : t ≤ s) (u v : ℝ) :
    grid μ s u ≤ grid μ t v + Real.log 2 := by
  have hc : ⌈t/s⌉ = (1 : ℤ) := by
    have hh := Int.ceil_pos.mpr (div_pos ht hs)
    have hu : ⌈t/s⌉ ≤ (1 : ℤ) := Int.ceil_le.mpr (by
      norm_num
      exact (div_le_one hs).mpr hts)
    omega
  simpa only [hc, Int.cast_one, one_add_one_eq_two] using grid_le_grid_add_log μ hμ hs ht u v

theorem grid_le_grid_add_log_ratio (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (u v : ℝ) :
    grid μ s u ≤ grid μ t v + Real.log (t/s+2) := by
  have hc : (0 : ℝ) < (⌈t/s⌉ : ℝ)+1 := by
    have hh := Int.le_ceil (t/s)
    linarith [div_pos ht hs]
  have hu : (⌈t/s⌉ : ℝ)+1 ≤ t/s+2 := by linarith [Int.ceil_lt_add_one (t/s)]
  exact (grid_le_grid_add_log μ hμ hs ht u v).trans
    (add_le_add_right (Real.log_le_log hc hu) _)

theorem averaged_le_averaged_add_log_two (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hts : t ≤ s) :
    averaged μ s ≤ averaged μ t + Real.log 2 := by
  have hi := (grid_integrable μ hμ ht).add (integrable_const (Real.log 2))
  have hh := integral_mono_ae (grid_integrable μ hμ hs) hi
    (Filter.Eventually.of_forall (fun u => grid_le_grid_add_log_two μ hμ hs ht hts u u))
  simp only [Pi.add_apply] at hh
  rw [integral_add (grid_integrable μ hμ ht) (integrable_const _)] at hh
  simpa [averaged, integral_const, Measure.real_def] using hh

theorem averaged_le_averaged_add_log_ratio (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    averaged μ s ≤ averaged μ t + Real.log (t/s+2) := by
  have hi := (grid_integrable μ hμ ht).add (integrable_const (Real.log (t/s+2)))
  have hh := integral_mono_ae (grid_integrable μ hμ hs) hi
    (Filter.Eventually.of_forall (fun u => grid_le_grid_add_log_ratio μ hμ hs ht u u))
  simp only [Pi.add_apply] at hh
  rw [integral_add (grid_integrable μ hμ ht) (integrable_const _)] at hh
  simpa [averaged, integral_const, Measure.real_def] using hh

theorem nested_grid_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) (u : ℝ) :
    0 ≤ grid μ s ((N : ℝ)*u)-grid μ ((N : ℝ)*s) u ∧
      grid μ s ((N : ℝ)*u)-grid μ ((N : ℝ)*s) u ≤ Real.log N := by
  classical
  obtain ⟨B,_,hB⟩ := hμ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  let f := label s ((N : ℝ)*u)
  let g := label ((N : ℝ)*s) u
  have hf := label_ae_finite (u := (N : ℝ)*u) μ hs hB
  have hg := label_ae_finite (u := u) μ (mul_pos hNr hs) hB
  have hfg : g = (fun z : ℤ => z/(N : ℤ)) ∘ f := by
    funext x
    exact label_nested s u x hN
  have hlow := entropy_comp_le μ f (label_measurable _ _) _ hf (fun z : ℤ => z/(N : ℤ))
  rw [← hfg] at hlow
  have hm : Measurable (fun x => f x % (N : ℤ)) :=
    (measurable_of_countable (fun z : ℤ => z % (N : ℤ))).comp (label_measurable _ _)
  have hr : ∀ᵐ x ∂μ, f x % (N : ℤ) ∈ Finset.Ico (0 : ℤ) (N : ℤ) := by
    apply Filter.Eventually.of_forall
    intro x
    exact Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hNz.ne', Int.emod_lt_of_pos _ hNz⟩
  have hh := entropy_le_add_of_reconstruct μ f g (fun x => f x%(N : ℤ))
    (label_measurable _ _) hm _ _ hg hr
    (fun p : ℤ × ℤ => p.1*(N : ℤ)+p.2) (Filter.Eventually.of_forall (fun x => by
      rw [hfg]
      exact (Int.ediv_mul_add_emod (f x) N).symm))
  have her := entropy_le_log_card μ _ hm _ hr
  simp only [Int.card_Ico, sub_zero, Int.toNat_natCast] at her
  change entropy μ f ≤ entropy μ g + entropy μ (fun x => f x%(N : ℤ)) at hh
  change 0 ≤ entropy μ f-entropy μ g ∧ entropy μ f-entropy μ g ≤ Real.log N
  constructor <;> linarith

theorem averaged_nested_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    0 ≤ averaged μ s-averaged μ ((N : ℝ)*s) ∧
      averaged μ s-averaged μ ((N : ℝ)*s) ≤ Real.log N := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : IntervalIntegrable (fun u => grid μ s ((N : ℝ)*u)) volume 0 1 := by
    simpa only [zero_div, div_self hNr] using
      (grid_intervalIntegrable μ hμ hs 0 (N : ℝ)).comp_mul_left (c := (N : ℝ))
  have hc := grid_intervalIntegrable μ hμ (mul_pos hpos hs) 0 1
  have hi := hf.sub hc
  have hge := intervalIntegral.integral_mono zero_le_one (intervalIntegrable_const (c := (0 : ℝ))) hi
    (fun u => (nested_grid_bounds μ hμ hs hN u).1)
  have hle := intervalIntegral.integral_mono zero_le_one hi
    (intervalIntegrable_const (c := Real.log N)) (fun u => (nested_grid_bounds μ hμ hs hN u).2)
  rw [intervalIntegral.integral_sub hf hc, averaged_grid_nsmul μ hμ hs hN,
    ← averaged_eq_intervalIntegral] at hge hle
  simpa only [intervalIntegral.integral_const, sub_zero, one_smul] using And.intro hge hle

theorem mass_mixture {ι : Type uι} {α : Type uα} {β : Type uβ} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) (ν : ι → Measure α) [∀ i, IsFiniteMeasure (ν i)] (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hm : μ = ∑ i, ENNReal.ofReal (w i) • ν i) (f : α → β) (b : β) :
    mass μ f b = ∑ i, w i*mass (ν i) f b := by
  unfold mass
  rw [hm]
  simp only [Measure.real_def, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw i)]

theorem entropy_coarsening_mixture {ι : Type uι} {α : Type uα} {β : Type uβ} {γ : Type uγ} [Fintype ι]
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
    [DecidableEq β] [DecidableEq γ]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : ι → Measure α)
    [∀ i, IsProbabilityMeasure (ν i)] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : μ = ∑ i, ENNReal.ofReal (w i) • ν i)
    (f : α → β) (hf : Measurable f) (s : Finset β)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (hsi : ∀ i, ∀ᵐ x ∂ν i, f x ∈ s) (g : β → γ) :
    (∑ i, w i*(entropy (ν i) f-entropy (ν i) (g ∘ f))) ≤
      entropy μ f-entropy μ (g ∘ f) := by
  classical
  have hh := FiniteEntropy.conditionalEntropy_mixture Finset.univ s w
    (fun i => mass (ν i) f) id g (fun i _ => hw i)
    (fun i _ b _ => mass_nonneg (ν i) f b) (fun i _ => mass_sum (ν i) f hf s (hsi i))
  have he : (fun b => ∑ i, w i*mass (ν i) f b) = mass μ f :=
    funext (fun b => (mass_mixture μ ν w hw hm f b).symm)
  rw [he, FiniteEntropy.conditionalEntropy_id _ _ _ (fun b _ => mass_nonneg μ f b)] at hh
  have hi : ∀ i, FiniteEntropy.conditionalEntropy s (mass (ν i) f) id g =
      entropy (ν i) f-entropy (ν i) (g ∘ f) := by
    intro i
    rw [FiniteEntropy.conditionalEntropy_id _ _ _ (fun b _ => mass_nonneg (ν i) f b),
      ← entropy_comp (ν i) f hf s (hsi i) g, entropy_eq_sum (ν i) f s (hsi i)]
    rfl
  simp_rw [hi] at hh
  rw [← entropy_comp μ f hf s hs g] at hh
  rw [entropy_eq_sum μ f s hs]
  exact hh

theorem nested_grid_mixture {ι : Type uι} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, CompactlyCarried (ν i)) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : μ = ∑ i, ENNReal.ofReal (w i) • ν i)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) (u : ℝ) :
    (∑ i, w i*(grid (ν i) s ((N : ℝ)*u)-grid (ν i) ((N : ℝ)*s) u)) ≤
      grid μ s ((N : ℝ)*u)-grid μ ((N : ℝ)*s) u := by
  classical
  obtain ⟨B,_,hB⟩ := hμ
  choose C hC hCi using hν
  let v := (N : ℝ)*u
  let a := Finset.Icc ⌊-B/s+v⌋ ⌊B/s+v⌋
  let ai := fun i => Finset.Icc ⌊-C i/s+v⌋ ⌊C i/s+v⌋
  let A := a ∪ Finset.univ.biUnion ai
  have ha : ∀ᵐ x ∂μ, label s v x ∈ A := (label_ae_finite μ hs hB).mono (fun x hx =>
    Finset.mem_union_left _ hx)
  have hai : ∀ i, ∀ᵐ x ∂ν i, label s v x ∈ A := by
    intro i
    filter_upwards [label_ae_finite (u := v) (ν i) hs (hCi i)] with x hx
    exact Finset.mem_union_right a (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩)
  have hh := entropy_coarsening_mixture μ ν w hw hm (label s v) (label_measurable s v)
    A ha hai (fun z : ℤ => z/(N : ℤ))
  have he : (fun z : ℤ => z/(N : ℤ)) ∘ label s v = label ((N : ℝ)*s) u := by
    funext x
    exact (label_nested s u x hN).symm
  rw [he] at hh
  exact hh

theorem grid_nsmul_intervalIntegrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    IntervalIntegrable (fun u => grid μ s ((N : ℝ)*u)) volume 0 1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simpa only [zero_div, div_self hn] using
    (grid_intervalIntegrable μ hμ hs 0 (N : ℝ)).comp_mul_left (c := (N : ℝ))

theorem averaged_nested_mixture {ι : Type uι} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)]
    (hν : ∀ i, CompactlyCarried (ν i)) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hm : μ = ∑ i, ENNReal.ofReal (w i) • ν i)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    (∑ i, w i*(averaged (ν i) s-averaged (ν i) ((N : ℝ)*s))) ≤
      averaged μ s-averaged μ ((N : ℝ)*s) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hi := fun i => (grid_nsmul_intervalIntegrable (ν i) (hν i) hs hN).sub
    (grid_intervalIntegrable (ν i) (hν i) (mul_pos hn hs) 0 1)
  have hf := (grid_nsmul_intervalIntegrable μ hμ hs hN).sub
    (grid_intervalIntegrable μ hμ (mul_pos hn hs) 0 1)
  have hh := intervalIntegral.integral_mono zero_le_one (IntervalIntegrable.sum Finset.univ
    (fun i (_ : i ∈ Finset.univ) => (hi i).const_mul (w i))) hf
      (fun u => by
        simpa only [Finset.sum_apply] using nested_grid_mixture μ hμ ν hν w hw hm hs hN u)
  simp only [Finset.sum_apply] at hh
  rw [intervalIntegral.integral_finsetSum (fun i (_ : i ∈ Finset.univ) => (hi i).const_mul (w i))] at hh
  simp_rw [intervalIntegral.integral_const_mul] at hh
  simp_rw [intervalIntegral.integral_sub (grid_nsmul_intervalIntegrable (ν _) (hν _) hs hN)
    (grid_intervalIntegrable (ν _) (hν _) (mul_pos hn hs) 0 1),
    averaged_grid_nsmul (ν _) (hν _) hs hN, ← averaged_eq_intervalIntegral] at hh
  rw [intervalIntegral.integral_sub (grid_nsmul_intervalIntegrable μ hμ hs hN)
    (grid_intervalIntegrable μ hμ (mul_pos hn hs) 0 1),
    averaged_grid_nsmul μ hμ hs hN, ← averaged_eq_intervalIntegral] at hh
  exact hh

theorem CompactlyCarried.mixture {ι : Type uι} [Fintype ι]
    (ν : ι → Measure ℝ) (hν : ∀ i, CompactlyCarried (ν i)) (w : ι → ℝ) :
    CompactlyCarried (∑ i, ENNReal.ofReal (w i) • ν i) := by
  classical
  choose C hC hCi using hν
  let B := ∑ i, C i
  have hi : ∀ i, C i ≤ B := fun i => Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i)
  refine ⟨B, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  have hz : ν i (Set.Icc (-B) B)ᶜ = 0 := measure_mono_null (by
    intro x hx hxin
    exact hx ⟨by linarith [hxin.1,hi i],by linarith [hxin.2,hi i]⟩) (hCi i)
  rw [hz, mul_zero]

theorem averaged_nested_translate_mixture {ι : Type uι} [Fintype ι]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1) (b : ι → ℝ)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    averaged μ s-averaged μ ((N : ℝ)*s) ≤
      averaged (∑ i, ENNReal.ofReal (w i) • μ.map (fun x => x+b i)) s-
      averaged (∑ i, ENNReal.ofReal (w i) • μ.map (fun x => x+b i)) ((N : ℝ)*s) := by
  let ν := fun i => μ.map (fun x => x+b i)
  have hp : ∀ i, IsProbabilityMeasure (ν i) := fun i =>
    (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const (b i)).aemeasurable).2 inferInstance
  let := hp
  have hc : ∀ i, CompactlyCarried (ν i) := fun i => by
    simpa only [one_mul] using hμ.map_affine 1 (b i)
  let ρ := ∑ i, ENNReal.ofReal (w i) • ν i
  have hpρ := mixture_probability ν w hw hw1
  let := hpρ
  have hh := averaged_nested_mixture ρ (CompactlyCarried.mixture ν hc w) ν hc w hw rfl hs hN
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have he : ∀ i, averaged (ν i) s-averaged (ν i) ((N : ℝ)*s) =
      averaged μ s-averaged μ ((N : ℝ)*s) := by
    intro i
    rw [averaged_translate μ hμ hs, averaged_translate μ hμ (mul_pos hn hs)]
  simp_rw [he] at hh
  simpa only [← Finset.sum_mul, hw1, one_mul] using hh

theorem entropy_summable {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) (a : Finset β) (ha : ∀ᵐ x ∂μ, f x ∈ a) :
    Summable (fun b => Real.negMulLog (mass μ f b)) := by
  apply summable_of_ne_finset_zero (s := a)
  intro b hb
  simp only [mass_eq_zero_of_ae μ f a ha hb, Real.negMulLog_zero]

theorem mass_summable {α : Type uα} {β : Type uβ} [MeasurableSpace α] (μ : Measure α)
    (f : α → β) (a : Finset β) (ha : ∀ᵐ x ∂μ, f x ∈ a) :
    Summable (mass μ f) := by
  apply summable_of_ne_finset_zero (s := a)
  exact fun b hb => mass_eq_zero_of_ae μ f a ha hb

theorem mass_tsum {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (a : Finset β) (ha : ∀ᵐ x ∂μ, f x ∈ a) :
    ∑' b, mass μ f b = 1 := by
  rw [tsum_eq_sum (fun b hb => mass_eq_zero_of_ae μ f a ha hb)]
  exact mass_sum μ f hf a ha

theorem fairShift_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] (v : ℝ) :
    IsProbabilityMeasure (fairShift μ v) := by
  let ν := fun i : Fin 2 => μ.map (fun x => x+(i : ℝ)*v)
  have : ∀ i, IsProbabilityMeasure (ν i) := fun i =>
    (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const _).aemeasurable).2 inferInstance
  let := this
  exact mixture_probability ν (fun _ => 1/2) (by intro; positivity) (by norm_num [Fin.sum_univ_two])

theorem CompactlyCarried.fairShift {μ : Measure ℝ} (hμ : CompactlyCarried μ) (v : ℝ) :
    CompactlyCarried (fairShift μ v) := by
  apply CompactlyCarried.mixture
  intro i
  simpa only [one_mul] using hμ.map_affine 1 ((i : ℝ)*v)

theorem label_add_scale {s : ℝ} (hs : s ≠ 0) (u x : ℝ) :
    label s u (x+s) = label s u x+1 := by
  dsimp only [label]
  rw [add_div, div_self hs]
  convert Int.floor_add_one (x/s+u) using 1
  congr 1
  ring

theorem mass_fairShift (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (u : ℝ) (j : ℤ) :
    mass (fairShift μ s) (label s u) j =
      (mass μ (label s u) j+mass μ (label s u) (j-1))/2 := by
  have hi : ∀ i : Fin 2, IsProbabilityMeasure (μ.map (fun x => x+(i : ℝ)*s)) :=
    fun i => (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const _).aemeasurable).2 inferInstance
  let := hi
  rw [mass_mixture (fairShift μ s) _ (fun _ : Fin 2 => 1/2) (by intro; positivity) rfl,
    Fin.sum_univ_two]
  simp only [Fin.val_zero, Nat.cast_zero, zero_mul, add_zero, Fin.val_one,
    Nat.cast_one, one_mul]
  rw [mass_map μ (fun x => x) measurable_id (label s u) (label_measurable s u),
    mass_map μ (fun x => x+s) (measurable_id.add_const s) (label s u) (label_measurable s u)]
  have he : mass μ ((label s u) ∘ (fun x => x+s)) j = mass μ (label s u) (j-1) := by
    unfold mass
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, Function.comp_apply, label_add_scale hs.ne']
    omega
  rw [he]
  change (1/2)*mass μ (label s u) j+(1/2)*mass μ (label s u) (j-1) = _
  ring

theorem mass_int_div_two {α : Type uα} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → ℤ) (hf : Measurable f) (k : ℤ) :
    mass μ (fun x => f x/2) k = mass μ f (2*k)+mass μ f (2*k+1) := by
  have he : {x | f x/2=k} = {x | f x=2*k} ∪ {x | f x=2*k+1} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    omega
  unfold mass
  rw [he]
  apply measureReal_union
  · exact Set.disjoint_left.mpr (by
      intro x hx hy
      simp only [Set.mem_ofPred_eq] at hx hy
      omega)
  · exact measurableSet_eq_fun hf measurable_const
  · exact measure_ne_top μ _
  · exact measure_ne_top μ _

theorem mass_nested_two (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s u : ℝ) (k : ℤ) :
    mass μ (label (2*s) (u/2)) k =
      mass μ (label s u) (2*k)+mass μ (label s u) (2*k+1) := by
  have he : label (2*s) (u/2) = fun x => label s u x/2 := by
    funext x
    simpa only [Nat.cast_ofNat, show (2 : ℝ) * (u / 2) = u by ring] using
      label_nested s (u/2) x (by norm_num : 0 < (2 : ℕ))
  rw [he, mass_int_div_two μ _ (label_measurable s u)]

theorem mass_fairShift_odd (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (u : ℝ) (k : ℤ) :
    mass (fairShift μ s) (label s u) (2*k+1) =
      mass μ (label (2*s) (u/2)) k/2 := by
  rw [mass_fairShift μ hs, mass_nested_two]
  simp only [add_sub_cancel_right]
  ring

theorem mass_fairShift_even (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : ℝ} (hs : 0 < s) (u : ℝ) (k : ℤ) :
    mass (fairShift μ s) (label s u) (2*k) =
      mass μ (label (2*s) ((u+1)/2)) k/2 := by
  have he (j : ℤ) : mass μ (label s (u+1)) j = mass μ (label s u) (j-1) := by
    unfold mass label
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, ← add_assoc, Int.floor_add_one]
    omega
  rw [mass_fairShift μ hs, mass_nested_two, he, he]
  simp only [add_sub_cancel_right]
  ring

theorem entropy_half_mass {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (a : Finset β) (ha : ∀ᵐ x ∂μ, f x ∈ a) :
    (∑' b, Real.negMulLog (mass μ f b/2)) = entropy μ f/2+Real.log 2/2 := by
  have he (b : β) : Real.negMulLog (mass μ f b/2) =
      (1/2)*Real.negMulLog (mass μ f b)+Real.negMulLog (1/2)*mass μ f b := by
    rw [div_eq_mul_inv, Real.negMulLog_mul]
    ring_nf
  simp_rw [he]
  rw [((entropy_summable μ f a ha).mul_left (1/2)).tsum_add
    ((mass_summable μ f a ha).mul_left (Real.negMulLog (1/2))),
    tsum_mul_left, tsum_mul_left, mass_tsum μ f hf a ha]
  have hc : Real.negMulLog (1/2)=Real.log 2/2 := by
    change -(1/2 : ℝ)*Real.log (1/2)=_
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  rw [hc]
  change (1/2)*entropy μ f+(Real.log 2/2)*1 = _
  ring

theorem grid_fairShift (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    grid (fairShift μ s) s u = Real.log 2+
      (grid μ (2*s) (u/2)+grid μ (2*s) ((u+1)/2))/2 := by
  classical
  obtain ⟨B,hB,hBμ⟩ := (hμ.fairShift s)
  let F := fun j => Real.negMulLog (mass (fairShift μ s) (label s u) j)
  have hf : Summable F := entropy_summable (fairShift μ s) _ _ (label_ae_finite _ hs hBμ)
  have heven : Summable (fun k : ℤ => F (k*2)) := hf.comp_injective (i := fun k : ℤ => k*2) (by
    intro a b h
    change a*2=b*2 at h
    omega)
  have hodd : Summable (fun k : ℤ => F (k*2+1)) := hf.comp_injective (i := fun k : ℤ => k*2+1) (by
    intro a b h
    change a*2+1=b*2+1 at h
    omega)
  have hprod := ((Int.divModEquiv 2).symm.summable_iff).mpr hf
  change Summable (fun p => F ((Int.divModEquiv 2).symm p)) at hprod
  change (∑' j, F j) = _
  rw [← (Int.divModEquiv 2).symm.tsum_eq F, hprod.tsum_prod]
  simp only [tsum_fintype, Fin.sum_univ_two, Int.divModEquiv_symm_apply,
    Nat.cast_ofNat, Fin.val_zero, Nat.cast_zero, add_zero, Fin.val_one, Nat.cast_one]
  rw [heven.tsum_add hodd]
  dsimp only [F]
  simp_rw [show ∀ k : ℤ, k*2=2*k from fun k => mul_comm k 2,
    mass_fairShift_even μ hs, mass_fairShift_odd μ hs]
  obtain ⟨C,hC,hCμ⟩ := hμ
  rw [entropy_half_mass μ _ (label_measurable _ _) _
      (label_ae_finite μ (by linarith : 0 < 2*s) hCμ),
    entropy_half_mass μ _ (label_measurable _ _) _
      (label_ae_finite μ (by linarith : 0 < 2*s) hCμ)]
  change grid μ (2*s) ((u+1)/2)/2+Real.log 2/2+
    (grid μ (2*s) (u/2)/2+Real.log 2/2) = _
  ring

theorem averaged_fairShift (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    averaged (fairShift μ s) s = averaged μ (2*s)+Real.log 2 := by
  have ht : 0 < 2*s := by linarith
  let f := grid μ (2*s)
  have hi0 : IntervalIntegrable (fun u => f (u/2)) volume 0 1 := by
    have h := (grid_intervalIntegrable μ hμ ht 0 (1/2)).comp_mul_left (c := (1/2 : ℝ))
    norm_num at h
    simpa only [f, div_eq_mul_inv, mul_comm, one_mul] using h
  have hi1 : IntervalIntegrable (fun u => f ((u+1)/2)) volume 0 1 := by
    have h := (grid_intervalIntegrable μ hμ ht (1/2) 1).comp_mul_left (c := (1/2 : ℝ))
    norm_num at h
    have hh := h.comp_add_right 1
    norm_num at hh
    simpa only [f, div_eq_mul_inv, mul_comm, one_mul] using hh
  have he0 : (∫ u in (0 : ℝ)..1, f (u/2)) = 2*(∫u in (0 : ℝ)..(1/2), f u) := by
    rw [intervalIntegral.integral_comp_div f (by norm_num : (2 : ℝ) ≠ 0)]
    simp only [zero_div, smul_eq_mul]
  have he1 : (∫ u in (0 : ℝ)..1, f ((u+1)/2)) = 2*(∫u in (1/2 : ℝ)..1, f u) := by
    rw [intervalIntegral.integral_comp_add_right (fun u => f (u/2)) 1]
    norm_num only [zero_add, one_add_one_eq_two]
    rw [intervalIntegral.integral_comp_div f (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num only [div_self (by norm_num : (2 : ℝ) ≠ 0), smul_eq_mul]
  rw [averaged_eq_intervalIntegral]
  calc
    _ = ∫u in (0 : ℝ)..1, Real.log 2+(f (u/2)+f ((u+1)/2))/2 := by
      apply intervalIntegral.integral_congr
      intro u _
      exact grid_fairShift μ hμ hs u
    _ = Real.log 2+(2*(∫u in (0 : ℝ)..(1/2), f u)+
        2*(∫u in (1/2 : ℝ)..1, f u))/2 := by
      rw [intervalIntegral.integral_add intervalIntegrable_const ((hi0.add hi1).div_const 2),
        intervalIntegral.integral_div, intervalIntegral.integral_add hi0 hi1, he0, he1]
      simp only [intervalIntegral.integral_const, sub_zero, one_smul]
    _ = averaged μ (2*s)+Real.log 2 := by
      have hh := intervalIntegral.integral_add_adjacent_intervals
        (grid_intervalIntegrable μ hμ ht 0 (1/2)) (grid_intervalIntegrable μ hμ ht (1/2) 1)
      change (∫u in (0 : ℝ)..(1/2), f u)+(∫u in (1/2 : ℝ)..1, f u) = _ at hh
      rw [← mul_add, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), hh,
        ← averaged_eq_intervalIntegral]
      ring

theorem gridDeficit_eq_js (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    gridDeficit μ s u=(gridLaw μ hμ hs u).js ((gridLaw μ hμ hs u).translate 1) := by
  let := fairShift_probability μ s
  let p := gridLaw μ hμ hs u
  have he : (p.mix (p.translate 1)).weight=(gridLaw (fairShift μ s) (hμ.fairShift s) hs u).weight := by
    funext b
    change (p.weight b+(p.translate 1).weight b)/2=mass (fairShift μ s) (label s u) b
    rw [FiniteDistribution.translate_weight, mass_fairShift μ hs]
    rfl
  have ht : (p.translate 1).entropy=p.entropy :=
    FiniteDistribution.entropy_map_injective p (fun a : ℤ => a+1) (add_left_injective 1)
  rw [FiniteDistribution.js, FiniteDistribution.entropy_congr _ _ he, ht]
  change grid (fairShift μ s) s u-grid μ s u=
    grid (fairShift μ s) s u-(grid μ s u+grid μ s u)/2
  ring

theorem gridDeficit_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    0 ≤ gridDeficit μ s u ∧ gridDeficit μ s u ≤ Real.log 2 := by
  rw [gridDeficit_eq_js μ hμ hs u]
  exact ⟨FiniteDistribution.js_nonneg _ _,FiniteDistribution.js_le_log_two _ _⟩

theorem gridLaw_coarsen_two (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    ((gridLaw μ hμ hs (2*u)).map (fun n : ℤ => n/2)).weight=
      (gridLaw μ hμ (mul_pos (by norm_num : (0 : ℝ)<2) hs) u).weight := by
  classical
  let : DecidableEq ℤ := fun _ _ => Classical.propDecidable _
  funext b
  rw [FiniteDistribution.map_weight_on _ _ _ (Finset.Subset.refl _)]
  change FiniteEntropy.mass (Finset.Icc ⌊-hμ.choose/s+2*u⌋ ⌊hμ.choose/s+2*u⌋) (mass μ (label s (2*u))) (fun n : ℤ => n/2) b=
    mass μ (label (2*s) u) b
  rw [← mass_comp μ (label s (2*u)) (label_measurable _ _) _
    (label_ae_finite μ hs hμ.choose_spec.2)]
  congr 1
  funext x
  symm
  simpa using label_nested s u x (by norm_num : 0 < (2 : ℕ))

theorem gridDeficit_double_sq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    (gridDeficit μ (2*s) u)^2 ≤ 8*(Real.log 2)^2*gridDeficit μ s (2*u) := by
  let p := gridLaw μ hμ hs (2*u)
  let q := gridLaw μ hμ (mul_pos (by norm_num : (0 : ℝ)<2) hs) u
  have he : (p.map (fun n => n/2)).weight=q.weight := gridLaw_coarsen_two μ hμ hs u
  have he' : ((p.translate 2).map (fun n => n/2)).weight=(q.translate 1).weight := by
    rw [FiniteDistribution.map_translate_div_two]
    funext b
    rw [FiniteDistribution.translate_weight, FiniteDistribution.translate_weight, he]
  have hh := FiniteDistribution.js_two_step_coarsen p (fun n => n/2)
  rw [FiniteDistribution.js_congr _ _ q (q.translate 1) he he'] at hh
  rw [gridDeficit_eq_js μ hμ (mul_pos (by norm_num : (0 : ℝ)<2) hs) u,
    gridDeficit_eq_js μ hμ hs (2*u)]
  exact hh

theorem gridDeficit_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    Integrable (gridDeficit μ s) (volume.restrict (Set.Icc 0 1)) := by
  let := fairShift_probability μ s
  exact (grid_integrable (fairShift μ s) (hμ.fairShift s) hs).sub (grid_integrable μ hμ hs)

theorem integral_gridDeficit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    (∫ u in Set.Icc (0 : ℝ) 1, gridDeficit μ s u)=
      Real.log 2-(averaged μ s-averaged μ (2*s)) := by
  let := fairShift_probability μ s
  simp only [gridDeficit]
  rw [integral_sub (grid_integrable _ (hμ.fairShift s) hs) (grid_integrable μ hμ hs)]
  change averaged (fairShift μ s) s-averaged μ s=_
  rw [averaged_fairShift μ hμ hs]
  ring

theorem deficit_bounds (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    0 ≤ deficit μ s ∧ deficit μ s ≤ Real.log 2 := by
  rw [deficit, ← integral_gridDeficit μ hμ hs]
  constructor
  · exact integral_nonneg (fun u => (gridDeficit_bounds μ hμ hs u).1)
  · have hh := integral_mono (gridDeficit_integrable μ hμ hs)
      (integrable_const (Real.log 2)) (fun u => (gridDeficit_bounds μ hμ hs u).2)
    simpa using hh

theorem gridDeficit_sq_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun u => (gridDeficit μ s u)^2) (volume.restrict (Set.Icc 0 1)) := by
  apply (integrable_const ((Real.log 2)^2)).mono'
    ((gridDeficit_integrable μ hμ hs).aestronglyMeasurable.pow 2)
  filter_upwards [] with u
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  obtain ⟨h0,h1⟩ := gridDeficit_bounds μ hμ hs u
  exact pow_le_pow_left₀ h0 h1 2

theorem integral_gridDeficit_double_shift (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    (∫ u in Set.Icc (0 : ℝ) 1, gridDeficit μ s (2*u))=deficit μ s := by
  let := fairShift_probability μ s
  have hi (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : CompactlyCarried ν) :
      IntervalIntegrable (fun u => grid ν s (2*u)) volume 0 1 := by
    have h := (grid_intervalIntegrable ν hν hs 0 2).comp_mul_left (c := (2 : ℝ))
    norm_num at h
    exact h
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  simp only [gridDeficit]
  have he (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν : CompactlyCarried ν) :
      (∫ u in (0 : ℝ)..1, grid ν s (2*u)) = averaged ν s := by
    simpa using averaged_grid_nsmul ν hν hs (by norm_num : 0 < (2 : ℕ))
  rw [intervalIntegral.integral_sub (hi _ (hμ.fairShift s)) (hi μ hμ),
    he _ (hμ.fairShift s), he μ hμ,
    averaged_fairShift μ hμ hs, deficit]
  ring

theorem deficit_double_sq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) :
    (deficit μ (2*s))^2 ≤ 8*(Real.log 2)^2*deficit μ s := by
  let := fairShift_probability μ s
  have ht : 0 < 2*s := mul_pos (by norm_num) hs
  let : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  have hj := (convexOn_pow (𝕜 := ℝ) 2).map_integral_le
    (continuous_pow 2).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun u => (gridDeficit_bounds μ hμ ht u).1))
    (gridDeficit_integrable μ hμ ht) (gridDeficit_sq_integrable μ hμ ht)
  rw [integral_gridDeficit μ hμ ht] at hj
  change (deficit μ (2*s))^2 ≤ _ at hj
  have hi : Integrable (fun u => gridDeficit μ s (2*u))
      (volume.restrict (Set.Icc 0 1)) := by
    apply (integrable_const (Real.log 2)).mono'
      (((measurable_grid (fairShift μ s) s).sub (measurable_grid μ s)).comp
        (measurable_const.mul measurable_id)).aestronglyMeasurable
    filter_upwards [] with u
    exact (abs_of_nonneg (gridDeficit_bounds μ hμ hs (2*u)).1).le.trans
      (gridDeficit_bounds μ hμ hs (2*u)).2
  have hh := integral_mono (gridDeficit_sq_integrable μ hμ ht)
    (hi.const_mul (8*(Real.log 2)^2)) (gridDeficit_double_sq μ hμ hs)
  change (∫ u in Set.Icc (0 : ℝ) 1, (gridDeficit μ (2*s) u)^2) ≤ _ at hh
  rw [integral_const_mul, integral_gridDeficit_double_shift μ hμ hs] at hh
  exact hj.trans hh

theorem deficit_dyadic_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℕ → ℝ) (hv : ∀ n, 0 < v n)
    (h : Filter.Tendsto (fun n => deficit μ (v n)) Filter.atTop (nhds 0)) (j : ℕ) :
    Filter.Tendsto (fun n => deficit μ ((2 : ℝ)^j*v n)) Filter.atTop (nhds 0) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    have hz : Filter.Tendsto (fun n => Real.sqrt (8*(Real.log 2)^2 *
        deficit μ ((2 : ℝ)^j*v n))) Filter.atTop (nhds 0) := by
      simpa using (ih.const_mul (8*(Real.log 2)^2)).sqrt
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hz
    · intro n
      exact (deficit_bounds μ hμ (s := (2 : ℝ)^(j+1)*v n)
        (mul_pos (pow_pos (by norm_num) _) (hv n))).1
    · intro n
      apply Real.le_sqrt_of_sq_le
      have hb := deficit_double_sq μ hμ (s := (2 : ℝ)^j*v n)
        (mul_pos (pow_pos (by norm_num) _) (hv n))
      have he : (2 : ℝ)^(j+1)*v n = 2*((2 : ℝ)^j*v n) := by rw [pow_succ]; ring
      rwa [← he] at hb

theorem sum_dyadic_deficit (μ : Measure ℝ) (s : ℝ) (K : ℕ) :
    (∑j ∈ Finset.range K, deficit μ ((2 : ℝ)^j*s))=
      K*Real.log 2-(averaged μ s-averaged μ ((2 : ℝ)^K*s)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [deficit, Nat.cast_add, Nat.cast_one, pow_succ]
    have he : 2*((2 : ℝ)^K*s)=2^K*2*s := by ring
    rw [he]
    ring

theorem wide_window_saturation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℕ → ℝ) (hv : ∀ n, 0 < v n)
    (h : Filter.Tendsto (fun n => deficit μ (v n)) Filter.atTop (nhds 0)) (K : ℕ) :
    Filter.Tendsto (fun n => averaged μ (v n)-averaged μ ((2 : ℝ)^K*v n))
      Filter.atTop (nhds (K*Real.log 2)) := by
  have hh := tendsto_finsetSum (Finset.range K) (fun j _ => deficit_dyadic_tendsto_zero μ hμ v hv h j)
  simp only [sum_dyadic_deficit, Finset.sum_const_zero] at hh
  have ht := (tendsto_const_nhds (x := (K : ℝ)*Real.log 2)).sub hh
  simpa only [sub_sub_cancel, sub_zero] using ht

end MeasureEntropy
end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.EntropyBounds ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
open MeasureEntropy

theorem stopped_lower (S : System ι) (F : ℝ → ℝ) {a v B : ℝ}
    (ha : 0 < a) (hai : ∀ i, a ≤ |S.ratio i|) (hv : 0 < v)
    (hstep : ∀ s, 0 < s → (∑ i, S.weight i*F (s/|S.ratio i|)) ≤ F s)
    (hbase : ∀ z, v ≤ z → z ≤ v/a → B ≤ F z) :
    ∀ s, 0 < s → s < v → B ≤ F s := by
  classical
  obtain ⟨c,_T,hc,hc1,_hT,hr,_ht⟩ := S.exists_uniform_bounds
  have hi : ∀ n s, 0 < s → v*c^n ≤ s → s ≤ v/a → B ≤ F s := by
    intro n
    induction n with
    | zero =>
      intro s _hs hvs hsa
      exact hbase s (by simpa using hvs) hsa
    | succ n ih =>
      intro s hs hvs hsa
      by_cases hvz : v ≤ s
      · exact hbase s hvz hsa
      have hsv : s < v := lt_of_not_ge hvz
      apply le_trans _ (hstep s hs)
      calc
        B = ∑i, S.weight i*B := by rw [← Finset.sum_mul, S.weight_sum, one_mul]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left _ (S.weight_nonneg i)
          apply ih _ (div_pos hs (S.ratio_pos i))
          · apply (le_div_iff₀ (S.ratio_pos i)).mpr
            calc
              v*c^n*|S.ratio i| ≤ v*c^n*c :=
                mul_le_mul_of_nonneg_left (hr i) (by positivity)
              _ ≤ s := by simpa only [pow_succ, mul_assoc] using hvs
          · exact (div_le_div_of_nonneg_left hv.le ha (hai i)).trans'
              (div_le_div_of_nonneg_right hsv.le (S.ratio_pos i).le)
  intro s hs hsv
  have hz : Filter.Tendsto (fun n : ℕ => v*c^n) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc1).const_mul v
  obtain ⟨n,hn⟩ := (hz.eventually (gt_mem_nhds hs)).exists
  have ha1 : a ≤ 1 := (hai (Classical.arbitrary ι)).trans
    (S.ratio_lt_one (Classical.arbitrary ι)).le
  exact hi n s hs hn.le (hsv.le.trans ((le_div_iff₀ ha).mpr (by nlinarith)))

theorem window_selfSimilar (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) {s : ℝ} (hs : 0 < s) {K : ℕ} (hK : 0 < K) :
    (∑i, S.weight i*(averaged μ (s/|S.ratio i|)-
      averaged μ ((K : ℝ)*(s/|S.ratio i|)))) ≤
      averaged μ s-averaged μ ((K : ℝ)*s) := by
  classical
  obtain ⟨B,hB,hBμ⟩ := S.selfSimilar_compact μ hμ
  have hc : CompactlyCarried μ := ⟨B,hB.le,hBμ⟩
  let : ∀ i, IsProbabilityMeasure (μ.map (S.affine i)) := fun i =>
    (Measure.isProbabilityMeasure_map_iff (S.affine_continuous i).measurable.aemeasurable).2 inferInstance
  have hh := averaged_nested_mixture μ hc (fun i => μ.map (S.affine i))
    (fun i => hc.map_affine (S.ratio i) (S.offset i)) S.weight S.weight_nonneg hμ hs hK
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  change _ = S.weight i*(averaged (μ.map (fun x => S.ratio i*x+S.offset i)) s-
    averaged (μ.map (fun x => S.ratio i*x+S.offset i)) ((K : ℝ)*s))
  rw [averaged_affine μ hc hs (abs_pos.mp (S.ratio_pos i)),
    averaged_affine μ hc (mul_pos (by exact_mod_cast hK) hs) (abs_pos.mp (S.ratio_pos i))]
  congr 2
  ring_nf

theorem stopped_window_transfer (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) {a v : ℝ} (ha : 0 < a)
    (hai : ∀ i, a ≤ |S.ratio i|) (hv : 0 < v) {K : ℕ} (hK : 0 < K)
    {s : ℝ} (hs : 0 < s) (hsv : s < v) :
    averaged μ v-averaged μ ((K : ℝ)*v)-(Real.log (1/a+2)+Real.log 2) ≤
      averaged μ s-averaged μ ((K : ℝ)*s) := by
  obtain ⟨B,hB,hBμ⟩ := S.selfSimilar_compact μ hμ
  have hc : CompactlyCarried μ := ⟨B,hB.le,hBμ⟩
  apply S.stopped_lower (fun z => averaged μ z-averaged μ ((K : ℝ)*z)) ha hai hv
    (fun z hz => S.window_selfSimilar μ hμ hz hK) _ s hs hsv
  intro z hvz hza
  have hz : 0 < z := hv.trans_le hvz
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 := averaged_le_averaged_add_log_ratio μ hc hv hz
  have h2 := averaged_le_averaged_add_log_two μ hc (mul_pos hk hz) (mul_pos hk hv)
    (mul_le_mul_of_nonneg_left hvz hk.le)
  have hlog : Real.log (z/v+2) ≤ Real.log (1/a+2) := by
    apply Real.log_le_log (by positivity)
    suffices z/v ≤ 1/a by linarith
    apply (div_le_iff₀ hv).mpr
    simpa [div_eq_mul_inv, mul_comm] using hza
  linarith

end System

namespace MeasureEntropy

theorem geometric_gain_lower (F : ℝ → ℝ) {v K B : ℝ} (hv : 0 < v) (hK : 1 < K)
    (hg : ∀ s, 0 < s → s < v → B ≤ F s-F (K*s)) (m : ℕ) :
    F v+(m : ℝ)*B ≤ F (v*(1/K)^m) := by
  have hk : 0 < K := zero_lt_one.trans hK
  have hr : 0 < 1/K := div_pos zero_lt_one hk
  have hr1 : 1/K < 1 := (div_lt_one hk).mpr hK
  induction m with
  | zero => simp
  | succ m ih =>
    have hs : 0 < v*(1/K)^(m+1) := mul_pos hv (pow_pos hr _)
    have hsv : v*(1/K)^(m+1) < v := by
      nlinarith [pow_lt_one₀ hr.le hr1 (by omega : m+1 ≠ 0)]
    have he : K*(v*(1/K)^(m+1))=v*(1/K)^m := by
      rw [pow_succ]
      field_simp
    have hh := hg _ hs hsv
    rw [he] at hh
    push_cast
    nlinarith

theorem geometric_gain_bound (F : ℝ → ℝ) {v K B d C : ℝ} (hv : 0 < v) (hK : 1 < K)
    (hu : ∀ s, 0 < s → s < 1 → F s ≤ d*Real.log (1/s)+C)
    (hg : ∀ s, 0 < s → s < v → B ≤ F s-F (K*s)) : B ≤ d*Real.log K := by
  have hk : 0 < K := zero_lt_one.trans hK
  have hr : 0 < 1/K := div_pos zero_lt_one hk
  have hr1 : 1/K < 1 := (div_lt_one hk).mpr hK
  have ht : Filter.Tendsto (fun n : ℕ => v*(1/K)^(n+1)) Filter.atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1).comp (Filter.tendsto_add_atTop_nat 1)
    simpa using h.const_mul v
  have he : ∀ᶠ n : ℕ in Filter.atTop,
      F v/((n : ℝ)+1)+B ≤ d*Real.log K + (C-d*Real.log v)/((n : ℝ)+1) := by
    filter_upwards [ht.eventually (gt_mem_nhds zero_lt_one)] with n hn
    have hg' := geometric_gain_lower F hv hK hg (n+1)
    have hu' := hu _ (mul_pos hv (pow_pos hr _)) hn
    have hlog : Real.log (1/(v*(1/K)^(n+1)))= ((n : ℝ)+1)*Real.log K-Real.log v := by
      rw [Real.log_div (by norm_num) (ne_of_gt (mul_pos hv (pow_pos hr _))), Real.log_one,
        Real.log_mul hv.ne' (pow_pos hr _).ne', Real.log_pow, Real.log_div (by norm_num) hk.ne',
        Real.log_one]
      push_cast
      ring
    rw [hlog] at hu'
    have hh : F v+((n : ℝ)+1)*B ≤ d*(((n : ℝ)+1)*Real.log K-Real.log v)+C := by
      exact_mod_cast hg'.trans hu'
    have hnpos : 0 < (n : ℝ)+1 := by positivity
    have hh' := (div_le_div_iff_of_pos_right hnpos).mpr hh
    have hl' : (F v+((n : ℝ)+1)*B)/((n : ℝ)+1) = F v/((n : ℝ)+1)+B := by
      field_simp
    have hr' : (d*(((n : ℝ)+1)*Real.log K-Real.log v)+C)/((n : ℝ)+1) =
        d*Real.log K+(C-d*Real.log v)/((n : ℝ)+1) := by
      field_simp
      ring
    rwa [hl',hr'] at hh'
  have hz : Filter.Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Filter.Tendsto (fun n : ℕ => F v/((n : ℝ)+1)+B) Filter.atTop (nhds B) := by
    simpa only [mul_one_div, mul_zero, zero_add] using (hz.const_mul (F v)).add_const B
  have hu' : Filter.Tendsto (fun n : ℕ => d*Real.log K+(C-d*Real.log v)/((n : ℝ)+1))
      Filter.atTop (nhds (d*Real.log K)) := by
    simpa only [mul_one_div, mul_zero, add_zero] using (hz.const_mul (C-d*Real.log v)).const_add (d*Real.log K)
  exact le_of_tendsto_of_tendsto hl hu' he

end MeasureEntropy

namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
open MeasureEntropy

theorem uniform_nonsaturation_of_entropy_bound (S : System ι) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ) {d C : ℝ} (hd : d < 1)
    (hu : ∀ s, 0 < s → s < 1 → averaged μ s ≤ d*Real.log (1/s)+C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v : ℝ, 0 < v → δ ≤ deficit μ v := by
  classical
  obtain ⟨B,hB,hBμ⟩ := S.selfSimilar_compact μ hμ
  have hc : CompactlyCarried μ := ⟨B,hB.le,hBμ⟩
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ (fun i => |S.ratio i|) Finset.univ_nonempty
  let a := |S.ratio i|
  have ha : 0 < a := S.ratio_pos i
  have hai : ∀ i, a ≤ |S.ratio i| := fun i => hi i (Finset.mem_univ i)
  let L := Real.log (1/a+2)+Real.log 2
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨j,hj⟩ := exists_nat_gt (max 1 ((L+1)/((1-d)*Real.log 2)))
  have hjpos : 0 < j := by have := (le_max_left _ _).trans_lt hj; exact_mod_cast (lt_trans zero_lt_one this)
  have hgap : L+1 < (1-d)*(j*Real.log 2) := by
    have hh := (div_lt_iff₀ (mul_pos (sub_pos.mpr hd) hl)).mp ((le_max_right _ _).trans_lt hj)
    nlinarith
  by_contra! h
  choose v hv hvd using fun n : ℕ => h (1/((n : ℝ)+1)) (by positivity)
  have hzero : Filter.Tendsto (fun n => deficit μ (v n)) Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat
      (fun n => (deficit_bounds μ hc (hv n)).1) (fun n => (hvd n).le)
  have hw := wide_window_saturation μ hc v hv hzero j
  obtain ⟨n,hn⟩ := (hw.eventually (lt_mem_nhds (by linarith :
    (j : ℝ)*Real.log 2-1 < j*Real.log 2))).exists
  have hk : 1 < (2 : ℝ)^j := one_lt_pow₀ (by norm_num) (by omega)
  have ht : ∀ s, 0 < s → s < v n →
      averaged μ (v n)-averaged μ ((2 : ℝ)^j*v n)-L ≤
        averaged μ s-averaged μ ((2 : ℝ)^j*s) := by
    intro s hs hsn
    simpa only [L, Nat.cast_pow, Nat.cast_ofNat] using
      S.stopped_window_transfer μ hμ ha hai (hv n) (K := 2^j) (by positivity) hs hsn
  have hh := geometric_gain_bound (averaged μ) (hv n) hk hu ht
  rw [Real.log_pow] at hh
  nlinarith

end System

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.RandomGrid ----
namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteDistribution

attribute [local instance] Classical.propDecidable

theorem entropy_map_le {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f : α → β) :
    (p.map f).entropy ≤ p.entropy := by
  classical
  rw [p.entropy_map_on f p.support (fun _ h => h),p.entropy_on p.support (fun _ h => h)]
  exact FiniteEntropy.observableEntropy_le _ _ _ (fun a _ => p.nonneg a)

theorem js_le_map_add {α : Type uα} {β : Type uβ} (p q : FiniteDistribution α) (f : α → β) :
    p.js q ≤ (p.map f).js (q.map f)+(p.mix q).entropy-((p.mix q).map f).entropy := by
  classical
  have he : ((p.map f).mix (q.map f)).entropy=((p.mix q).map f).entropy := by
    let s := p.support ∪ q.support
    rw [mix_map_entropy p q f s Finset.subset_union_left Finset.subset_union_right,
      (p.mix q).entropy_map_on f s (by exact fun _ h => h)]
    rfl
  have hp := p.entropy_map_le f
  have hq := q.entropy_map_le f
  unfold js
  rw [he]
  linarith

theorem tv_maps_le_disagreement {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f g : α → β) :
    (p.map f).tv (p.map g) ≤ ∑ a ∈ p.support, if f a = g a then 0 else p.weight a := by
  classical
  let t := (p.map f).support ∪ (p.map g).support
  rw [(p.map f).tv_on (p.map g) t Finset.subset_union_left Finset.subset_union_right]
  unfold FiniteEntropy.totalVariation
  have hm (k : α → β) (b : β) : (p.map k).weight b =
      ∑ a ∈ p.support, if k a=b then p.weight a else 0 := by
    rw [map_weight_on p k p.support (fun _ h => h)]
    simp only [FiniteEntropy.mass,Finset.sum_filter]
  have hsum : ∑ b ∈ t, |(p.map f).weight b-(p.map g).weight b| ≤
      ∑ a ∈ p.support, if f a = g a then 0 else 2*p.weight a := by
    calc
      _ ≤ ∑ b ∈ t, ∑ a ∈ p.support,
          |(if f a=b then p.weight a else 0)-(if g a=b then p.weight a else 0)| := by
        apply Finset.sum_le_sum
        intro b _
        rw [hm f b,hm g b,← Finset.sum_sub_distrib]
        exact Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        by_cases h : f a=g a
        · simp [h]
        · have hf : f a ∈ t := Finset.mem_union_left _ (Finset.mem_image_of_mem f ha)
          have hg : g a ∈ t := Finset.mem_union_right _ (Finset.mem_image_of_mem g ha)
          have habs : ∀ b, |(if f a=b then p.weight a else 0)-(if g a=b then p.weight a else 0)| =
              (if f a=b then p.weight a else 0)+(if g a=b then p.weight a else 0) := by
            intro b
            by_cases hfb : f a=b <;> by_cases hgb : g a=b
            · exact (h (hfb.trans hgb.symm)).elim
            · simp [hfb,hgb,abs_of_nonneg (p.nonneg a)]
            · simp [hfb,hgb,abs_of_nonneg (p.nonneg a)]
            · simp [hfb,hgb]
          simp_rw [habs]
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_ite_eq,hf,hg,ite_true,h,ite_false]
          ring
  have he : (∑ a ∈ p.support, if f a=g a then 0 else 2*p.weight a) =
      2*∑ a ∈ p.support, if f a=g a then 0 else p.weight a := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> ring
  rw [he] at hsum
  linarith

end FiniteDistribution
namespace RandomGrid

attribute [local instance] OAI.EntropyRateDimension.RandomGrid.unitCircleProbability
theorem hit_eq_indicator (c : AddCircle (1 : ℝ)) (r : ℝ) :
    hit c r = (Metric.closedBall c r).indicator (fun _ => (1 : ℝ)) := by
  classical
  ext u
  change (if dist u c ≤ r then 1 else 0) = (if u ∈ Metric.closedBall c r then 1 else 0)
  rfl

theorem hit_integrable (c : AddCircle (1 : ℝ)) (r : ℝ) : Integrable (hit c r) := by
  rw [hit_eq_indicator]
  exact (integrable_const 1).indicator measurableSet_closedBall

theorem integral_hit (c : AddCircle (1 : ℝ)) {r : ℝ} (hr : 0 ≤ r) :
    (∫ u, hit c r u) = min 1 (2 * r) := by
  rw [hit_eq_indicator, integral_indicator_const _ measurableSet_closedBall]
  simp only [Measure.real, AddCircle.volume_closedBall, smul_eq_mul, mul_one]
  exact ENNReal.toReal_ofReal (le_min (by norm_num) (mul_nonneg (by norm_num) hr))

theorem circle_norm_le_of_floor_ne {x y : ℝ} (h : ⌊x⌋ ≠ ⌊y⌋) :
    ‖(x : AddCircle (1 : ℝ))‖ ≤ |y - x| := by
  rw [AddCircle.norm_eq]
  simp only [inv_one, one_mul, mul_one]
  rcases lt_or_gt_of_ne h with hxy | hxy
  · apply (round_le x (⌊x⌋ + 1)).trans
    have hy : (⌊x⌋ : ℝ) + 1 ≤ y := by
      have hh : ⌊x⌋ + 1 ≤ ⌊y⌋ := hxy
      have hh' : (⌊x⌋ : ℝ) + 1 ≤ (⌊y⌋ : ℝ) := by exact_mod_cast hh
      exact hh'.trans (Int.floor_le y)
    have hx := Int.lt_floor_add_one x
    rw [Int.cast_add, Int.cast_one, abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · apply (round_le x ⌊x⌋).trans
    have hy : y ≤ (⌊x⌋ : ℝ) := by
      have hh : ⌊y⌋ + 1 ≤ ⌊x⌋ := hxy
      have hh' : (⌊y⌋ : ℝ) + 1 ≤ (⌊x⌋ : ℝ) := by exact_mod_cast hh
      exact (Int.lt_floor_add_one y).le.trans hh'
    have hx := Int.floor_le x
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
    linarith

end RandomGrid

namespace MeasureEntropy

theorem observationLaw_map_weight {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s)
    (g : β → γ) (c : γ) :
    ((observationLaw μ f hf s hs).map g).weight c = mass μ (g ∘ f) c := by
  classical
  rw [FiniteDistribution.map_weight_on _ _ s (fun _ h => h)]
  exact (mass_comp μ f hf s hs g c).symm

theorem integral_finite_observation {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → β) (hf : Measurable f) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s)
    (F : β → ℝ) : ∫ x, F (f x) ∂μ = ∑ b ∈ s, mass μ f b*F b := by
  classical
  have he : (fun x => F (f x)) =ᵐ[μ]
      fun x => ∑ b ∈ s, ({x | f x=b} : Set α).indicator (fun _ => F b) x := by
    filter_upwards [hs] with x hx
    simp only [Set.indicator_apply,Set.mem_ofPred]
    simp [Finset.sum_ite_eq,hx]
  rw [integral_congr_ae he, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro b _
    change (∫ a, (f ⁻¹' {b}).indicator (fun _ => F b) a ∂μ) = _
    rw [integral_indicator_const _ ((measurableSet_singleton b).preimage hf)]
    rfl
  · intro b _
    exact (integrable_const _).indicator ((measurableSet_singleton b).preimage hf)

theorem entropy_binary_extra {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq β]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → β) (g : α → ℤ)
    (hf : Measurable f) (hg : Measurable g) (s : Finset β)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (hg01 : ∀ᵐ x ∂μ, g x ∈ Finset.Icc (0 : ℤ) 1)
    (bad : β → Prop) [DecidablePred bad]
    (hgood : ∀ᵐ x ∂μ, ¬bad (f x) → g x=0) :
    entropy μ (fun x => (g x,f x))-entropy μ f ≤
      (∫ x, if bad (f x) then (1 : ℝ) else 0 ∂μ)*Real.log 2 := by
  classical
  let t := ((Finset.Icc (0 : ℤ) 1) ×ˢ s).filter (fun y => bad y.2 ∨ y.1=0)
  let F := fun x => (g x,f x)
  have hF : Measurable F := hg.prodMk hf
  have ht : ∀ᵐ x ∂μ, F x ∈ t := by
    filter_upwards [hs,hg01,hgood] with x hx hgx hgoodx
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hgx,hx⟩,or_iff_not_imp_left.mpr hgoodx⟩
  have hh := FiniteEntropy.conditionalEntropy_le_bad_mass t (mass μ F) Prod.fst Prod.snd bad
    (fun a _ => mass_nonneg μ F a) (by
      intro a ha b hb hab hbad
      have ha' := (Finset.mem_filter.mp ha).2.resolve_left hbad
      have hb' := (Finset.mem_filter.mp hb).2.resolve_left (hab ▸ hbad)
      exact ha'.trans hb'.symm)
  have hi : (fun a : ℤ × β => (a.1,a.2))=id := rfl
  unfold FiniteEntropy.conditionalEntropy at hh
  rw [hi,FiniteEntropy.observableEntropy_id,← entropy_comp μ F hF t ht Prod.snd] at hh
  change FiniteEntropy.entropy t (mass μ F)-entropy μ f ≤ _ at hh
  unfold FiniteEntropy.entropy at hh
  rw [← entropy_eq_sum μ F t ht] at hh
  have hbad0 : 0 ≤ ∑ a ∈ t, if bad a.2 then mass μ F a else 0 := by
    apply Finset.sum_nonneg
    intro a _
    split_ifs
    · exact mass_nonneg μ F a
    · exact le_rfl
  have hc : (t.image Prod.fst).card ≤ 2 := by
    have hsub : t.image Prod.fst ⊆ Finset.Icc (0 : ℤ) 1 := by
      rintro a ha
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hb).1).1
    simpa using Finset.card_le_card hsub
  have hl : Real.log (t.image Prod.fst).card ≤ Real.log 2 := by
    by_cases hz : (t.image Prod.fst).card=0
    · simp [hz,Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
    · apply Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz))
      exact_mod_cast hc
  have he : (∫ x, if bad (f x) then (1 : ℝ) else 0 ∂μ) =
      ∑ a ∈ t, if bad a.2 then mass μ F a else 0 := by
    have h := integral_finite_observation μ F hF t ht
      (fun a : ℤ × β => if bad a.2 then (1 : ℝ) else 0)
    simpa only [F, mul_ite, mul_one, mul_zero] using h

  rw [he]
  exact hh.trans (mul_le_mul_of_nonneg_left hl hbad0)

end MeasureEntropy

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.Boundary ----
namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace Boundary
open Set

theorem increment_periodic (a : ℝ) : Function.Periodic (increment a) 1 := by
  intro u
  simp only [increment,add_right_comm u 1 a, Int.floor_add_one, Int.cast_add, Int.cast_one]
  ring

theorem increment_bounds {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (u : ℝ) :
    0 ≤ increment a u ∧ increment a u ≤ 1 := by
  have hl := Int.floor_le_floor (show u ≤ u+a by linarith)
  have hu := Int.floor_le_floor (show u+a ≤ u+1 by linarith)
  rw [Int.floor_add_one] at hu
  have hl' : (⌊u⌋ : ℝ) ≤ (⌊u+a⌋ : ℝ) := by exact_mod_cast hl
  have hu' : (⌊u+a⌋ : ℝ) ≤ (⌊u⌋ : ℝ)+1 := by exact_mod_cast hu
  unfold increment
  constructor <;> linarith

theorem increment_measurable (a : ℝ) : Measurable (increment a) := by
  unfold increment
  exact (((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
    (measurable_id.add_const a).floor)).sub
    ((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp measurable_id.floor)

theorem increment_eq_indicator {a u : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    increment a u = (Icc (1-a) 1).indicator (fun _ => (1 : ℝ)) u := by
  have hfl : ⌊u⌋=(0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨hu.1.le,hu.2⟩
  by_cases h : 1-a ≤ u
  · have hf : ⌊u+a⌋=(1 : ℤ) := Int.floor_eq_iff.mpr (by
      norm_num
      constructor <;> linarith [hu.2])
    simp [increment,hfl,hf,Set.indicator_of_mem (show u ∈ Icc (1-a) 1 from ⟨h,hu.2.le⟩)]
  · have hf : ⌊u+a⌋=(0 : ℤ) := Int.floor_eq_zero_iff.mpr (by constructor <;> linarith [hu.1])
    simp [increment,hfl,hf,Set.indicator_of_notMem (show u ∉ Icc (1-a) 1 from fun hh => h hh.1)]

theorem integral_increment {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (∫ u in (0 : ℝ)..1, increment a u) = a := by
  rw [intervalIntegral.integral_of_le zero_le_one,integral_Ioc_eq_integral_Ioo]
  have he := setIntegral_congr_fun (μ := (volume : Measure ℝ)) measurableSet_Ioo (fun u hu => increment_eq_indicator ha ha1 hu)
  rw [he,integral_indicator measurableSet_Icc,Measure.restrict_restrict measurableSet_Icc]
  have hi : (Ioo (0 : ℝ) 1 : Set ℝ) =ᵐ[volume] (Icc 0 1 : Set ℝ) := Ioo_ae_eq_Icc
  have hs : (Icc (1-a) 1 ∩ Ioo (0 : ℝ) 1 : Set ℝ) =ᵐ[volume] (Icc (1-a) 1 : Set ℝ) := by
    filter_upwards [hi] with u hu
    change (u ∈ Ioo (0 : ℝ) 1) = (u ∈ Icc 0 1) at hu
    apply propext
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h,hu.mpr ⟨by linarith [h.1],h.2⟩⟩

  rw [Measure.restrict_congr_set hs,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Icc,smul_eq_mul,mul_one]
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ 1-(1-a))]
  ring

theorem integral_increment_shift {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (b : ℝ) :
    (∫ u in (0 : ℝ)..1, increment a (u+b)) = a := by
  rw [intervalIntegral.integral_comp_add_right]
  have h := (increment_periodic a).intervalIntegral_add_eq b 0
  simpa only [zero_add,add_comm 1 b,integral_increment ha ha1] using h

theorem increment_eq_ite {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (u : ℝ) :
    increment a u = if ⌊u+a⌋=⌊u⌋ then 0 else 1 := by
  classical
  have hl := Int.floor_le_floor (show u ≤ u+a by linarith)
  have hu := Int.floor_le_floor (show u+a ≤ u+1 by linarith)
  rw [Int.floor_add_one] at hu
  by_cases h : ⌊u+a⌋=⌊u⌋
  · simp [increment,h]
  · have he : ⌊u+a⌋=⌊u⌋+1 := by omega
    simp [increment,he]

theorem increment_prod_integrable {α : Type uα} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (b : α → ℝ) (hb : Measurable b) :
    Integrable (fun ux : ℝ × α => increment a (ux.1+b ux.2))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod μ) := by
  let : IsProbabilityMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := ⟨by simp⟩
  apply (integrable_const (1 : ℝ)).mono'
    ((increment_measurable a).comp (measurable_fst.add (hb.comp measurable_snd))).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ux => by
    change ‖increment a (ux.1+b ux.2)‖ ≤ (1 : ℝ)
    rw [Real.norm_eq_abs,abs_of_nonneg (increment_bounds ha ha1 _).1]
    exact (increment_bounds ha ha1 _).2)

theorem increment_measure_intervalIntegrable {α : Type uα} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (b : α → ℝ) (hb : Measurable b) :
    IntervalIntegrable (fun u => ∫ x, increment a (u+b x) ∂μ) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
  exact (increment_prod_integrable μ ha ha1 b hb).integral_prod_left

theorem integral_increment_measure {α : Type uα} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (b : α → ℝ) (hb : Measurable b) :
    (∫ u in (0 : ℝ)..1, ∫ x, increment a (u+b x) ∂μ) = a := by
  have hp := increment_prod_integrable μ ha ha1 b hb
  have hs : Integrable (Function.uncurry (fun u x => increment a (u+b x)))
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod μ) := by
    rw [uIoc_of_le zero_le_one]
    convert hp using 1
    rfl
  rw [intervalIntegral_integral_swap hs]
  simp only [integral_increment_shift ha ha1,integral_const,probReal_univ,one_smul]

end Boundary

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.TranslationGain ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace MeasureEntropy

attribute [local instance] Classical.propDecidable

theorem mass_halfMix {α : Type uα} {β : Type uβ} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (f : α → β) (b : β) :
    mass ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) f b = (mass μ f b+mass ν f b)/2 := by
  unfold mass
  rw [Measure.real_def, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul,smul_eq_mul,ENNReal.toReal_add
      (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _))
      (ENNReal.mul_ne_top (by norm_num) (measure_ne_top _ _))]
  simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_one,ENNReal.toReal_ofNat]
  rw [Measure.real_def,Measure.real_def]
  ring

theorem observationLaw_map_entropy {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) (s : Finset β) (hs : ∀ᵐ x ∂μ, f x ∈ s)
    (g : β → γ) :
    ((observationLaw μ f hf s hs).map g).entropy = entropy μ (g ∘ f) := by
  apply tsum_congr
  intro c
  rw [observationLaw_map_weight]

theorem mix_observationLaw_map_entropy {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α → β) (hf : Measurable f) (s t : Finset β)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (ht : ∀ᵐ x ∂ν, f x ∈ t) (g : β → γ) :
    (((observationLaw μ f hf s hs).map g).mix
      ((observationLaw ν f hf t ht).map g)).entropy =
      entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) (g ∘ f) := by
  apply tsum_congr
  intro c
  congr 1
  change (((observationLaw μ f hf s hs).map g).weight c+
    ((observationLaw ν f hf t ht).map g).weight c)/2 = _
  rw [observationLaw_map_weight,observationLaw_map_weight,mass_halfMix]

theorem js_observationLaw_map {α : Type uα} {β : Type uβ} {γ : Type uγ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α → β) (hf : Measurable f) (s t : Finset β)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (ht : ∀ᵐ x ∂ν, f x ∈ t) (g : β → γ) :
    ((observationLaw μ f hf s hs).map g).js ((observationLaw ν f hf t ht).map g) =
      information μ ν (g ∘ f) := by
  rw [FiniteDistribution.js,mix_observationLaw_map_entropy,
    observationLaw_map_entropy,observationLaw_map_entropy]
  rfl

theorem information_le_map_add {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : α → β) (hF : Measurable F) (s t : Finset β)
    (hs : ∀ᵐ x ∂μ, F x ∈ s) (ht : ∀ᵐ x ∂ν, F x ∈ t)
    (f : β → γ) (g : β → δ) :
    information μ ν (g ∘ F) ≤ information μ ν (f ∘ F)+
      entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) F-
      entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) (f ∘ F) := by
  classical
  let p := observationLaw μ F hF s hs
  let q := observationLaw ν F hF t ht
  have h := (p.js_map_le q g).trans (p.js_le_map_add q f)
  rw [js_observationLaw_map,js_observationLaw_map] at h
  have he : (p.mix q).entropy=entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) F := by
    apply tsum_congr
    intro b
    congr 1
    exact (mass_halfMix μ ν F b).symm
  have hf : ((p.mix q).map f).entropy = entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • ν) (f ∘ F) := by
    rw [(p.mix q).entropy_map_on f (p.support ∪ q.support) (fun _ h => h)]
    change FiniteEntropy.observableEntropy (p.support ∪ q.support)
      (fun a => (p.weight a+q.weight a)/2) f = _
    rw [← FiniteDistribution.mix_map_entropy p q f (p.support ∪ q.support)
      Finset.subset_union_left Finset.subset_union_right]
    exact mix_observationLaw_map_entropy μ ν F hF s t hs ht f
  rwa [he,hf] at h

theorem information_map_le_disagreement {α : Type uα} {β : Type uβ} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsProbabilityMeasure μ] (T : α → α) (hT : Measurable T)
    (f : α → β) (hf : Measurable f) (s t : Finset β)
    (hs : ∀ᵐ x ∂μ, f x ∈ s) (ht : ∀ᵐ x ∂μ, f (T x) ∈ t) :
    information μ (μ.map T) f ≤ (∫ x, if f x=f (T x) then (0 : ℝ) else 1 ∂μ)*Real.log 2 := by
  classical
  let : IsProbabilityMeasure (μ.map T) := (Measure.isProbabilityMeasure_map_iff hT.aemeasurable).2 inferInstance
  let F := fun x => (f x,f (T x))
  have hF : Measurable F := hf.prodMk (hf.comp hT)
  have hst : ∀ᵐ x ∂μ, F x ∈ s ×ˢ t := by
    filter_upwards [hs,ht] with x hx hy
    exact Finset.mem_product.mpr ⟨hx,hy⟩
  let p := observationLaw μ F hF (s ×ˢ t) hst
  have he1 : (p.map Prod.fst).entropy=entropy μ f :=
    observationLaw_map_entropy μ F hF _ hst Prod.fst
  have he2 : (p.map Prod.snd).entropy=entropy (μ.map T) f := by
    rw [observationLaw_map_entropy,entropy_map μ T hT f hf]
    rfl
  have hem : ((p.map Prod.fst).mix (p.map Prod.snd)).entropy=
      entropy ((1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • μ.map T) f := by
    apply tsum_congr
    intro b
    congr 1
    change ((p.map Prod.fst).weight b+(p.map Prod.snd).weight b)/2=_
    rw [observationLaw_map_weight,observationLaw_map_weight,mass_halfMix,
      mass_map μ T hT f hf]
    rfl
  have hi : (p.map Prod.fst).js (p.map Prod.snd)=information μ (μ.map T) f := by
    rw [FiniteDistribution.js,he1,he2,hem]
    rfl
  have hh := (p.map Prod.fst).js_le_tv (p.map Prod.snd)
  have ht' := p.tv_maps_le_disagreement Prod.fst Prod.snd
  have he : (∫ x, if f x=f (T x) then (0 : ℝ) else 1 ∂μ) =
      ∑ b ∈ p.support, if b.1=b.2 then 0 else p.weight b := by
    have h := integral_finite_observation μ F hF (s ×ˢ t) hst
      (fun b : β × β => if b.1=b.2 then (0 : ℝ) else 1)
    simpa only [F,p,observationLaw,mul_ite,mul_zero,mul_one] using h
  rw [hi] at hh
  rw [he]
  exact hh.trans (mul_le_mul_of_nonneg_right ht' (Real.log_nonneg (by norm_num)))

theorem fairShift_eq_halfMix (μ : Measure ℝ) (v : ℝ) :
    fairShift μ v = (1/2 : ℝ≥0∞) • μ+(1/2 : ℝ≥0∞) • μ.map (fun x => x+v) := by
  norm_num [fairShift,Fin.sum_univ_two, ENNReal.ofReal_div_of_pos]

theorem gridInformation_eq (μ : Measure ℝ) (v s u : ℝ) :
    gridInformation μ v s u = grid (fairShift μ v) s u-
      (grid μ s u+grid (μ.map (fun x => x+v)) s u)/2 := by
  rw [fairShift_eq_halfMix]
  rfl

theorem gridInformation_intervalIntegrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℝ) {s : ℝ} (hs : 0 < s) :
    IntervalIntegrable (gridInformation μ v s) volume 0 1 := by
  let := fairShift_probability μ v
  let : IsProbabilityMeasure (μ.map (fun x => x+v)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const v).aemeasurable).2 inferInstance
  have hc : CompactlyCarried (μ.map (fun x => x+v)) := by simpa only [one_mul] using hμ.map_affine 1 v
  have he : gridInformation μ v s = fun u => grid (fairShift μ v) s u-
      (grid μ s u+grid (μ.map (fun x => x+v)) s u)/2 := funext (gridInformation_eq μ v s)
  rw [he]
  exact (grid_intervalIntegrable _ (hμ.fairShift v) hs 0 1).sub
    (((grid_intervalIntegrable μ hμ hs 0 1).add (grid_intervalIntegrable _ hc hs 0 1)).div_const 2)

theorem integral_gridInformation (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ u in (0 : ℝ)..1, gridInformation μ v s u) = averaged (fairShift μ v) s-averaged μ s := by
  let := fairShift_probability μ v
  let : IsProbabilityMeasure (μ.map (fun x => x+v)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const v).aemeasurable).2 inferInstance
  have hc : CompactlyCarried (μ.map (fun x => x+v)) := by simpa only [one_mul] using hμ.map_affine 1 v
  simp_rw [gridInformation_eq]
  rw [intervalIntegral.integral_sub (grid_intervalIntegrable _ (hμ.fairShift v) hs 0 1)
      (((grid_intervalIntegrable μ hμ hs 0 1).add (grid_intervalIntegrable _ hc hs 0 1)).div_const 2),
    intervalIntegral.integral_div,intervalIntegral.integral_add (grid_intervalIntegrable μ hμ hs 0 1)
      (grid_intervalIntegrable _ hc hs 0 1),← averaged_eq_intervalIntegral,← averaged_eq_intervalIntegral,
    ← averaged_eq_intervalIntegral,averaged_translate μ hμ hs v]
  ring

theorem gridInformation_le_boundary (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {v t : ℝ} (hv : 0 < v) (ht : 0 < t) (hvt : v ≤ t) (u : ℝ) :
    gridInformation μ v t u ≤ (∫ x, Boundary.increment (v/t) (u+x/t) ∂μ)*Real.log 2 := by
  classical
  obtain ⟨B,_,hB⟩ := hμ
  have h1 := label_ae_finite (u := u) μ ht hB
  have he : (fun x => label t u (x+v))=label t (u+v/t) := by
    funext x
    dsimp [label]
    congr 1
    ring
  have h2 : ∀ᵐ x ∂μ, label t u (x+v) ∈ Finset.Icc ⌊-B/t+(u+v/t)⌋ ⌊B/t+(u+v/t)⌋ := by
    filter_upwards [label_ae_finite (u := u+v/t) μ ht hB] with x hx
    rwa [congrFun he x]
  have hh := information_map_le_disagreement μ (fun x => x+v) (measurable_id.add_const v)
    (label t u) (label_measurable t u) _ _ h1 h2
  have hi : (fun x => if label t u x=label t u (x+v) then (0 : ℝ) else 1) =
      fun x => Boundary.increment (v/t) (u+x/t) := by
    funext x
    rw [Boundary.increment_eq_ite (div_nonneg hv.le ht.le) ((div_le_one ht).mpr hvt)]
    have hleft : ⌊u+x/t⌋=label t u x := by dsimp [label]; rw [add_comm]
    have hright : ⌊u+x/t+v/t⌋=label t u (x+v) := by dsimp [label]; congr 1; ring
    rw [hleft,hright]
    simp only [eq_comm]
  calc
    gridInformation μ v t u ≤ _ := hh
    _ = _ := by
      congr 1
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      by_cases hz : label t u x = label t u (x+v)
      · simpa only [ite_eq_left hz] using congrFun hi x
      · simpa only [ite_eq_right hz] using congrFun hi x

theorem averaged_fairShift_gain_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {v t : ℝ} (hv : 0 < v) (ht : 0 < t) (hvt : v ≤ t) :
    averaged (fairShift μ v) t-averaged μ t ≤ (v/t)*Real.log 2 := by
  have hi := (Boundary.increment_measure_intervalIntegrable μ (div_nonneg hv.le ht.le)
    ((div_le_one ht).mpr hvt) (fun x => x/t) (measurable_id.div_const t)).mul_const (Real.log 2)
  have hh := intervalIntegral.integral_mono zero_le_one
    (gridInformation_intervalIntegrable μ hμ v ht) hi (fun u => gridInformation_le_boundary μ hμ hv ht hvt u)
  rw [integral_gridInformation μ hμ v ht,intervalIntegral.integral_mul_const,
    Boundary.integral_increment_measure μ (div_nonneg hv.le ht.le) ((div_le_one ht).mpr hvt)
      (fun x => x/t) (measurable_id.div_const t)] at hh
  exact hh

theorem relativeLabel_zero_of_good {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (u w x : ℝ)
    (hgood : ⌊u+(s/t)*(label s w x : ℝ)-(s/t)*w+s/t⌋ =
      ⌊u+(s/t)*(label s w x : ℝ)-(s/t)*w⌋) :
    relativeLabel t s u w x=0 := by
  let b := u+(s/t)*(label s w x : ℝ)-(s/t)*w
  let z := x/s+w-(label s w x : ℝ)
  have hz : 0 ≤ z := sub_nonneg.mpr (Int.floor_le _)
  have hz1 : z ≤ 1 := by
    change x/s+w-(⌊x/s+w⌋ : ℝ) ≤ 1
    linarith [Int.lt_floor_add_one (x/s+w)]
  have hl := Int.floor_le_floor (show b ≤ b+(s/t)*z from le_add_of_nonneg_right (mul_nonneg (div_pos hs ht).le hz))
  have hu := Int.floor_le_floor (show b+(s/t)*z ≤ b+s/t by nlinarith [div_pos hs ht])
  change ⌊b+s/t⌋=⌊b⌋ at hgood
  have hf : ⌊b+(s/t)*z⌋=⌊b⌋ := le_antisymm (hu.trans_eq hgood) hl
  have he : b+(s/t)*z=x/t+u := by
    dsimp [b,z]
    field_simp
    ring
  rw [he] at hf
  have hb : (s/t)*(label s w x : ℝ)+u-(s/t)*w=b := by dsimp [b]; ring
  unfold relativeLabel
  rw [hb]
  change ⌊x/t+u⌋-⌊b⌋=0
  omega

theorem gridInformation_le_fine_add_boundary (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hst : s ≤ t) (u w : ℝ) :
    gridInformation μ v t u ≤ gridInformation μ v s w+
      (∫ x, Boundary.increment (s/t) (u+((s/t)*(label s w x : ℝ)-(s/t)*w)) ∂fairShift μ v)*Real.log 2 := by
  classical
  let ν := μ.map (fun x => x+v)
  let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff (measurable_id.add_const v).aemeasurable).2 inferInstance
  let := fairShift_probability μ v
  have hcν : CompactlyCarried ν := by simpa only [one_mul] using hμ.map_affine 1 v
  have hcρ := hμ.fairShift v
  let f := label s w
  let g := relativeLabel t s u w
  let F := fun x => (g x,f x)
  have hF : Measurable F := (relativeLabel_measurable t s u w).prodMk (label_measurable s w)
  have hceil : ⌈s/t⌉=(1 : ℤ) := by
    have hl := Int.ceil_pos.mpr (div_pos hs ht)
    have hu : ⌈s/t⌉ ≤ (1 : ℤ) := Int.ceil_le.mpr (by norm_num; exact (div_le_one ht).mpr hst)
    omega
  have hg : ∀ x, g x ∈ Finset.Icc (0 : ℤ) 1 := by
    intro x
    simpa only [hceil] using relativeLabel_mem ht hs u w x
  let aμ := Finset.Icc ⌊-hμ.choose/s+w⌋ ⌊hμ.choose/s+w⌋
  let aν := Finset.Icc ⌊-hcν.choose/s+w⌋ ⌊hcν.choose/s+w⌋
  have hfμ : ∀ᵐ x ∂μ, f x ∈ aμ := label_ae_finite μ hs hμ.choose_spec.2
  have hfν : ∀ᵐ x ∂ν, f x ∈ aν := label_ae_finite ν hs hcν.choose_spec.2
  have hFμ : ∀ᵐ x ∂μ, F x ∈ (Finset.Icc (0 : ℤ) 1) ×ˢ aμ := by
    filter_upwards [hfμ] with x hx
    exact Finset.mem_product.mpr ⟨hg x,hx⟩
  have hFν : ∀ᵐ x ∂ν, F x ∈ (Finset.Icc (0 : ℤ) 1) ×ˢ aν := by
    filter_upwards [hfν] with x hx
    exact Finset.mem_product.mpr ⟨hg x,hx⟩
  let r : ℤ × ℤ → ℤ := fun p => p.1+⌊(s/t)*(p.2 : ℝ)+u-(s/t)*w⌋
  have hr : r ∘ F=label t u := by
    funext x
    dsimp [r,F,g,f,relativeLabel]
    omega
  have hh := information_le_map_add μ ν F hF _ _ hFμ hFν Prod.snd r
  rw [hr,← fairShift_eq_halfMix] at hh
  change gridInformation μ v t u ≤ gridInformation μ v s w+entropy (fairShift μ v) F-
    entropy (fairShift μ v) f at hh
  let bad : ℤ → Prop := fun k => ⌊u+(s/t)*(k : ℝ)-(s/t)*w+s/t⌋ ≠ ⌊u+(s/t)*(k : ℝ)-(s/t)*w⌋
  have hgood : ∀ᵐ x ∂fairShift μ v, ¬bad (f x) → g x=0 := by
    apply Filter.Eventually.of_forall
    intro x hx
    apply relativeLabel_zero_of_good ht hs u w x
    exact not_not.mp hx
  have hb := entropy_binary_extra (fairShift μ v) f g (label_measurable s w)
    (relativeLabel_measurable t s u w) _ (label_ae_finite (fairShift μ v) hs hcρ.choose_spec.2)
    (Filter.Eventually.of_forall hg) bad hgood
  have he : (fun x => if bad (f x) then (1 : ℝ) else 0)=
      fun x => Boundary.increment (s/t) (u+((s/t)*(label s w x : ℝ)-(s/t)*w)) := by
    funext x
    rw [Boundary.increment_eq_ite (div_pos hs ht).le ((div_le_one ht).mpr hst)]
    simp only [bad,f,add_sub_assoc,ite_not]
  rw [he] at hb
  change entropy (fairShift μ v) F-entropy (fairShift μ v) f ≤ _ at hb
  linarith

theorem averaged_fairShift_gain_compare (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) (v : ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s ≤ t) :
    averaged (fairShift μ v) t-averaged μ t ≤
      averaged (fairShift μ v) s-averaged μ s+(s/t)*Real.log 2 := by
  let := fairShift_probability μ v
  have hh (w : ℝ) : averaged (fairShift μ v) t-averaged μ t ≤
      gridInformation μ v s w+(s/t)*Real.log 2 := by
    let b := fun x => (s/t)*(label s w x : ℝ)-(s/t)*w
    have hb : Measurable b :=
      ((((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp
        (label_measurable s w)).const_mul (s/t)).sub_const ((s/t)*w))
    have hi := (intervalIntegrable_const (c := gridInformation μ v s w)).add
      ((Boundary.increment_measure_intervalIntegrable (fairShift μ v) (div_pos hs ht).le
        ((div_le_one ht).mpr hst) b hb).mul_const (Real.log 2))
    have h := intervalIntegral.integral_mono zero_le_one
      (gridInformation_intervalIntegrable μ hμ v ht) hi
      (fun u => gridInformation_le_fine_add_boundary μ hμ v hs ht hst u w)
    rw [integral_gridInformation μ hμ v ht,
      intervalIntegral.integral_add intervalIntegrable_const
        ((Boundary.increment_measure_intervalIntegrable (fairShift μ v) (div_pos hs ht).le
          ((div_le_one ht).mpr hst) b hb).mul_const (Real.log 2)),
      intervalIntegral.integral_const,intervalIntegral.integral_mul_const,
      Boundary.integral_increment_measure (fairShift μ v) (div_pos hs ht).le
        ((div_le_one ht).mpr hst) b hb] at h
    simpa only [sub_zero,one_smul] using h
  have h := intervalIntegral.integral_mono zero_le_one
    (intervalIntegrable_const (c := averaged (fairShift μ v) t-averaged μ t))
    ((gridInformation_intervalIntegrable μ hμ v hs).add intervalIntegrable_const) hh
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (gridInformation_intervalIntegrable μ hμ v hs) intervalIntegrable_const,
    integral_gridInformation μ hμ v hs,intervalIntegral.integral_const] at h
  simpa only [sub_zero,one_smul] using h

theorem two_point_gain (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s v t : ℝ} (hs : 0 < s) (hsv : s < v) (hvt : v < t) :
    deficit μ v-(s/v+v/t)*Real.log 2 ≤
      (averaged (fairShift μ v) s-averaged (fairShift μ v) t)-(averaged μ s-averaged μ t) := by
  have hv := hs.trans hsv
  have ht := hv.trans hvt
  have hf := averaged_fairShift_gain_compare μ hμ v hs hv hsv.le
  have hc := averaged_fairShift_gain_le μ hμ hv ht hvt.le
  have hd : averaged (fairShift μ v) v-averaged μ v=deficit μ v := by
    rw [averaged_fairShift μ hμ hv]
    unfold deficit
    ring
  rw [hd] at hf
  nlinarith

end MeasureEntropy

end EntropyRateDimension

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.FairPairs ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace FairPairs

theorem edge_mem_left {ν : Law} {ℓ : ℤ} (e : ν.edges ℓ) : e.val.1 ∈ ν.support := by
  classical
  exact (Finset.mem_product.mp (Finset.mem_filter.mp e.property).1).1

theorem edge_mem_right {ν : Law} {ℓ : ℤ} (e : ν.edges ℓ) : e.val.2 ∈ ν.support := by
  classical
  exact (Finset.mem_product.mp (Finset.mem_filter.mp e.property).1).2

theorem incident_sum {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) :
    ∑ x ∈ ν.support, incident w x = ∑ e, w e := by
  classical
  simp only [incident]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, edge_mem_left e, edge_mem_right e, ite_true]
  ring

theorem feasible_zero (ν : Law) (ℓ : ℤ) : Feasible (ν := ν) (ℓ := ℓ) (fun _ => 0) := by
  constructor
  · simp
  · intro x hx
    simpa [incident] using (ν.prob_pos x hx).le

theorem total_le_one {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w) :
    ∑ e, w e ≤ 1 := by
  rw [← incident_sum w, ← ν.prob_sum]
  exact Finset.sum_le_sum hw.2

theorem weight_le_one {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w)
    (e : ν.edges ℓ) : w e ≤ 1 := by
  exact (Finset.single_le_sum (fun a _ => hw.1 a) (Finset.mem_univ e)).trans (total_le_one hw)

theorem totals_nonempty (ν : Law) (ℓ : ℤ) :
    {t : ℝ | ∃ w : ν.edges ℓ → ℝ, Feasible w ∧ ∑ e, w e = t}.Nonempty :=
  ⟨0, (fun _ => 0), feasible_zero ν ℓ, by simp⟩

theorem totals_bddAbove (ν : Law) (ℓ : ℤ) :
    BddAbove {t : ℝ | ∃ w : ν.edges ℓ → ℝ, Feasible w ∧ ∑ e, w e = t} := by
  refine ⟨1, ?_⟩
  rintro t ⟨w, hw, rfl⟩
  exact total_le_one hw

theorem capacity_nonneg (ν : Law) (ℓ : ℤ) : 0 ≤ capacity ν ℓ := by
  apply le_csSup (totals_bddAbove ν ℓ)
  exact ⟨(fun _ => 0), feasible_zero ν ℓ, by simp⟩

theorem total_le_capacity {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w) :
    ∑ e, w e ≤ capacity ν ℓ :=
  le_csSup (totals_bddAbove ν ℓ) ⟨w, hw, rfl⟩

theorem feasible_isClosed (ν : Law) (ℓ : ℤ) :
    IsClosed {w : ν.edges ℓ → ℝ | Feasible w} := by
  classical
  change IsClosed ({w : ν.edges ℓ → ℝ | ∀ e, 0 ≤ w e} ∩
    {w | ∀ x ∈ ν.support, incident w x ≤ ν.prob x})
  apply IsClosed.inter
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun e => isClosed_le continuous_const (continuous_apply e))
  · simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro _
    apply isClosed_le _ continuous_const
    unfold incident
    apply continuous_finsetSum
    intro e _
    apply Continuous.add <;> split_ifs <;> fun_prop

theorem feasible_isCompact (ν : Law) (ℓ : ℤ) :
    IsCompact {w : ν.edges ℓ → ℝ | Feasible w} := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : ν.edges ℓ → ℝ) 1)).of_isClosed_subset
    (feasible_isClosed ν ℓ)
  intro w hw
  exact ⟨hw.1, weight_le_one hw⟩

theorem capacity_attained (ν : Law) (ℓ : ℤ) :
    ∃ w : ν.edges ℓ → ℝ, Feasible w ∧ ∑ e, w e = capacity ν ℓ := by
  obtain ⟨w, hw, hmax⟩ := (feasible_isCompact ν ℓ).exists_isMaxOn
    ⟨(fun _ => 0), feasible_zero ν ℓ⟩
    (continuous_finsetSum _ (fun e _ => continuous_apply e)).continuousOn
  refine ⟨w, hw, le_antisymm (total_le_capacity hw) ?_⟩
  apply csSup_le (totals_nonempty ν ℓ)
  rintro t ⟨v, hv, rfl⟩
  exact hmax hv

theorem sum_first_endpoint {α : Type uα} [DecidableEq α] (F : Finset α) (P : α × α → Prop)
    [DecidablePred P] (q : α → α → ℝ) {x : α} (hx : x ∈ F) :
    (∑ e ∈ (F ×ˢ F).filter P, if e.1 = x then q e.1 e.2 else 0) =
      ∑ y ∈ F, if P (x, y) then q x y else 0 := by
  classical
  rw [Finset.sum_filter, Finset.sum_product, Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · exact fun h => (h hx).elim

theorem sum_second_endpoint {α : Type uα} [DecidableEq α] (F : Finset α) (P : α × α → Prop)
    [DecidablePred P] (q : α → α → ℝ) {x : α} (hx : x ∈ F) :
    (∑ e ∈ (F ×ˢ F).filter P, if e.2 = x then q e.1 e.2 else 0) =
      ∑ y ∈ F, if P (y, x) then q y x else 0 := by
  classical
  rw [Finset.sum_filter, Finset.sum_product, Finset.sum_comm, Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [hy]
  · exact fun h => (h hx).elim

theorem coupling_incident {ν : Law} (ℓ : ℤ) (π : ℝ → ℝ → ℝ)
    (hsym : ∀ x ∈ ν.support, ∀ y ∈ ν.support, π x y = π y x)
    {x : ℝ} (hx : x ∈ ν.support) :
    incident (ν := ν) (ℓ := ℓ) (fun e => 2 * π e.val.1 e.val.2) x =
      ∑ y ∈ ν.support, if (2 : ℝ) ^ (-ℓ) ≤ |y - x| ∧
        |y - x| < (2 : ℝ) ^ (1 - ℓ) then π x y else 0 := by
  classical
  simp only [incident, mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [Finset.sum_coe_sort (ν.edges ℓ) (fun e : ℝ × ℝ =>
    (if e.1 = x then π e.1 e.2 else 0) + (if e.2 = x then π e.1 e.2 else 0)),
    Finset.sum_add_distrib]
  unfold Law.edges
  rw [sum_first_endpoint _ _ _ hx, sum_second_endpoint _ _ _ hx, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  rw [← hsym x hx y hy]
  rcases lt_trichotomy x y with h | h | h
  · have hxy : ¬y < x := not_lt.mpr h.le
    simp [h, hxy, abs_of_pos (sub_pos.mpr h)]
  · subst y
    have hp : 0 < (2 : ℝ) ^ (-ℓ) := zpow_pos (by norm_num) _
    simp only [lt_self_iff_false, false_and, ite_false, sub_self, abs_zero, not_le.mpr hp, add_zero]
  · have hxy : ¬x < y := not_lt.mpr h.le
    have habs : |y - x| = x - y := by rw [abs_of_neg (sub_neg.mpr h)]; ring
    simp [h, hxy, habs]

theorem coupling_band_le_capacity {ν : Law} (ℓ : ℤ) (π : ℝ → ℝ → ℝ)
    (hπ : ∀ x ∈ ν.support, ∀ y ∈ ν.support, 0 ≤ π x y)
    (hsym : ∀ x ∈ ν.support, ∀ y ∈ ν.support, π x y = π y x)
    (hrow : ∀ x ∈ ν.support, ∑ y ∈ ν.support, π x y ≤ ν.prob x) :
    (∑ x ∈ ν.support, ∑ y ∈ ν.support,
      if (2 : ℝ) ^ (-ℓ) ≤ |y - x| ∧ |y - x| < (2 : ℝ) ^ (1 - ℓ)
      then π x y else 0) ≤ capacity ν ℓ := by
  classical
  let w : ν.edges ℓ → ℝ := fun e => 2 * π e.val.1 e.val.2
  have hw : Feasible w := by
    constructor
    · intro e
      exact mul_nonneg (by norm_num) (hπ _ (edge_mem_left e) _ (edge_mem_right e))
    · intro x hx
      rw [coupling_incident ℓ π hsym hx]
      apply le_trans _ (hrow x hx)
      apply Finset.sum_le_sum
      intro y hy
      split_ifs
      · exact le_rfl
      · exact hπ x hx y hy
  calc
    _ = ∑ x ∈ ν.support, incident w x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (coupling_incident ℓ π hsym hx).symm
    _ = ∑ e, w e := incident_sum w
    _ ≤ capacity ν ℓ := total_le_capacity hw

theorem cell_mass_pos {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) {x : ℝ} (hx : x ∈ ν.support) :
    0 < FiniteEntropy.mass ν.support ν.prob g (g x) := by
  apply lt_of_lt_of_le (ν.prob_pos x hx)
  apply Finset.single_le_sum
  · intro y hy
    exact (ν.prob_pos y (Finset.mem_filter.mp hy).1).le
  · exact Finset.mem_filter.mpr ⟨hx, rfl⟩

theorem conditionalCoupling_nonneg {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) {x y : ℝ} (hx : x ∈ ν.support) (hy : y ∈ ν.support) :
    0 ≤ conditionalCoupling ν g x y := by
  unfold conditionalCoupling
  split_ifs
  · exact div_nonneg (mul_nonneg (ν.prob_pos x hx).le (ν.prob_pos y hy).le)
      (cell_mass_pos ν g hx).le
  · exact le_rfl

theorem conditionalCoupling_symm {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) (x y : ℝ) :
    conditionalCoupling ν g x y = conditionalCoupling ν g y x := by
  by_cases h : g x = g y
  · simp only [conditionalCoupling, h, ite_true, mul_comm]
  · simp only [conditionalCoupling, h, Ne.symm h, ite_false]

theorem conditionalCoupling_row {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) {x : ℝ} (hx : x ∈ ν.support) :
    ∑ y ∈ ν.support, conditionalCoupling ν g x y = ν.prob x := by
  classical
  have hp := ne_of_gt (cell_mass_pos ν g hx)
  unfold conditionalCoupling
  simp only [eq_comm (a := g x), ← Finset.sum_filter]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  change ν.prob x * FiniteEntropy.mass ν.support ν.prob g (g x) /
    FiniteEntropy.mass ν.support ν.prob g (g x) = _
  exact mul_div_cancel_right₀ _ hp

theorem conditionalCoupling_eq_zero_of_ne {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) {x y : ℝ} (h : g x ≠ g y) :
    conditionalCoupling ν g x y = 0 := by
  simp only [conditionalCoupling, h, ite_false]

theorem mem_bandIndex {u : ℝ} (hu : 0 < u) :
    (2 : ℝ) ^ (-bandIndex u) ≤ u ∧ u < (2 : ℝ) ^ (1 - bandIndex u) := by
  have hb : (1 : ℝ) < 2 := by norm_num
  constructor
  · rw [← Real.rpow_intCast]
    apply (Real.le_logb_iff_rpow_le hb hu).mp
    simpa only [bandIndex, neg_neg] using Int.floor_le (Real.logb 2 u)
  · rw [← Real.rpow_intCast]
    apply (Real.logb_lt_iff_lt_rpow hb hu).mp
    simpa only [bandIndex, sub_neg_eq_add, Int.cast_add, Int.cast_one, add_comm] using
      Int.lt_floor_add_one (Real.logb 2 u)

theorem coupling_distance_le {ν : Law} (π : ℝ → ℝ → ℝ) (R : ℝ)
    (hπ : ∀ x ∈ ν.support, ∀ y ∈ ν.support, 0 ≤ π x y)
    (hsym : ∀ x ∈ ν.support, ∀ y ∈ ν.support, π x y = π y x)
    (hrow : ∀ x ∈ ν.support, ∑ y ∈ ν.support, π x y ≤ ν.prob x)
    (hdiam : ∀ x ∈ ν.support, ∀ y ∈ ν.support, R < |y - x| → π x y = 0) :
    (∑ x ∈ ν.support, ∑ y ∈ ν.support, π x y * |y - x|) ≤
      ∑ ℓ ∈ ((ν.support ×ˢ ν.support).image (fun e => bandIndex |e.2 - e.1|)).filter
        (fun ℓ => (2 : ℝ) ^ (-ℓ) ≤ R), (2 : ℝ) ^ (1 - ℓ) * capacity ν ℓ := by
  classical
  let B := ((ν.support ×ˢ ν.support).image (fun e => bandIndex |e.2 - e.1|)).filter
    (fun ℓ => (2 : ℝ) ^ (-ℓ) ≤ R)
  let cost := fun (ℓ : ℤ) (x y : ℝ) =>
    if (2 : ℝ) ^ (-ℓ) ≤ |y - x| ∧ |y - x| < (2 : ℝ) ^ (1 - ℓ)
    then π x y else 0
  have hcost : ∀ ℓ x y, x ∈ ν.support → y ∈ ν.support → 0 ≤ cost ℓ x y := by
    intro ℓ x y hx hy
    dsimp [cost]
    split_ifs <;> first | exact hπ x hx y hy | exact le_rfl
  calc
    _ ≤ ∑ x ∈ ν.support, ∑ y ∈ ν.support,
        ∑ ℓ ∈ B, (2 : ℝ) ^ (1 - ℓ) * cost ℓ x y := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      by_cases hd : |y - x| = 0
      · rw [hd, mul_zero]
        exact Finset.sum_nonneg (fun ℓ _ => mul_nonneg (zpow_pos (by norm_num) _).le
          (hcost ℓ x y hx hy))
      by_cases hR : R < |y - x|
      · rw [hdiam x hx y hy hR, zero_mul]
        exact Finset.sum_nonneg (fun ℓ _ => mul_nonneg (zpow_pos (by norm_num) _).le
          (hcost ℓ x y hx hy))
      have hu : 0 < |y - x| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hd)
      have hb := mem_bandIndex hu
      have hm : bandIndex |y - x| ∈ B := Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨(x,y), Finset.mem_product.mpr ⟨hx,hy⟩, rfl⟩,
          hb.1.trans (le_of_not_gt hR)⟩
      apply le_trans _ (Finset.single_le_sum (fun ℓ _ =>
        mul_nonneg (zpow_pos (by norm_num) _).le (hcost ℓ x y hx hy)) hm)
      dsimp only [cost]
      rw [ite_eq_left hb]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb.2.le (hπ x hx y hy)
    _ = ∑ ℓ ∈ B, (2 : ℝ) ^ (1 - ℓ) *
        ∑ x ∈ ν.support, ∑ y ∈ ν.support, cost ℓ x y := by
      conv_lhs =>
        arg 2
        intro x
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ℓ _
      apply mul_le_mul_of_nonneg_left (coupling_band_le_capacity ℓ π hπ hsym hrow)
      exact (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le

theorem geometric_fine_scale_bound (s : Finset ℕ) {a : ℝ} (ha : 0 ≤ a)
    (hs : ∀ h ∈ s, a * (4 : ℝ)^h ≤ 2) :
    (∑ h ∈ s, a * (4 : ℝ)^h) ≤ 8 / 3 := by
  by_cases hn : s.Nonempty
  · let m := s.max' hn
    have hm : m ∈ s := Finset.max'_mem s hn
    have hsub : s ⊆ Finset.range (m + 1) := by
      intro h hh
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' s h hh))
    have hsum := Finset.sum_le_sum_of_subset_of_nonneg (f := fun h => a * (4 : ℝ)^h) hsub
      (fun h _ _ => mul_nonneg ha (pow_nonneg (by norm_num) h))
    have hg := geom_sum_mul (4 : ℝ) (m + 1)
    have he : (∑ h ∈ Finset.range (m+1), a * (4 : ℝ)^h) * 3 =
        4 * (a * (4 : ℝ)^m) - a := by
      rw [← Finset.mul_sum, mul_assoc]
      norm_num only [show (4 : ℝ) - 1 = 3 by norm_num] at hg
      rw [hg, pow_succ]
      ring
    linarith [hs m hm]
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty]
    norm_num

end FairPairs

end EntropyRateDimension

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.ProductLaw ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace ProductLaw

variable {ι : Type uι} {α : Type uα} [Fintype ι] [DecidableEq ι] [Fintype α]

omit [Fintype α] [DecidableEq ι] in
theorem weight_nonneg (p : ι → α → ℝ) (hp : ∀ i a, 0 ≤ p i a) (x : ι → α) :
    0 ≤ weight p x := Finset.prod_nonneg (fun i _ => hp i (x i))

theorem weight_sum (p : ι → α → ℝ) (hp : ∀ i, ∑ a, p i a = 1) :
    ∑ x, weight p x = 1 := by
  simpa only [weight, hp, Finset.prod_const_one] using (Fintype.prod_sum p).symm

theorem moment (p f : ι → α → ℝ) (s : Finset ι)
    (hp : ∀ i, ∑ a, p i a = 1) :
    (∑ x, weight p x * ∏ i ∈ s, f i (x i)) = ∏ i ∈ s, ∑ a, p i a * f i a := by
  classical
  have h := (Fintype.prod_sum (fun i a => p i a * if i ∈ s then f i a else 1)).symm
  have hleft : ∀ x : ι → α, (∏ i, p i (x i) * if i ∈ s then f i (x i) else 1) =
      weight p x * ∏ i ∈ s, f i (x i) := by
    intro x
    rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq]
    rfl
  have hright : ∀ i, (∑ a, p i a * if i ∈ s then f i a else 1) =
      if i ∈ s then ∑ a, p i a * f i a else 1 := by
    intro i
    split_ifs <;> simp_all only [mul_one]
  simpa only [hleft, hright, Finset.prod_ite_mem_eq] using h

theorem coordinate_event (p : ι → α → ℝ) (E : ι → α → Prop)
    [∀ i, DecidablePred (E i)] (hp : ∀ i, ∑ a, p i a = 1) (i : ι) :
    (∑ x, if E i (x i) then weight p x else 0) = ∑ a, if E i a then p i a else 0 := by
  classical
  simpa only [Finset.prod_singleton, mul_ite, mul_one, mul_zero] using
    moment p (fun j a => if E j a then 1 else 0) {i} hp

theorem two_coordinate_events (p : ι → α → ℝ) (E : ι → α → Prop)
    [∀ i, DecidablePred (E i)] (hp : ∀ i, ∑ a, p i a = 1)
    (i j : ι) (hij : i ≠ j) :
    (∑ x, if E i (x i) ∧ E j (x j) then weight p x else 0) =
      (∑ x, if E i (x i) then weight p x else 0) *
      (∑ x, if E j (x j) then weight p x else 0) := by
  classical
  rw [coordinate_event p E hp i, coordinate_event p E hp j]
  have h := moment p (fun l a => if E l a then 1 else 0) {i,j} hp
  simp only [Finset.prod_pair hij] at h
  convert h using 1
  · apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp_all
  · simp only [mul_ite, mul_one, mul_zero]

theorem entropy (p : ι → α → ℝ) (hp : ∀ i, ∑ a, p i a = 1) :
    FiniteEntropy.entropy Finset.univ (weight p) =
      ∑ i, FiniteEntropy.entropy Finset.univ (p i) := by
  classical
  have hm : ∀ i, (∑ x, weight p x * Real.log (p i (x i))) = ∑ a, p i a * Real.log (p i a) := by
    intro i
    simpa only [Finset.prod_singleton] using moment p (fun j a => Real.log (p j a)) {i} hp
  have hn : ∀ x : ι → α, Real.negMulLog (weight p x) =
      -(∑ i, weight p x * Real.log (p i (x i))) := by
    intro x
    by_cases hx : weight p x = 0
    · simp only [hx, Real.negMulLog_zero, zero_mul, Finset.sum_const_zero, neg_zero]
    · change -(weight p x) * Real.log (weight p x) = _
      have hfac : ∀ i ∈ (Finset.univ : Finset ι), p i (x i) ≠ 0 :=
        (Finset.prod_ne_zero_iff.mp hx)
      rw [weight, Real.log_prod hfac, Finset.mul_sum]
      simp only [neg_mul, Finset.sum_neg_distrib]
  simp only [FiniteEntropy.entropy, hn, Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  simp only [hm, Real.negMulLog, neg_mul, Finset.sum_neg_distrib]

variable {β : Type uβ} [DecidableEq β]

theorem mass_cells (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β) :
    FiniteEntropy.mass Finset.univ (weight p) (fun x i => g i (x i)) c =
      ∏ i, cellMass p g c i := by
  classical
  have hh := (Fintype.prod_sum (fun i a => if g i a = c i then p i a else 0)).symm
  simpa only [Fintype.prod_ite_zero, ← funext_iff, FiniteEntropy.mass,
    Finset.sum_filter, weight, cellMass] using hh

theorem weight_conditional (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β) (x : ι → α) :
    weight (conditional p g c) x =
      if (fun i => g i (x i)) = c then weight p x /
        FiniteEntropy.mass Finset.univ (weight p) (fun x i => g i (x i)) c else 0 := by
  classical
  rw [mass_cells]
  simp only [weight, conditional, Finset.prod_div_distrib, Fintype.prod_ite_zero, ← funext_iff]
  split_ifs <;> simp_all

theorem conditional_sum (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β)
    (hc : FiniteEntropy.mass Finset.univ (weight p) (fun x i => g i (x i)) c ≠ 0) (i : ι) :
    ∑ a, conditional p g c i a = 1 := by
  rw [mass_cells] at hc
  have hi : cellMass p g c i ≠ 0 := (Finset.prod_ne_zero_iff.mp hc) i (Finset.mem_univ i)
  simp only [conditional, ← Finset.sum_div]
  exact div_self hi

omit [Fintype ι] [DecidableEq ι] in
theorem conditional_nonneg (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β)
    (hp : ∀ i a, 0 ≤ p i a) (i : ι) (a : α) : 0 ≤ conditional p g c i a := by
  have hn : ∀ j b, 0 ≤ (if g j b = c j then p j b else 0) := by
    intro j b
    split_ifs <;> first | exact hp j b | exact le_rfl
  exact div_nonneg (hn i a) (Finset.sum_nonneg (fun b _ => hn i b))

theorem conditional_event (p : ι → α → ℝ) (g : ι → α → β) (c : ι → β)
    (E : (ι → α) → Prop) [DecidablePred E] :
    (∑ x ∈ Finset.univ.filter (fun x => (fun i => g i (x i)) = c),
      if E x then weight p x / FiniteEntropy.mass Finset.univ (weight p) (fun x i => g i (x i)) c else 0) =
    ∑ x, if E x then weight (conditional p g c) x else 0 := by
  classical
  simp only [Finset.sum_filter, weight_conditional]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl

theorem observable_entropy [Nonempty α] [Nonempty β]
    (p : α → ℝ) (g : α → β) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    FiniteEntropy.observableEntropy Finset.univ (weight (fun _ : ι => p)) (fun x i => g (x i)) =
      Fintype.card ι * FiniteEntropy.observableEntropy Finset.univ p g := by
  classical
  let B : Finset β := Finset.univ.image g
  let g' : α → B := fun a => ⟨g a, Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
  have : Nonempty B := ⟨g' (Classical.choice inferInstance)⟩
  have hg : FiniteEntropy.observableEntropy Finset.univ p g =
      FiniteEntropy.observableEntropy Finset.univ p g' := by
    apply FiniteEntropy.observableEntropy_eq_of_fibers _ _ _ _ (fun a _ => hp a)
    intro a _ b _
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hG : FiniteEntropy.observableEntropy Finset.univ (weight (fun _ : ι => p)) (fun x i => g (x i)) =
      FiniteEntropy.observableEntropy Finset.univ (weight (fun _ : ι => p)) (fun x i => g' (x i)) := by
    apply FiniteEntropy.observableEntropy_eq_of_fibers _ _ _ _
      (fun x _ => weight_nonneg _ (fun _ a => hp a) x)
    intro x _ y _
    constructor
    · intro h
      funext i
      exact Subtype.ext (congrFun h i)
    · intro h
      funext i
      exact congrArg Subtype.val (congrFun h i)
  rw [hg, hG, FiniteEntropy.observableEntropy_on_superset Finset.univ Finset.univ _ _
    (fun _ _ => Finset.mem_univ _)]
  have hm : FiniteEntropy.mass Finset.univ (weight (fun _ : ι => p)) (fun x i => g' (x i)) =
      weight (fun _ : ι => FiniteEntropy.mass Finset.univ p g') := by
    funext c
    rw [mass_cells]
    simp only [weight, cellMass, FiniteEntropy.mass, Finset.sum_filter]
  have hpB : ∑ b : B, FiniteEntropy.mass Finset.univ p g' b = 1 := by
    rw [← hp1, ← FiniteEntropy.mass_sum Finset.univ p g']
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro b _ hb
    exact FiniteEntropy.mass_eq_zero_of_not_mem _ _ _ hb
  rw [hm, entropy _ (fun _ => hpB)]
  rw [FiniteEntropy.observableEntropy_on_superset Finset.univ Finset.univ p g'
    (fun _ _ => Finset.mem_univ _)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end ProductLaw

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.GridCoupling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace RandomGrid

attribute [local instance] unitCircleProbability
theorem exists_shift_cost_le {α : Type uα} (s : Finset α) (w : α → ℝ)
    (c : α → AddCircle (1 : ℝ)) (r : α → ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hr : ∀ a ∈ s, 0 ≤ r a) :
    ∃ u : AddCircle (1 : ℝ),
      (∑ a ∈ s, w a * hit (c a) (r a) u) ≤ ∑ a ∈ s, w a * (2 * r a) := by
  have hi : ∀ a ∈ s, Integrable (fun u => w a * hit (c a) (r a) u) :=
    fun a _ => (hit_integrable (c a) (r a)).const_mul (w a)
  obtain ⟨u, hu⟩ := exists_le_integral (integrable_finsetSum s hi)
  refine ⟨u, hu.trans ?_⟩
  rw [integral_finsetSum s hi]
  apply Finset.sum_le_sum
  intro a ha
  rw [integral_const_mul, integral_hit (c a) (hr a ha)]
  exact mul_le_mul_of_nonneg_left (min_le_right _ _) (hw a ha)

theorem shift_zero : shift 0 = 0 := by
  have hh := AddCircle.equivIco_coe_of_mem (p := (1 : ℝ)) (a := (0 : ℝ))
    (y := (0 : ℝ)) (by norm_num : (0 : ℝ) ∈ Set.Ico 0 (0+1))
  simpa only [shift, AddCircle.coe_zero] using hh

theorem cell_eq_distance_lt {δ x y : ℝ} (hδ : 0 < δ) (u : AddCircle (1 : ℝ))
    (h : cell δ u x = cell δ u y) : |x-y| < δ := by
  have hx := Int.floor_le (x/δ+shift u)
  have hx' := Int.lt_floor_add_one (x/δ+shift u)
  have hy := Int.floor_le (y/δ+shift u)
  have hy' := Int.lt_floor_add_one (y/δ+shift u)
  change ⌊x/δ+shift u⌋ = ⌊y/δ+shift u⌋ at h
  rw [h] at hx hx'
  have hxy : (x-y)/δ < 1 := by rw [sub_div]; linarith
  have hyx : (y-x)/δ < 1 := by rw [sub_div]; linarith
  have hhxy := (div_lt_iff₀ hδ).mp hxy
  have hhyx := (div_lt_iff₀ hδ).mp hyx
  rw [abs_lt]
  constructor <;> linarith

theorem cell_change_margin {δ x m : ℝ} (hδ : 0 < δ) (u : AddCircle (1 : ℝ))
    (h : cell δ u x ≠ cell δ u m) :
    δ * dist u (-(m / δ : ℝ) : AddCircle (1 : ℝ)) ≤ |x - m| := by
  have hn := circle_norm_le_of_floor_ne (Ne.symm h)
  have he : ((m / δ + shift u : ℝ) : AddCircle (1 : ℝ)) =
      u + (m / δ : ℝ) := by
    rw [AddCircle.coe_add]
    simp only [shift, AddCircle.coe_equivIco, add_comm]
  change ‖((m / δ + shift u : ℝ) : AddCircle (1 : ℝ))‖ ≤ _ at hn
  rw [he] at hn
  have habs : |x / δ + shift u - (m / δ + shift u)| = |x - m| / δ := by
    rw [show x / δ + shift u - (m / δ + shift u) = (x - m) / δ by ring,
      abs_div, abs_of_pos hδ]
  rw [habs] at hn
  rw [dist_eq_norm, sub_neg_eq_add]
  simpa only [mul_comm] using (le_div_iff₀ hδ).mp hn

theorem cell_mem_interval {δ x m : ℝ} (hδ : 0 < δ) (u : AddCircle (1 : ℝ))
    (hx : |x-m| ≤ 4*δ) :
    cell δ u x ∈ Finset.Icc (cell δ u m - 5) (cell δ u m + 5) := by
  apply Finset.mem_Icc.mpr
  have hxm := (abs_le.mp hx)
  have hdiv : |x/δ + shift u - (m/δ + shift u)| ≤ 4 := by
    rw [show x/δ + shift u - (m/δ + shift u) = (x-m)/δ by ring,
      abs_div, abs_of_pos hδ]
    exact (div_le_iff₀ hδ).mpr hx
  have hx1 := Int.floor_le (x/δ+shift u)
  have hx2 := Int.lt_floor_add_one (x/δ+shift u)
  have hm1 := Int.floor_le (m/δ+shift u)
  have hm2 := Int.lt_floor_add_one (m/δ+shift u)
  obtain ⟨hlo,hhi⟩ := abs_le.mp hdiv
  constructor <;> unfold cell
  · have : (⌊m/δ+shift u⌋ : ℝ) - 5 ≤ (⌊x/δ+shift u⌋ : ℝ) := by linarith
    exact_mod_cast this
  · have : (⌊x/δ+shift u⌋ : ℝ) ≤ (⌊m/δ+shift u⌋ : ℝ) + 5 := by linarith
    exact_mod_cast this

theorem grid_alphabet_bound {α : Type uα} (s : Finset α) (k : ℕ)
    (v : α → Fin k → ℝ) (m : Fin k → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (u : AddCircle (1 : ℝ)) (hs : s.Nonempty)
    (hv : ∀ x ∈ s, ∀ i, |v x i-m i| ≤ 4*δ) :
    Real.log (s.image (fun x i => cell δ u (v x i))).card ≤
      4*k*Real.log 2 := by
  classical
  let T := Fintype.piFinset (fun i : Fin k => Finset.Icc (cell δ u (m i)-5) (cell δ u (m i)+5))
  have hcard : (s.image (fun x i => cell δ u (v x i))).card ≤ 11^k := by
    calc
      _ ≤ T.card := Finset.card_le_card (by
        intro f hf
        obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hf
        apply Fintype.mem_piFinset.mpr
        intro i
        exact cell_mem_interval hδ u (hv x hx i))
      _ = 11^k := by
        simp only [T, Fintype.card_piFinset, Int.card_Icc]
        simp [show ∀ n : ℤ, n + 5 + 1 - (n-5) = 11 by intro n; ring]
  have hcpos : (0 : ℝ) < (s.image (fun x i => cell δ u (v x i))).card := by
    exact_mod_cast Finset.card_pos.mpr (hs.image _)
  have hb : Real.log (s.image (fun x i => cell δ u (v x i))).card ≤ Real.log ((16 : ℝ)^k) := by
    apply Real.log_le_log hcpos
    have he : (s.image (fun x i => cell δ u (v x i))).card ≤ 16^k :=
      hcard.trans (Nat.pow_le_pow_left (by norm_num) k)
    exact_mod_cast he
  calc
    _ ≤ _ := hb
    _ = 4*k*Real.log 2 := by
      rw [Real.log_pow, show (16 : ℝ) = 2^4 by norm_num, Real.log_pow]
      ring

theorem refinement_entropy_bound {α : Type uα} (s : Finset α) (p : α → ℝ)
    (k : ℕ) (hk : 1 ≤ k) (v : α → Fin k → ℝ) (m : Fin k → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (u : AddCircle (1 : ℝ)) (a : ℝ)
    (hmargin : ∀ i, a ≤ δ * dist u (-(m i/δ : ℝ) : AddCircle (1 : ℝ)))
    (hp : ∀ x ∈ s, 0 ≤ p x) (hp1 : ∑ x ∈ s, p x = 1)
    (hv : ∀ x ∈ s, ∀ i, |v x i-m i| ≤ 4*δ)
    (hind : ∀ i j : Fin k, i ≠ j →
      (∑ x ∈ s, if a/(4*k) ≤ |v x i-m i| ∧ a/(4*k) ≤ |v x j-m j| then p x else 0) =
      (∑ x ∈ s, if a/(4*k) ≤ |v x i-m i| then p x else 0) *
      (∑ x ∈ s, if a/(4*k) ≤ |v x j-m j| then p x else 0)) :
    FiniteEntropy.conditionalEntropy s p (fun x i => cell δ u (v x i)) (fun x => ∑ i, v x i) ≤
      11*k*(∑ i, ∑ x ∈ s, if a/(4*k) ≤ |v x i-m i| then p x else 0)*Real.log 2 := by
  classical
  let Ex := fun (i : Fin k) x => a/(4*k) ≤ |v x i-m i|
  let E : α → Bool := fun x => decide (∃ i j, i ≠ j ∧ Ex i x ∧ Ex j x)
  let B : ℝ → Prop := fun y => a/2 ≤ |y-∑ i, m i|
  let Y := fun x => ∑ i, v x i
  let C := fun x i => cell δ u (v x i)
  let t := ∑ i, ∑ x ∈ s, if Ex i x then p x else 0
  let q := ∑ x ∈ s, if ∃ i j, i ≠ j ∧ Ex i x ∧ Ex j x then p x else 0
  let b := ∑ x ∈ s, if B (Y x) then p x else 0
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have ht : 0 ≤ t := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro x hx
    split_ifs <;> first | exact hp x hx | exact le_rfl
  have hq : 0 ≤ q := by
    apply Finset.sum_nonneg
    intro x hx
    split_ifs <;> first | exact hp x hx | exact le_rfl
  have hb : 0 ≤ b := by
    apply Finset.sum_nonneg
    intro x hx
    split_ifs <;> first | exact hp x hx | exact le_rfl
  have hq1 : q ≤ 1 := by
    rw [← hp1]
    apply Finset.sum_le_sum
    intro x hx
    split_ifs <;> first | exact le_rfl | exact hp x hx
  have htq : q ≤ t^2 ∧ q ≤ t := by
    convert FiniteEntropy.two_exceptions_bound s p Ex hp hind using 2 <;>
      apply Finset.sum_congr rfl <;> intro x hx <;> split_ifs <;> rfl
  have hbt : b ≤ t := by
    apply le_trans _ (FiniteEntropy.event_union_bound s p Ex hp)
    apply Finset.sum_le_sum
    intro x hx
    by_cases hbx : B (Y x)
    · rw [ite_eq_left hbx]
      have he : ∃ i, Ex i x := by
        by_contra hn
        have hi : ∀ i, |v x i-m i| < a/(4*k) := by
          intro i
          exact lt_of_not_ge (fun h => hn ⟨i,h⟩)
        have ha : 0 < a := by
          have h := (abs_nonneg (v x ⟨0,by omega⟩-m ⟨0,by omega⟩)).trans_lt (hi ⟨0,by omega⟩)
          exact (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 4*k)).mp h
        have hh : |∑ i, (v x i-m i)| ≤ a/4 := by
          apply (Finset.abs_sum_le_sum_abs _ _).trans
          calc
            (∑ i, |v x i-m i|) ≤ ∑ _i : Fin k, a/(4*k) :=
              Finset.sum_le_sum (fun i _ => (hi i).le)
            _ = a/4 := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              field_simp
        dsimp only [B,Y] at hbx
        rw [Finset.sum_sub_distrib] at hh
        linarith
      rw [ite_eq_left he]
    · rw [ite_eq_right hbx]
      split_ifs <;> first | exact hp x hx | exact le_rfl
  have hflag := FiniteEntropy.conditionalEntropy_rare_flag s p C Y E B
    (fun i => cell δ u (m i)) hp hp1 ?_
  · have heq : FiniteEntropy.mass s p E true = q := by
      simp only [FiniteEntropy.mass, Finset.sum_filter, E, decide_eq_true_eq, q]
    have hbeq : (∑ x ∈ s.filter (fun x => B (Y x)), p x) = b := by
      simp only [Finset.sum_filter, b]
    rw [heq, hbeq] at hflag
    have hs : s.Nonempty := by
      by_contra hn
      rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty] at hp1
      norm_num at hp1
    have hcard := grid_alphabet_bound s k v m hδ u hs hv
    have hm := mul_le_mul_of_nonneg_left hcard (add_nonneg hq hb)
    have hsqrt : Real.sqrt q ≤ t := (Real.sqrt_le_left ht).mpr htq.1
    have hbin : Real.binEntropy q ≤ 3*t*Real.log 2 := by
      apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
      exact (FiniteEntropy.binEntropy_bits_le_three_sqrt hq hq1).trans (by linarith)
    have hqb : q+b ≤ 2*t := by linarith [htq.2]
    have hqb' := mul_le_mul_of_nonneg_right hqb
      (by positivity : 0 ≤ 4*(k : ℝ)*Real.log 2)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hlast := mul_nonneg (sub_nonneg.mpr hk1) (mul_nonneg ht (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le)
    change FiniteEntropy.conditionalEntropy s p C Y ≤ 11*k*t*Real.log 2
    nlinarith
  · intro x hx hEx hBx
    have hm : |∑ i, (v x i-m i)| < a/2 := by
      simpa only [Finset.sum_sub_distrib] using lt_of_not_ge hBx
    have ha : 0 < a := by linarith [abs_nonneg (∑ i, (v x i-m i))]
    have hn : ¬∃ i j, i ≠ j ∧ Ex i x ∧ Ex j x := by
      simpa only [E, decide_eq_false_iff_not] using hEx
    funext i
    by_contra hne
    have hfar := hmargin i |>.trans (cell_change_margin hδ u hne)
    have hnear := FiniteEntropy.no_large_coordinate (fun i => v x i-m i) ha
      (by simpa only [Fintype.card_fin] using hn) hm i
    linarith

theorem hit_nonneg (c : AddCircle (1 : ℝ)) (r : ℝ) (u : AddCircle (1 : ℝ)) :
    0 ≤ hit c r u := by unfold hit; split_ifs <;> norm_num

theorem refinement_entropy_hit_bound {α : Type uα} (s : Finset α) (p : α → ℝ)
    (k : ℕ) (hk : 1 ≤ k) (v : α → Fin k → ℝ) (m : Fin k → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (u : AddCircle (1 : ℝ))
    (hp : ∀ x ∈ s, 0 ≤ p x) (hp1 : ∑ x ∈ s, p x = 1)
    (hv : ∀ x ∈ s, ∀ i, |v x i-m i| ≤ 4*δ)
    (hind : ∀ a : ℝ, ∀ i j : Fin k, i ≠ j →
      (∑ x ∈ s, if a/(4*k) ≤ |v x i-m i| ∧ a/(4*k) ≤ |v x j-m j| then p x else 0) =
      (∑ x ∈ s, if a/(4*k) ≤ |v x i-m i| then p x else 0) *
      (∑ x ∈ s, if a/(4*k) ≤ |v x j-m j| then p x else 0)) :
    FiniteEntropy.conditionalEntropy s p (fun x i => cell δ u (v x i)) (fun x => ∑ i, v x i) ≤
      11*k*(∑ x ∈ s, p x * ∑ i, ∑ j,
        hit (-(m j/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v x i-m i|/δ) u)*Real.log 2 := by
  classical
  have hkR : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  let d : Fin k → ℝ := fun i => dist u (-(m i/δ : ℝ) : AddCircle (1 : ℝ))
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0,by omega⟩,Finset.mem_univ _⟩
  obtain ⟨j₀, _, hj₀⟩ := Finset.exists_min_image Finset.univ d hne
  let a := δ*d j₀
  have ha : ∀ i, a ≤ δ*d i := fun i => mul_le_mul_of_nonneg_left (hj₀ i (Finset.mem_univ i)) hδ.le
  have h := refinement_entropy_bound s p k hk v m δ hδ u a ha hp hp1 hv (hind a)
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (11 : ℝ)*k)
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases he : a/(4*k) ≤ |v x i-m i|
  · rw [ite_eq_left he]
    have hdist : d j₀ ≤ 4*k*|v x i-m i|/δ := by
      apply (le_div_iff₀ hδ).mpr
      have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 4*k)).mp he
      dsimp only [a] at hh
      nlinarith
    have hone : hit (-(m j₀/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v x i-m i|/δ) u = 1 :=
      ite_eq_left hdist
    have hs : 1 ≤ ∑ j, hit (-(m j/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v x i-m i|/δ) u := by
      have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin k))) (f := fun j =>
        hit (-(m j/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v x i-m i|/δ) u)
        (fun j _ => hit_nonneg _ _ _) (Finset.mem_univ j₀)
      simpa only [hone] using hh
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hs (hp x hx)
  · rw [ite_eq_right he]
    exact mul_nonneg (hp x hx) (Finset.sum_nonneg (fun j _ => hit_nonneg _ _ _))

theorem exists_shift_variation_bound {α : Type uα} (s : Finset α) (p : α → ℝ)
    (k : ℕ) (v m : α → Fin k → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hp : ∀ x ∈ s, 0 ≤ p x) :
    ∃ u : AddCircle (1 : ℝ),
      (∑ x ∈ s, p x * ∑ i, ∑ j,
        hit (-(m x j/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v x i-m x i|/δ) u) ≤
      (8*k^2/δ)*(∑ x ∈ s, p x * ∑ i, |v x i-m x i|) := by
  classical
  let T : Finset (α × Fin k × Fin k) := s ×ˢ (Finset.univ ×ˢ Finset.univ)
  obtain ⟨u,hu⟩ := exists_shift_cost_le T (fun z => p z.1)
    (fun z => (-(m z.1 z.2.2/δ : ℝ) : AddCircle (1 : ℝ)))
    (fun z => 4*k*|v z.1 z.2.1-m z.1 z.2.1|/δ)
    (fun z hz => hp z.1 (Finset.mem_product.mp hz).1) (fun z _ => by positivity)
  refine ⟨u, ?_⟩
  have he : (∑ z ∈ T, p z.1 * hit (-(m z.1 z.2.2/δ : ℝ) : AddCircle (1 : ℝ))
      (4*k*|v z.1 z.2.1-m z.1 z.2.1|/δ) u) =
      ∑ x ∈ s, p x * ∑ i, ∑ j,
        hit (-(m x j/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v x i-m x i|/δ) u := by
    simp only [T, Finset.sum_product, Finset.mul_sum]
  rw [he] at hu
  apply hu.trans_eq
  simp only [T, Finset.sum_product, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end RandomGrid

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteRefinement ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uα uβ uγ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteRefinement

open FiniteEntropy

variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem distance_mean_le (p : α → ℝ) (v : α → ℝ) (z R : ℝ)
    (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (hR : ∀ a, p a ≠ 0 → |z-v a| ≤ R) : |z - ∑ a, p a * v a| ≤ R := by
  have he : z - ∑ a, p a * v a = ∑ a, p a * (z-v a) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    (∑ a, |p a * (z-v a)|) ≤ ∑ a, p a * R := by
      apply Finset.sum_le_sum
      intro a _
      rw [abs_mul, abs_of_nonneg (hp a)]
      by_cases ha : p a = 0
      · simp only [ha, zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left (hR a ha) (hp a)
    _ = R := by rw [← Finset.sum_mul, hp1, one_mul]

omit [Fintype α] in
theorem mass_pos {γ : Type uγ} [DecidableEq γ] (s : Finset α) (p : α → ℝ)
    (g : α → γ) (hp : ∀ a ∈ s, 0 < p a) {b : γ} (hb : b ∈ s.image g) :
    0 < mass s p g b := by
  classical
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  exact (hp a ha).trans_le (Finset.single_le_sum
    (fun x hx => (hp x (Finset.mem_filter.mp hx).1).le) (by simp [ha]))

theorem cellMass_eq (p : α → ℝ) (g : α → β) {k : ℕ} (c : Fin k → β) (i : Fin k) :
    ProductLaw.cellMass (fun _ : Fin k => p) (fun _ => g) c i = mass Finset.univ p g (c i) := by
  simp only [ProductLaw.cellMass, mass, Finset.sum_filter]

theorem conditional_mean_eq (p : α → ℝ) (v : α → ℝ) (g : α → β)
    {k : ℕ} (c : Fin k → β) (i : Fin k) :
    (∑ a, ProductLaw.conditional (fun _ : Fin k => p) (fun _ => g) c i a * v a) =
      cellMean p v g (c i) := by
  simp only [cellMean, ProductLaw.conditional, cellMass_eq]

theorem conditional_mean_distance_le (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp : ∀ a, 0 ≤ p a) {k : ℕ} (c : Fin k → β) (i : Fin k)
    (hc : mass Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => g (x i)) c ≠ 0) (x : α) (hx : g x = c i) (R : ℝ)
    (hd : ∀ a b, g a = g b → |v a-v b| ≤ R) :
    |v x-cellMean p v g (c i)| ≤ R := by
  rw [← conditional_mean_eq p v g c i]
  apply distance_mean_le _ _ _ R
    (ProductLaw.conditional_nonneg _ _ _ (fun _ a => hp a) i)
    (ProductLaw.conditional_sum _ _ _ hc i)
  intro a ha
  have hga : g a = c i := by
    by_contra hn
    exact ha (by simp only [ProductLaw.conditional, ite_eq_right hn, zero_div])
  exact hd x a (hx.trans hga.symm)

theorem fiber_entropy_hit_bound (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp : ∀ a, 0 < p a) (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ)
    (hd : ∀ a b, g a = g b → |v a-v b| ≤ 4*δ) (u : AddCircle (1 : ℝ))
    (c : Fin k → β)
    (hc : c ∈ (Finset.univ : Finset (Fin k → α)).image (fun x i => g (x i))) :
    conditionalEntropy (Finset.univ.filter (fun x : Fin k → α => (fun i => g (x i)) = c))
      (fun x => ProductLaw.weight (fun _ : Fin k => p) x /
        mass Finset.univ (ProductLaw.weight (fun _ : Fin k => p)) (fun x i => g (x i)) c)
      (fun x i => RandomGrid.cell δ u (v (x i))) (fun x => ∑ i, v (x i)) ≤
    11*k*(∑ x ∈ Finset.univ.filter (fun x : Fin k → α => (fun i => g (x i)) = c),
      (ProductLaw.weight (fun _ : Fin k => p) x /
        mass Finset.univ (ProductLaw.weight (fun _ : Fin k => p)) (fun x i => g (x i)) c) *
      ∑ i, ∑ j, RandomGrid.hit (-(cellMean p v g (c j)/δ : ℝ) : AddCircle (1 : ℝ))
        (4*k*|v (x i)-cellMean p v g (c i)|/δ) u)*Real.log 2 := by
  classical
  let w : (Fin k → α) → ℝ := ProductLaw.weight (fun _ : Fin k => p)
  let G : (Fin k → α) → (Fin k → β) := fun x i => g (x i)
  have hw : ∀ x : Fin k → α, 0 < w x := fun x => Finset.prod_pos (fun i _ => hp (x i))
  have hP : 0 < mass Finset.univ w G c := mass_pos Finset.univ w G (fun x _ => hw x) hc
  have hnc : mass Finset.univ w G c ≠ 0 := ne_of_gt hP
  let s₀ : Finset (Fin k → α) := Finset.univ.filter (fun x => G x = c)
  let p₀ : (Fin k → α) → ℝ := fun x => w x / mass Finset.univ w G c
  let v₀ : (Fin k → α) → Fin k → ℝ := fun x i => v (x i)
  let m₀ : Fin k → ℝ := fun i => cellMean p v g (c i)
  have hp₀ : ∀ x ∈ s₀, 0 ≤ p₀ x := fun x _ => div_nonneg (hw x).le hP.le
  have hp₀1 : ∑ x ∈ s₀, p₀ x = 1 := by
    rw [show (∑ x ∈ s₀, p₀ x) = mass Finset.univ w G c / mass Finset.univ w G c by
      exact (Finset.sum_div _ _ _).symm]
    exact div_self hnc
  have hv₀ : ∀ x ∈ s₀, ∀ i, |v₀ x i-m₀ i| ≤ 4*δ := by
    intro x hx i
    have he : G x = c := (Finset.mem_filter.mp hx).2
    exact conditional_mean_distance_le p v g (fun a => (hp a).le) c i hnc (x i)
      (congrFun he i) (4*δ) hd
  have hind : ∀ a : ℝ, ∀ i j : Fin k, i ≠ j →
      (∑ x ∈ s₀, if a/(4*k) ≤ |v₀ x i-m₀ i| ∧ a/(4*k) ≤ |v₀ x j-m₀ j| then p₀ x else 0) =
      (∑ x ∈ s₀, if a/(4*k) ≤ |v₀ x i-m₀ i| then p₀ x else 0) *
      (∑ x ∈ s₀, if a/(4*k) ≤ |v₀ x j-m₀ j| then p₀ x else 0) := by
    intro a i j hij
    let E := fun (i : Fin k) (x : α) => a/(4*k) ≤ |v x-cellMean p v g (c i)|
    have heen := ProductLaw.two_coordinate_events
      (ProductLaw.conditional (fun _ : Fin k => p) (fun _ => g) c) E
      (ProductLaw.conditional_sum _ _ _ hnc) i j hij
    rw [← ProductLaw.conditional_event (fun _ : Fin k => p) (fun _ => g) c (fun x => E i (x i) ∧ E j (x j)),
      ← ProductLaw.conditional_event (fun _ : Fin k => p) (fun _ => g) c (fun x => E i (x i)),
      ← ProductLaw.conditional_event (fun _ : Fin k => p) (fun _ => g) c (fun x => E j (x j))] at heen
    exact heen
  exact RandomGrid.refinement_entropy_hit_bound s₀ p₀ k hk v₀ m₀ δ hδ u hp₀ hp₀1 hv₀ hind

theorem entropy_step_hit_bound (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp : ∀ a, 0 < p a)
    (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ)
    (hd : ∀ a b, g a = g b → |v a-v b| ≤ 4*δ)
    (u : AddCircle (1 : ℝ)) :
    conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => RandomGrid.cell δ u (v (x i)))
      (fun x => (∑ i, v (x i), fun i => g (x i))) ≤
    11*k*(∑ x : Fin k → α, ProductLaw.weight (fun _ : Fin k => p) x * ∑ i, ∑ j,
      RandomGrid.hit (-(cellMean p v g (g (x j))/δ : ℝ) : AddCircle (1 : ℝ))
        (4*k*|v (x i)-cellMean p v g (g (x i))|/δ) u)*Real.log 2 := by
  classical
  let w := ProductLaw.weight (fun _ : Fin k => p)
  let G := fun (x : Fin k → α) i => g (x i)
  let Y := fun (x : Fin k → α) => ∑ i, v (x i)
  let C := fun (x : Fin k → α) i => RandomGrid.cell δ u (v (x i))
  let P := mass Finset.univ w G
  let M := fun (c : Fin k → β) i => cellMean p v g (c i)
  let cost := fun (c : Fin k → β) (x : Fin k → α) => ∑ i, ∑ j,
    RandomGrid.hit (-(M c j/δ : ℝ) : AddCircle (1 : ℝ)) (4*k*|v (x i)-M c i|/δ) u
  have hw : ∀ x : Fin k → α, 0 < w x := fun x => Finset.prod_pos (fun i _ => hp (x i))
  have hP : ∀ c ∈ Finset.univ.image G, 0 < P c :=
    fun c hc => mass_pos Finset.univ w G (fun x _ => hw x) hc
  have hcstep : ∀ c ∈ Finset.univ.image G,
      conditionalEntropy (Finset.univ.filter (fun x => G x = c)) (fun x => w x/P c) C Y ≤
        11*k*(∑ x ∈ Finset.univ.filter (fun x => G x = c), (w x/P c)*cost c x)*Real.log 2 :=
    fun c hc => fiber_entropy_hit_bound p v g hp k hk δ hδ hd u c hc
  rw [conditionalEntropy_disintegrate Finset.univ w C G Y (fun x _ => (hw x).le)]
  calc
    _ ≤ ∑ c ∈ Finset.univ.image G, P c *
        (11*k*(∑ x ∈ Finset.univ.filter (fun x => G x = c), (w x/P c)*cost c x)*Real.log 2) := by
      apply Finset.sum_le_sum
      intro c hc
      exact mul_le_mul_of_nonneg_left (hcstep c hc) (hP c hc).le
    _ = 11*k*(∑ c ∈ Finset.univ.image G,
        ∑ x ∈ Finset.univ.filter (fun x => G x = c), w x*cost (G x) x)*Real.log 2 := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
      field_simp [ne_of_gt (hP c hc)]
    _ = _ := by
      rw [Finset.sum_fiberwise_of_maps_to (fun x (_ : x ∈ Finset.univ) => Finset.mem_image_of_mem G (Finset.mem_univ x))]

theorem mean_deviation_le_coupling (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp : ∀ a, 0 < p a) :
    (∑ a, p a * |v a-cellMean p v g (g a)|) ≤
      ∑ a, ∑ b, (if g a = g b then p a*p b/mass Finset.univ p g (g a) else 0) *
        |v a-v b| := by
  classical
  apply Finset.sum_le_sum
  intro a _
  have hP : 0 < mass Finset.univ p g (g a) :=
    mass_pos Finset.univ p g (fun x _ => hp x) (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
  let q : α → ℝ := fun b => (if g b = g a then p b else 0)/mass Finset.univ p g (g a)
  have hq : ∀ b, 0 ≤ q b := by
    intro b
    exact div_nonneg (by split_ifs <;> first | exact (hp b).le | exact le_rfl) hP.le
  have hq1 : ∑ b, q b = 1 := by
    dsimp only [q]
    rw [← Finset.sum_div]
    simpa only [mass, Finset.sum_filter] using div_self (ne_of_gt hP)
  have he : v a-cellMean p v g (g a) = ∑ b, q b*(v a-v b) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hq1, one_mul]
    rfl
  rw [he]
  calc
    p a * |∑ b, q b*(v a-v b)| ≤ p a * ∑ b, |q b*(v a-v b)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (hp a).le
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [abs_mul, abs_of_nonneg (hq b)]
      dsimp only [q]
      by_cases hg : g a = g b
      · simp only [hg, ite_true]
        ring
      · simp only [hg, Ne.symm hg, ite_false, zero_div, mul_zero, zero_mul]

theorem product_mean_deviation (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp1 : ∑ a, p a = 1) (k : ℕ) :
    (∑ x : Fin k → α, ProductLaw.weight (fun _ : Fin k => p) x *
      ∑ i, |v (x i)-cellMean p v g (g (x i))|) =
      k * ∑ a, p a*|v a-cellMean p v g (g a)| := by
  classical
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ i : Fin k, (∑ x : Fin k → α, ProductLaw.weight (fun _ : Fin k => p) x *
      |v (x i)-cellMean p v g (g (x i))|) = ∑ a, p a*|v a-cellMean p v g (g a)| := by
    intro i
    simpa only [Finset.prod_singleton] using ProductLaw.moment (fun _ : Fin k => p)
      (fun _ a => |v a-cellMean p v g (g a)|) {i} (fun _ => hp1)
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]

theorem exists_entropy_step (p : α → ℝ) (v : α → ℝ) (g : α → β)
    (hp : ∀ a, 0 < p a) (hp1 : ∑ a, p a = 1)
    (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ : 0 < δ)
    (hd : ∀ a b, g a = g b → |v a-v b| ≤ 4*δ) :
    ∃ u : AddCircle (1 : ℝ),
    conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => RandomGrid.cell δ u (v (x i)))
      (fun x => (∑ i, v (x i), fun i => g (x i))) ≤
    (88*k^4/δ)*(∑ a, p a*|v a-cellMean p v g (g a)|)*Real.log 2 := by
  classical
  obtain ⟨u,hu⟩ := RandomGrid.exists_shift_variation_bound Finset.univ
    (ProductLaw.weight (fun _ : Fin k => p)) k (fun x i => v (x i))
    (fun x i => cellMean p v g (g (x i))) δ hδ
    (fun x _ => ProductLaw.weight_nonneg _ (fun _ a => (hp a).le) x)
  refine ⟨u, (entropy_step_hit_bound p v g hp k hk δ hδ hd u).trans ?_⟩
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ (11 : ℝ)*k))
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  rw [product_mean_deviation p v g hp1 k] at hm
  convert hm using 1; ring

theorem refinement_increment (p : α → ℝ) (v : α → ℝ) (g : α → List ℤ)
    (hp : ∀ a, 0 ≤ p a) (k : ℕ) (δ : ℝ) (u : AddCircle (1 : ℝ)) :
    conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => RandomGrid.cell δ u (v (x i)) :: g (x i)) (fun x => ∑ i, v (x i)) =
    conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => g (x i)) (fun x => ∑ i, v (x i)) +
    conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => p))
      (fun x i => RandomGrid.cell δ u (v (x i)))
      (fun x => (∑ i, v (x i), fun i => g (x i))) := by
  classical
  let w : (Fin k → α) → ℝ := ProductLaw.weight (fun _ : Fin k => p)
  let G := fun (x : Fin k → α) i => g (x i)
  let C := fun (x : Fin k → α) i => RandomGrid.cell δ u (v (x i))
  let Y := fun (x : Fin k → α) => ∑ i, v (x i)
  have hw : ∀ x ∈ (Finset.univ : Finset (Fin k → α)), 0 ≤ w x :=
    fun x _ => ProductLaw.weight_nonneg _ (fun _ a => hp a) x
  have he := conditionalEntropy_eq_of_fibers Finset.univ w
    (fun x i => C x i :: G x i) (fun x => (C x,G x)) Y hw (by
      intro x _ y _
      constructor
      · intro h
        apply Prod.ext
        · funext i
          exact (List.cons.inj (congrFun h i)).1
        · funext i
          exact (List.cons.inj (congrFun h i)).2
      · intro h
        rw [Prod.mk.injEq] at h
        rw [h.1,h.2])
  rw [he, conditionalEntropy_chain Finset.univ w C G Y hw,
    conditionalEntropy_condition_swap Finset.univ w C G Y hw]

end FiniteRefinement

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.SumsetBound ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uβ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FairPairs

open FiniteEntropy

theorem Law.support_nonempty (ν : Law) : ν.support.Nonempty := by
  by_contra h
  have := ν.prob_sum
  rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at this
  norm_num at this

theorem mass_support {β : Type uβ} [DecidableEq β] (ν : Law) (g : ℝ → β) (b : β) :
    mass Finset.univ (fun a : ν.support => ν.prob a) (fun a => g a) b =
      mass ν.support ν.prob g b := by
  classical
  simp only [mass, Finset.sum_filter]
  exact Finset.sum_coe_sort ν.support (fun a => if g a = b then ν.prob a else 0)

theorem sum_support₂ (ν : Law) (f : ℝ → ℝ → ℝ) :
    (∑ a : ν.support, ∑ b : ν.support, f a b) = ∑ a ∈ ν.support, ∑ b ∈ ν.support, f a b := by
  calc
    _ = ∑ a : ν.support, ∑ b ∈ ν.support, f a b := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_coe_sort ν.support (f a)
    _ = _ := Finset.sum_coe_sort ν.support (fun a => ∑ b ∈ ν.support, f a b)

theorem mean_deviation_le_bandCost {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) (R : ℝ)
    (hd : ∀ a ∈ ν.support, ∀ b ∈ ν.support, g a = g b → |a-b| ≤ R) :
    (∑ a : ν.support, ν.prob a * |(a : ℝ)-FiniteRefinement.cellMean
      (fun b : ν.support => ν.prob b) (fun b => (b : ℝ)) (fun b => g b) (g a)|) ≤
      ν.bandCost R := by
  classical
  have hj := FiniteRefinement.mean_deviation_le_coupling
    (fun a : ν.support => ν.prob a) (fun a => (a : ℝ)) (fun a => g a)
    (fun a => ν.prob_pos a a.property)
  have he : (∑ a : ν.support, ∑ b : ν.support,
      (if g a = g b then ν.prob a*ν.prob b /
        mass Finset.univ (fun x : ν.support => ν.prob x) (fun x => g x) (g a) else 0)*
      |(a : ℝ)-(b : ℝ)|) =
      ∑ a ∈ ν.support, ∑ b ∈ ν.support, conditionalCoupling ν g a b * |b-a| := by
    simp only [mass_support, conditionalCoupling, abs_sub_comm]
    exact sum_support₂ ν (fun a b => (if g a = g b then ν.prob a*ν.prob b /
      mass ν.support ν.prob g (g a) else 0) * |a-b|)
  rw [he] at hj
  apply hj.trans
  exact coupling_distance_le (conditionalCoupling ν g) R
    (fun x hx y hy => conditionalCoupling_nonneg ν g hx hy)
    (fun x _ y _ => conditionalCoupling_symm ν g x y)
    (fun x hx => (conditionalCoupling_row ν g hx).le)
    (by
      intro x hx y hy hxy
      apply conditionalCoupling_eq_zero_of_ne
      intro he
      have hh := hd x hx y hy he
      rw [abs_sub_comm] at hh
      exact (not_le_of_gt hxy) hh)

theorem exists_capacity_refinement (ν : Law) (g : ℝ → List ℤ)
    (k : ℕ) (hk : 1 ≤ k) (R : ℝ) (hR : 0 < R)
    (hd : ∀ a ∈ ν.support, ∀ b ∈ ν.support, g a = g b → |a-b| ≤ R) :
    ∃ g' : ℝ → List ℤ,
      (∀ a ∈ ν.support, ∀ b ∈ ν.support, g' a = g' b → |a-b| ≤ R/4) ∧
      conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => fun a : ν.support => ν.prob a))
        (fun x i => g' (x i)) (fun x => ∑ i, (x i : ℝ)) ≤
      conditionalEntropy Finset.univ (ProductLaw.weight (fun _ : Fin k => fun a : ν.support => ν.prob a))
        (fun x i => g (x i)) (fun x => ∑ i, (x i : ℝ)) +
      (352*k^4/R)*ν.bandCost R*Real.log 2 := by
  classical
  let p : ν.support → ℝ := fun a => ν.prob a
  have hp : ∀ a, 0 < p a := fun a => ν.prob_pos a a.property
  obtain ⟨u,hu⟩ := FiniteRefinement.exists_entropy_step p (fun a => (a : ℝ)) (fun a => g a)
    hp ν.subtype_sum k hk (R/4) (by positivity) (by
      intro a b hab
      simpa only [mul_div_cancel₀ _ (by norm_num : (4 : ℝ) ≠ 0)] using hd a a.property b b.property hab)
  refine ⟨fun a => RandomGrid.cell (R/4) u a :: g a, ?_, ?_⟩
  · intro a _ b _ he
    exact (RandomGrid.cell_eq_distance_lt (by positivity) u (List.cons.inj he).1).le
  · rw [FiniteRefinement.refinement_increment p (fun a => (a : ℝ)) (fun a => g a)
      (fun a => (hp a).le) k (R/4) u]
    apply add_le_add le_rfl
    apply hu.trans
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mean_deviation_le_bandCost ν g R hd)
        (by positivity : 0 ≤ (88 : ℝ)*k^4/(R/4)))
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    convert hh using 1; ring

theorem exists_fine_partition (ν : Law) (k : ℕ) (hk : 1 ≤ k)
    (ρ : ℝ) (hρ : 0 < ρ) (J : ℕ) :
    ∃ g : ℝ → List ℤ,
      (∀ a ∈ ν.support, ∀ b ∈ ν.support, g a = g b → |a-b| ≤ ρ/4^J) ∧
      ν.partitionEntropy k g ≤ ν.partitionEntropy k (fun x => [⌊x/ρ⌋]) +
        ∑ h ∈ Finset.range J, ν.refinementCost k (ρ/4^h) := by
  classical
  induction J with
  | zero =>
    refine ⟨fun x => [⌊x/ρ⌋], ?_, ?_⟩
    · intro a _ b _ he
      have hh : RandomGrid.cell ρ 0 a = RandomGrid.cell ρ 0 b := by
        simpa only [RandomGrid.cell, RandomGrid.shift_zero, add_zero] using (List.cons.inj he).1
      simpa only [pow_zero, div_one] using (RandomGrid.cell_eq_distance_lt hρ 0 hh).le
    · simp only [Finset.range_zero, Finset.sum_empty, add_zero, le_refl]
  | succ J ih =>
    obtain ⟨g,hd,hg⟩ := ih
    obtain ⟨g',hd',hg'⟩ := exists_capacity_refinement ν g k hk (ρ/4^J) (by positivity) hd
    refine ⟨g', ?_, ?_⟩
    · intro a ha b hb he
      simpa only [pow_succ, div_div] using hd' a ha b hb he
    · change ν.partitionEntropy k g' ≤ ν.partitionEntropy k g + ν.refinementCost k (ρ/4^J) at hg'
      rw [Finset.sum_range_succ]
      linarith

theorem exists_separating_depth (ν : Law) (ρ : ℝ) :
    ∃ J : ℕ, ∀ a ∈ ν.support, ∀ b ∈ ν.support, a ≠ b → ρ/4^J < |a-b| := by
  classical
  have ht : Filter.Tendsto (fun n : ℕ => ρ/(4 : ℝ)^n) Filter.atTop (nhds 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/4)
      (by norm_num : (1 : ℝ)/4 < 1)).const_mul ρ
    simpa only [div_pow, one_pow, mul_zero, div_eq_mul_inv, one_mul, inv_pow] using hh
  have he : ∀ᶠ J : ℕ in Filter.atTop,
      ∀ a ∈ ν.support, ∀ b ∈ ν.support, a ≠ b → ρ/4^J < |a-b| := by
    apply (Filter.eventually_all_finset ν.support).mpr
    intro a ha
    apply (Filter.eventually_all_finset ν.support).mpr
    intro b hb
    by_cases hab : a = b
    · exact Filter.Eventually.of_forall (fun _ h => (h hab).elim)
    · exact (ht.eventually (isOpen_Iio.mem_nhds (abs_pos.mpr (sub_ne_zero.mpr hab)))).mono
        (fun J h _ => h)
  exact he.exists

theorem dyadic_upper_eq (ℓ : ℤ) : (2 : ℝ)^(1-ℓ) = 2*(2 : ℝ)^(-ℓ) := by
  rw [sub_eq_add_neg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]

theorem band_scale_sum (ρ : ℝ) (hρ : 0 < ρ) (ℓ : ℤ) (J : ℕ) :
    (∑ h ∈ (Finset.range J).filter (fun h => (2 : ℝ)^(-ℓ) ≤ ρ/4^h),
      (2 : ℝ)^(1-ℓ)/(ρ/4^h)) ≤ if (2 : ℝ)^(-ℓ) ≤ ρ then 8/3 else 0 := by
  classical
  let s := (Finset.range J).filter (fun h => (2 : ℝ)^(-ℓ) ≤ ρ/4^h)
  have hpow : ∀ h : ℕ, (0 : ℝ) < 4^h := fun h => pow_pos (by norm_num) h
  have hs : ∀ h ∈ s, ((2 : ℝ)^(1-ℓ)/ρ)*4^h ≤ 2 := by
    intro h hh
    have he := (le_div_iff₀ (hpow h)).mp (Finset.mem_filter.mp hh).2
    rw [dyadic_upper_eq]
    have he' : (2*(2 : ℝ)^(-ℓ)*4^h)/ρ ≤ 2 :=
      (div_le_iff₀ hρ).mpr (by nlinarith)
    convert he' using 1; ring
  have hgeom := geometric_fine_scale_bound s
    (div_nonneg (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le hρ.le) hs
  have heq : (∑ h ∈ s, (2 : ℝ)^(1-ℓ)/(ρ/4^h)) =
      ∑ h ∈ s, ((2 : ℝ)^(1-ℓ)/ρ)*4^h := by
    apply Finset.sum_congr rfl
    intro h _
    field_simp
  change (∑ h ∈ s, _) ≤ _
  rw [heq]
  by_cases hℓ : (2 : ℝ)^(-ℓ) ≤ ρ
  · rw [ite_eq_left hℓ]
    exact hgeom
  · rw [ite_eq_right hℓ]
    have hempty : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro h hh
      have he := (le_div_iff₀ (hpow h)).mp (Finset.mem_filter.mp hh).2
      have hone : (1 : ℝ) ≤ 4^h := one_le_pow₀ (by norm_num)
      have hlower : (2 : ℝ)^(-ℓ) ≤ (2 : ℝ)^(-ℓ)*4^h :=
        le_mul_of_one_le_right (zpow_pos (by norm_num : (0 : ℝ) < 2) _).le hone
      exact hℓ (hlower.trans he)
    simp only [hempty, Finset.sum_empty, le_refl]

theorem sum_refinementCost_le (ν : Law) (k : ℕ) (ρ : ℝ) (hρ : 0 < ρ) (J : ℕ) :
    (∑ h ∈ Finset.range J, ν.refinementCost k (ρ/4^h)) ≤
      60000*k^4*Real.log 2 * ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ 2*ρ),
        capacity ν ℓ := by
  classical
  let C : ℝ := 352*k^4*Real.log 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have he : (∑ h ∈ Finset.range J, ν.refinementCost k (ρ/4^h)) =
      C * ∑ ℓ ∈ ν.bandSupport, capacity ν ℓ *
        ∑ h ∈ (Finset.range J).filter (fun h => (2 : ℝ)^(-ℓ) ≤ ρ/4^h),
          (2 : ℝ)^(1-ℓ)/(ρ/4^h) := by
    simp only [Law.refinementCost, Law.bandCost, Finset.sum_filter, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ℓ _
    apply Finset.sum_congr rfl
    intro h _
    dsimp only [C]
    split_ifs <;> ring
  rw [he]
  have hpoint := Finset.sum_le_sum (s := ν.bandSupport) (fun ℓ _ =>
    mul_le_mul_of_nonneg_left (band_scale_sum ρ hρ ℓ J) (capacity_nonneg ν ℓ))
  calc
    _ ≤ C * ∑ ℓ ∈ ν.bandSupport, capacity ν ℓ *
        (if (2 : ℝ)^(-ℓ) ≤ ρ then 8/3 else 0) := mul_le_mul_of_nonneg_left hpoint hC
    _ = (C*(8/3)) * ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ ρ), capacity ν ℓ := by
      simp only [Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ℓ _
      split_ifs <;> ring
    _ ≤ (60000*k^4*Real.log 2) *
        ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ ρ), capacity ν ℓ := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun ℓ _ => capacity_nonneg ν ℓ))
      dsimp only [C]
      have hn : 0 ≤ (k : ℝ)^4*Real.log 2 := by positivity
      nlinarith
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ℓ hℓ
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hℓ).1,
          (Finset.mem_filter.mp hℓ).2.trans (by linarith)⟩
      · intro ℓ _ _
        exact capacity_nonneg ν ℓ

theorem observableEntropy_support {β : Type uβ} [DecidableEq β]
    (ν : Law) (g : ℝ → β) :
    observableEntropy Finset.univ (fun a : ν.support => ν.prob a) (fun a => g a) =
      observableEntropy ν.support ν.prob g := by
  classical
  have he : (Finset.univ : Finset ν.support).image (fun a : ν.support => g (a : ℝ)) = ν.support.image g := by
    ext b
    constructor
    · intro hb
      obtain ⟨a,_,hab⟩ := Finset.mem_image.mp hb
      exact Finset.mem_image.mpr ⟨a,a.property,hab⟩
    · intro hb
      obtain ⟨a,ha,hab⟩ := Finset.mem_image.mp hb
      exact Finset.mem_image.mpr ⟨⟨a,ha⟩,Finset.mem_univ _,hab⟩
  simp only [observableEntropy, he, entropy, mass_support]

theorem pair_bound_natural (ν : Law) (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ) (hρ : 0 < ρ) :
    k * (entropy ν.support ν.prob - observableEntropy ν.support ν.prob (fun x => ⌊x/ρ⌋)) ≤
      Real.log (ν.sumset k).card + 60000*k^4*Real.log 2 *
        ∑ ℓ ∈ ν.bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ 2*ρ), capacity ν ℓ := by
  classical
  obtain ⟨a,ha⟩ := ν.support_nonempty
  have : Nonempty ν.support := ⟨⟨a,ha⟩⟩
  let p : ν.support → ℝ := fun a => ν.prob a
  let w := ProductLaw.weight (fun _ : Fin k => p)
  let Y : (Fin k → ν.support) → ℝ := fun x => ∑ i, (x i : ℝ)
  let C₀ : (Fin k → ν.support) → Fin k → List ℤ := fun x i => [⌊(x i : ℝ)/ρ⌋]
  have hp : ∀ a, 0 ≤ p a := fun a => (ν.prob_pos a a.property).le
  have hw : ∀ x ∈ (Finset.univ : Finset (Fin k → ν.support)), 0 ≤ w x :=
    fun x _ => ProductLaw.weight_nonneg _ (fun _ a => hp a) x
  have hw1 : ∑ x, w x = 1 := ProductLaw.weight_sum _ (fun _ => ν.subtype_sum)
  obtain ⟨J,hJ⟩ := exists_separating_depth ν ρ
  obtain ⟨g,hd,hg⟩ := exists_fine_partition ν k hk ρ hρ J
  let G : (Fin k → ν.support) → Fin k → List ℤ := fun x i => g (x i)
  have hi : Function.Injective (fun a : ν.support => g a) := by
    intro a b he
    apply Subtype.ext
    by_contra hab
    exact (not_lt_of_ge (hd a a.property b b.property he)) (hJ a a.property b b.property hab)
  have hG : Function.Injective G := by
    intro x y he
    funext i
    exact hi (congrFun he i)
  have hent : observableEntropy Finset.univ w G = k*entropy ν.support ν.prob := by
    rw [observableEntropy_of_injective Finset.univ w G hw hG, ProductLaw.entropy _ (fun _ => ν.subtype_sum)]
    have he : entropy Finset.univ p = entropy ν.support ν.prob :=
      Finset.sum_coe_sort ν.support (fun a => Real.negMulLog (ν.prob a))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact congrArg (fun z => (k : ℝ)*z) he
  have hinit : observableEntropy Finset.univ w C₀ =
      k*observableEntropy ν.support ν.prob (fun x => ⌊x/ρ⌋) := by
    rw [ProductLaw.observable_entropy p (fun a : ν.support => [⌊(a : ℝ)/ρ⌋]) hp ν.subtype_sum]
    simp only [Fintype.card_fin]
    rw [observableEntropy_support ν (fun a => [⌊a/ρ⌋])]
    congr 1
    apply observableEntropy_eq_of_fibers _ _ _ _ (fun x hx => (ν.prob_pos x hx).le)
    intro x _ y _
    simp only [List.cons.injEq, and_true]
  have hy : observableEntropy Finset.univ w Y ≤ Real.log (ν.sumset k).card :=
    observableEntropy_le_log_on_superset Finset.univ (ν.sumset k) w Y
      (fun x _ => Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩) hw hw1
  have hjoint := observableEntropy_fst_le Finset.univ w G Y hw
  have hcinit := conditionalEntropy_le Finset.univ w C₀ Y hw hw1
  have hsum := sum_refinementCost_le ν k ρ hρ J
  change conditionalEntropy Finset.univ w G Y ≤ conditionalEntropy Finset.univ w C₀ Y + _ at hg
  rw [hent] at hjoint
  rw [hinit] at hcinit
  unfold conditionalEntropy at hg hcinit
  linarith

end FairPairs

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.Windows ----
namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace Windows

theorem ceiling_increment (x y : ℝ) :
    (⌈y⌉ : ℝ) - (⌈x⌉ : ℝ) ≤ y - x + 1 := by
  linarith [Int.le_ceil x, Int.ceil_lt_add_one y]

theorem finer_window_before {σ : ℕ → ℝ} (hσ : Monotone σ)
    {j k n : ℕ} {L a B : ℤ} {d : ℝ}
    (hadvance : σ (j + n) - σ j ≤ d)
    (hstart : a ≤ L - ⌈σ j⌉) (hcoarse : L - ⌈σ k⌉ ≤ B)
    (hgap : (B : ℝ) < (a : ℝ) - d - 1) : j + n < k := by
  have hb : (B : ℝ) < (L : ℝ) - (⌈σ (j + n)⌉ : ℝ) := by
    have hs : (a : ℝ) ≤ (L : ℝ) - (⌈σ j⌉ : ℝ) := by exact_mod_cast hstart
    linarith [ceiling_increment (σ j) (σ (j + n))]
  by_contra h
  have hm := Int.ceil_mono (hσ (Nat.le_of_not_gt h))
  have hc : (L : ℝ) - (⌈σ k⌉ : ℝ) ≤ (B : ℝ) := by exact_mod_cast hcoarse
  have hm' : (⌈σ k⌉ : ℝ) ≤ (⌈σ (j + n)⌉ : ℝ) := by exact_mod_cast hm
  linarith

theorem multiples_disjoint {n j k : ℕ} (hjk : j ≠ k) :
    Disjoint (Finset.Ico (j * n) (j * n + n)) (Finset.Ico (k * n) (k * n + n)) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨hja, haj⟩ := Finset.mem_Ico.mp ha
  obtain ⟨hka, hak⟩ := Finset.mem_Ico.mp hb
  rcases lt_or_gt_of_ne hjk with h | h
  · have hle := Nat.mul_le_mul_right n h
    have : j * n + n ≤ k * n := by simpa [Nat.add_mul] using hle
    omega
  · have hle := Nat.mul_le_mul_right n h
    have : k * n + n ≤ j * n := by simpa [Nat.add_mul] using hle
    omega

theorem sum_disjoint_drops_le {α : Type uα} (s : Finset α) (u v : α → ℕ)
    (huv : ∀ i ∈ s, u i ≤ v i)
    (hd : (↑s : Set α).PairwiseDisjoint (fun i => Finset.Ico (u i) (v i)))
    (g : ℕ → ℝ) (hg : Antitone g) (hgn : ∀ i, 0 ≤ g i) :
    ∑ i ∈ s, (g (u i) - g (v i)) ≤ g 0 := by
  classical
  let N := s.sup v
  have htel : ∀ i ∈ s, g (u i) - g (v i) =
      ∑ t ∈ Finset.Ico (u i) (v i), (g t - g (t + 1)) := by
    intro i hi
    have ht := Finset.sum_Ico_sub (fun t => -g t) (huv i hi)
    simpa only [neg_sub_neg] using ht.symm
  simp_rw [Finset.sum_congr rfl htel]
  rw [← Finset.sum_biUnion hd]
  calc
    ∑ t ∈ s.biUnion (fun i => Finset.Ico (u i) (v i)), (g t - g (t + 1)) ≤
        ∑ t ∈ Finset.range N, (g t - g (t + 1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro t ht
        obtain ⟨i, hi, hit⟩ := Finset.mem_biUnion.mp ht
        exact Finset.mem_range.mpr ((Finset.mem_Ico.mp hit).2.trans_le (Finset.le_sup hi))
      · intro t _ _
        exact sub_nonneg.mpr (hg (Nat.le_succ t))
    _ = g 0 - g N := by
      simpa only [neg_sub_neg] using Finset.sum_range_sub (fun t => -g t) N
    _ ≤ g 0 := sub_le_self _ (hgn N)

end Windows

end EntropyRateDimension

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.WordTypes ----
namespace OAI

universe uι

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace System
variable {ι : Type uι} [Fintype ι]

theorem wordAffine_append (S : System ι) (v w : List ι) :
    S.wordAffine (v++w) = ((S.wordAffine v).1*(S.wordAffine w).1,
      (S.wordAffine v).1*(S.wordAffine w).2+(S.wordAffine v).2) := by
  induction v with
  | nil => simp [wordAffine]
  | cons i v ih => simp only [List.cons_append,wordAffine,ih]; ext <;> dsimp <;> ring

theorem map_entropy_as_observation (S : System ι) (n : ℕ) :
    FiniteEntropy.observableEntropy Finset.univ (S.wordWeight (n := n)) S.completeMap =
      S.walkEntropy n*Real.log 2 := by
  classical
  unfold walkEntropy FiniteEntropy.observableEntropy FiniteEntropy.entropy mapSupport
  rw [div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ)<2)))]
  rfl

end System
end EntropyRateDimension

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.DigitSumset ----
namespace OAI

universe uα uβ

section

open scoped BigOperators
namespace EntropyRateDimension
namespace DigitSumset

theorem counts_expand {α : Type uα} {β : Type uβ} [Fintype α] [Fintype β] {k : ℕ}
    (v : β → α → ℝ) (w : Fin k → β → α) :
    ∑ t, ∑ j, v j (w t j) = ∑ j, ∑ a, ((counts w j a).val : ℝ)*v j a := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_fiberwise Finset.univ (fun t : Fin k => w t j)]
  apply Finset.sum_congr rfl
  intro a _
  calc
    ∑ t ∈ Finset.univ.filter (fun t : Fin k => w t j=a), v j (w t j) =
        ∑ _t ∈ Finset.univ.filter (fun t : Fin k => w t j=a), v j a := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [(Finset.mem_filter.mp ht).2]
    _ = _ := by simp [counts]

theorem card_sumset_le {α : Type uα} {β : Type uβ} [Fintype α] [Fintype β]
    (S : Finset ℝ) (v : β → α → ℝ)
    (hS : ∀ x ∈ S, ∃ w : β → α, x=∑ j, v j (w j)) (k : ℕ) :
    (sumset S k).card ≤ (k+1)^(Fintype.card β*Fintype.card α) := by
  classical
  let F : (β → α → Fin (k+1)) → ℝ := fun c => ∑ j, ∑ a, ((c j a).val : ℝ)*v j a
  have hin : sumset S k ⊆ Finset.univ.image F := by
    intro x hx
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hx
    choose w hw using (fun t => hS (u t) (u t).property)
    apply Finset.mem_image.mpr
    refine ⟨counts w,Finset.mem_univ _,?_⟩
    change (∑ j, ∑ a, ((counts w j a).val : ℝ)*v j a)=∑ t, (u t : ℝ)
    rw [← counts_expand]
    exact Finset.sum_congr rfl (fun t _ => (hw t).symm)
  calc
    (sumset S k).card ≤ (Finset.univ.image F).card := Finset.card_le_card hin
    _ ≤ (Finset.univ : Finset (β → α → Fin (k+1))).card := Finset.card_image_le
    _ = _ := by simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,← pow_mul]; rw [Nat.mul_comm]

end DigitSumset
end EntropyRateDimension

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.LocalEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace FiniteEntropy

theorem entropy_le_mass_log_card {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    entropy s p ≤ Real.negMulLog (∑ a ∈ s, p a)+
      (∑ a ∈ s, p a)*Real.log (max 1 (s.card : ℝ)) := by
  let P := ∑ a ∈ s, p a
  have hP : 0 ≤ P := Finset.sum_nonneg hp
  rw [entropy_normalize s p hp]
  change Real.negMulLog P+P*entropy s (fun a => p a/P) ≤
    Real.negMulLog P+P*Real.log (max 1 (s.card : ℝ))
  rcases eq_or_lt_of_le hP with he | he
  · simp only [← he,zero_mul,add_zero,le_refl]
  have hs : 0 < s.card := Finset.card_pos.mpr (by
    by_contra h
    have hse : s=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [P,hse,Finset.sum_empty] at he
    exact lt_irrefl _ he)
  have hh := entropy_le_log_card s (fun a => p a/P)
    (fun a ha => div_nonneg (hp a ha) hP) (by rw [← Finset.sum_div]; exact div_self he.ne')
  have hcard : max 1 (s.card : ℝ)=(s.card : ℝ) := max_eq_right (by exact_mod_cast hs)
  rw [hcard]
  exact add_le_add_right (mul_le_mul_of_nonneg_left hh hP) _

theorem entropy_split_bound {α : Type uα} [DecidableEq α] (s a : Finset α)
    (p : α → ℝ) (ha : a ⊆ s) (hp : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∑ i ∈ s, p i=1) :
    entropy s p ≤ Real.log 2+Real.log (max 1 (a.card : ℝ))+
      (∑ i ∈ s\a, p i)*Real.log (max 1 (s.card : ℝ)) := by
  classical
  let P := ∑ i ∈ a, p i
  let Q := ∑ i ∈ s\a, p i
  have hP : 0 ≤ P := Finset.sum_nonneg (fun i hi => hp i (ha hi))
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i hi => hp i (Finset.mem_sdiff.mp hi).1)
  have hPQ : P+Q=1 := by
    change (∑ i ∈ a, p i)+(∑ i ∈ s\a, p i)=1
    rw [add_comm,Finset.sum_sdiff ha,hp1]
  have hPa := entropy_le_mass_log_card a p (fun i hi => hp i (ha hi))
  have hQb := entropy_le_mass_log_card (s\a) p (fun i hi => hp i (Finset.mem_sdiff.mp hi).1)
  have hnum := entropy_le_log_card (Finset.univ : Finset (Fin 2))
    (fun i => if i=0 then P else Q) (by intro i _; split <;> assumption)
    (by simpa [Fin.sum_univ_two] using hPQ)
  have hn : Real.negMulLog P+Real.negMulLog Q ≤ Real.log 2 := by
    simpa [entropy,Fin.sum_univ_two] using hnum
  have hlogA : 0 ≤ Real.log (max 1 (a.card : ℝ)) := Real.log_nonneg (le_max_left _ _)
  have hlogB : Real.log (max 1 ((s\a).card : ℝ)) ≤ Real.log (max 1 (s.card : ℝ)) := by
    apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    exact max_le_max_left 1 (by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := s) (t := a)))
  have he : entropy s p=entropy a p+entropy (s\a) p := by
    unfold entropy
    rw [add_comm,Finset.sum_sdiff ha]
  rw [he]
  change entropy a p ≤ Real.negMulLog P+P*_ at hPa
  change entropy (s\a) p ≤ Real.negMulLog Q+Q*_ at hQb
  change _ ≤ Real.log 2+_+Q*_
  nlinarith [mul_le_mul_of_nonneg_left hlogB hQ,mul_nonneg hQ hlogA]

end FiniteEntropy

namespace MeasureEntropy

theorem entropy_subset_bound {α : Type uα} {β : Type uβ} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β] [DecidableEq β]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → β) (hf : Measurable f)
    (s a : Finset β) (ha : a ⊆ s) (hs : ∀ᵐ x ∂μ, f x ∈ s) {η : ℝ}
    (hη : μ.real {x | f x ∉ a} ≤ η) :
    entropy μ f ≤ Real.log 2+Real.log (max 1 (a.card : ℝ))+
      η*Real.log (max 1 (s.card : ℝ)) := by
  have hh := FiniteEntropy.entropy_split_bound s a (mass μ f) ha
    (fun i _ => mass_nonneg μ f i) (mass_sum μ f hf s hs)
  have hm : ∑ i ∈ s\a, mass μ f i = μ.real {x | f x ∉ a} := by
    have hd : (↑(s\a) : Set β).PairwiseDisjoint (fun b => {x | f x=b}) := by
      intro b _ c _ hbc
      exact Set.disjoint_left.mpr (fun _ hx hy => hbc (hx.symm.trans hy))
    have hie : (⋃ b ∈ s\a, {x | f x=b}) = {x | f x ∈ s\a} := by
      ext x
      simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
      constructor
      · rintro ⟨b,hb,hxb⟩
        exact hxb ▸ hb
      · intro hx
        exact ⟨f x,hx,rfl⟩
    have he : (⋃ b ∈ s\a, {x | f x=b}) =ᵐ[μ] {x | f x ∉ a} := by
      rw [hie]
      filter_upwards [hs] with x hx
      apply propext
      show f x ∈ s \ a ↔ f x ∉ a
      simp only [Finset.mem_sdiff,hx,true_and]
    unfold mass
    rw [← measureReal_biUnion_finset (μ := μ) hd (fun b _ => hf (measurableSet_singleton b))]
    exact measureReal_congr he
  rw [entropy_eq_sum μ f s hs]
  rw [hm] at hh
  exact hh.trans (add_le_add_right (mul_le_mul_of_nonneg_right hη
    (Real.log_nonneg (le_max_left _ _))) _)

theorem card_mul_mass_le_one {α : Type uα} (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (s : Finset α) (x : α → ℝ) {r q : ℝ}
    (hd : (↑s : Set α).PairwiseDisjoint (fun i => Metric.ball (x i) r))
    (hq : ∀ i ∈ s, q ≤ μ.real (Metric.ball (x i) r)) :
    (s.card : ℝ)*q ≤ 1 := by
  calc
    (s.card : ℝ)*q = ∑ i ∈ s, q := by simp
    _ ≤ ∑ i ∈ s, μ.real (Metric.ball (x i) r) := Finset.sum_le_sum hq
    _ = μ.real (⋃ i ∈ s, Metric.ball (x i) r) :=
      (measureReal_biUnion_finset hd (fun _ _ => measurableSet_ball)).symm
    _ ≤ 1 := (measureReal_mono (Set.subset_univ _)).trans_eq (by simp)

theorem label_ball_disjoint {s u x y : ℝ} (hs : 0 < s)
    (hne : label s u x ≠ label s u y) (hmod : label s u x % 3=label s u y % 3) :
    Disjoint (Metric.ball x (s/2)) (Metric.ball y (s/2)) := by
  have hd : s ≤ dist x y := by
    rw [Real.dist_eq]
    have hx1 := Int.floor_le (x/s+u)
    have hx2 := Int.lt_floor_add_one (x/s+u)
    have hy1 := Int.floor_le (y/s+u)
    have hy2 := Int.lt_floor_add_one (y/s+u)
    have hdiff : label s u x+3 ≤ label s u y ∨ label s u y+3 ≤ label s u x := by omega
    rcases hdiff with h | h
    · have h' : (label s u x : ℝ)+3 ≤ (label s u y : ℝ) := by exact_mod_cast h
      change (⌊x/s+u⌋ : ℝ)+3 ≤ (⌊y/s+u⌋ : ℝ) at h'
      have hxy : 2 < y/s-x/s := by linarith
      have hmul := (lt_div_iff₀ hs).mp (by simpa only [← sub_div] using hxy)
      rw [abs_of_nonpos (by linarith : x-y ≤ 0)]
      linarith
    · have h' : (label s u y : ℝ)+3 ≤ (label s u x : ℝ) := by exact_mod_cast h
      change (⌊y/s+u⌋ : ℝ)+3 ≤ (⌊x/s+u⌋ : ℝ) at h'
      have hxy : 2 < x/s-y/s := by linarith
      have hmul := (lt_div_iff₀ hs).mp (by simpa only [← sub_div] using hxy)
      rw [abs_of_nonneg (by linarith : 0 ≤ x-y)]
      linarith
  apply Set.disjoint_left.mpr
  intro z hz hzy
  have hz1 := Metric.mem_ball.mp hz
  have hz2 := Metric.mem_ball.mp hzy
  have ht := dist_triangle_left x y z
  linarith

theorem good_labels_card_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s u q : ℝ} (hs : 0 < s) (a : Finset ℤ) (x : ℤ → ℝ)
    (hx : ∀ i ∈ a, label s u (x i)=i)
    (hq : ∀ i ∈ a, q ≤ μ.real (Metric.ball (x i) (s/2))) :
    (a.card : ℝ)*q ≤ 3 := by
  let color : ℤ → Fin 3 := fun i => ⟨(i%3).toNat, by omega⟩
  have hc : ∀ c : Fin 3,
      (((a.filter (fun i => color i=c)).card : ℕ) : ℝ)*q ≤ 1 := by
    intro c
    apply card_mul_mass_le_one μ _ x
    · intro i hi j hj hij
      have hia := (Finset.mem_filter.mp hi).1
      have hja := (Finset.mem_filter.mp hj).1
      apply label_ball_disjoint hs
      · rwa [hx i hia,hx j hja]
      · rw [hx i hia,hx j hja]
        have he := congrArg Fin.val ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
        dsimp [color] at he
        omega
    · intro i hi
      exact hq i (Finset.mem_filter.mp hi).1
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ => hc c)
  have he : ∑ c : Fin 3, (((a.filter (fun i => color i=c)).card : ℕ) : ℝ) = (a.card : ℝ) := by
    simp only [← Nat.cast_sum]
    congr 1
    simpa only [Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] using
      (Finset.sum_fiberwise a color (fun _ => (1 : ℕ)))
  rw [← Finset.sum_mul,he] at hsum
  simpa using hsum

theorem grid_le_of_ball_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {B s u q η : ℝ} (hs : 0 < s) (hq : 0 < q)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (E : Set ℝ) (hη : μ.real Eᶜ ≤ η)
    (hball : ∀ x ∈ E, q ≤ μ.real (Metric.ball x (s/2))) :
    grid μ s u ≤ Real.log 2+Real.log (max 1 (3/q))+
      η*Real.log (max 1 ((Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card : ℝ)) := by
  classical
  let t := Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋
  let a := t.filter (fun i => ∃ x ∈ E, label s u x=i)
  have ha : a ⊆ t := Finset.filter_subset _ _
  have has : ∀ i ∈ a, ∃ x ∈ E, label s u x=i := fun i hi => (Finset.mem_filter.mp hi).2
  let x : ℤ → ℝ := fun i => if hi : i ∈ a then (has i hi).choose else 0
  have hx : ∀ i ∈ a, x i ∈ E ∧ label s u (x i)=i := by
    intro i hi
    dsimp only [x]
    rw [dite_eq_left hi]
    exact (has i hi).choose_spec
  have hcard := good_labels_card_bound μ hs a x
    (fun i hi => (hx i hi).2) (fun i hi => hball _ (hx i hi).1)
  have hm : μ.real {z | label s u z ∉ a} ≤ η := by
    have hae : {z | label s u z ∉ a} ≤ᵐ[μ] Eᶜ := by
      filter_upwards [label_ae_uniform μ hs hB hu] with z hz hza
      intro hzE
      exact hza (Finset.mem_filter.mpr ⟨hz,⟨z,hzE,rfl⟩⟩)
    exact (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hae)).trans hη
  have hh := entropy_subset_bound μ (label s u) (label_measurable s u) t a ha
    (label_ae_uniform μ hs hB hu) hm
  have hlog : Real.log (max 1 (a.card : ℝ)) ≤ Real.log (max 1 (3/q)) := by
    apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    exact max_le_max_left _ ((le_div_iff₀ hq).mpr hcard)
  exact hh.trans (by dsimp only [t]; linarith)

theorem grid_support_card_le {B s : ℝ} (hB : 0 ≤ B) (hs : 0 < s) (hs1 : s ≤ 1) :
    ((Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card : ℝ) ≤ (2*B+3)/s := by
  have hf : ⌊-B/s⌋ ≤ ⌊B/s+1⌋ := Int.floor_le_floor (by
    have := div_nonneg hB hs.le
    simp only [neg_div]
    linarith)
  rw [Int.card_Icc, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega : 0 ≤ ⌊B/s+1⌋+1-⌊-B/s⌋)]
  push_cast
  have h1 := Int.floor_le (B/s+1)
  have h2 := Int.lt_floor_add_one (-B/s)
  have h3 : (3 : ℝ) ≤ 3/s := (le_div_iff₀ hs).mpr (by nlinarith)
  calc
    (⌊B/s+1⌋ : ℝ)+1-⌊-B/s⌋ ≤ 2*B/s+3 := by
      simp only [neg_div] at h2 ⊢
      rw [mul_div_assoc]
      linarith
    _ ≤ (2*B+3)/s := by rw [add_div]; linarith

end MeasureEntropy
end EntropyRateDimension

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.LocalMass ----
namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace EntropyRateDimension
namespace LocalMass

theorem eventual_lower_of_limit (μ : Measure ℝ) [IsFiniteMeasure μ] {x e d : ℝ}
    (hx : x ∈ μ.support) (hde : d < e)
    (hlim : Tendsto (fun r => -Real.log (μ.real (closedBall x r)) / -Real.log r)
      (𝓝[>] 0) (𝓝 d)) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      r^e ≤ μ.real (closedBall x r) := by
  have hev := hlim.eventually (gt_mem_nhds hde)
  obtain ⟨R,hR,hRx⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨min R 1,lt_min hR zero_lt_one,?_⟩
  intro r hr hrR
  have hr1 : r < 1 := lt_of_lt_of_le hrR (min_le_right _ _)
  have harr : -Real.log (μ.real (closedBall x r)) / -Real.log r < e :=
    hRx ⟨by simpa [Real.dist_eq,abs_of_pos hr] using lt_of_lt_of_le hrR (min_le_left _ _),hr⟩
  have hh := (div_lt_iff₀ (neg_pos.mpr (Real.log_neg hr hr1))).mp harr
  have hmass : 0 < μ.real (closedBall x r) :=
    ENNReal.toReal_pos (ne_of_gt ((Measure.mem_support_iff_forall x).mp hx _
      (closedBall_mem_nhds x hr))) (measure_ne_top μ _)
  rw [Real.rpow_def_of_pos hr,← Real.exp_log hmass]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem large_uniform_mass_set (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {e η : ℝ} (he : 0 ≤ e) (hη : 0 < η)
    (hlocal : ∀ᵐ x ∂μ, ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      r^e ≤ μ.real (closedBall x r)) :
    ∃ E : Set ℝ, MeasurableSet E ∧ μ.real Eᶜ ≤ η ∧
      ∃ R : ℝ, 0 < R ∧ ∀ x ∈ E, ∀ r : ℝ, 0 < r → r < R →
        (r/2)^e ≤ μ.real (ball x r) := by
  let E : ℕ → Set ℝ := fun n => {x | ∀ q : ℚ, 0 < (q : ℝ) →
    (q : ℝ) < 1/((n : ℝ)+1) → (q : ℝ)^e ≤ μ.real (closedBall x q)}
  have hE : ∀ n, MeasurableSet (E n) := by
    intro n
    simp only [E,Set.ofPred_forall]
    apply MeasurableSet.iInter fun q : ℚ => ?_
    apply MeasurableSet.iInter fun _ : 0 < (q : ℝ) => ?_
    apply MeasurableSet.iInter fun _ : (q : ℝ) < 1/((n : ℝ)+1) => ?_
    have hm := measurable_measure_prodMk_left (ν := μ)
      (measurableSet_le (measurable_snd.dist measurable_fst) (measurable_const (a := (q : ℝ))))
    exact measurableSet_le measurable_const hm.ennreal_toReal
  have hmono : Monotone E := by
    intro n m hnm x hx q hq hqm
    apply hx q hq
    exact hqm.trans_le (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1))
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃ n, E n := by
    filter_upwards [hlocal] with x hx
    obtain ⟨R,hR,hRx⟩ := hx
    obtain ⟨n,hn⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (gt_mem_nhds hR)).exists
    exact mem_iUnion.mpr ⟨n,fun q hq hqn => hRx q hq (hqn.trans hn)⟩
  have hzero : μ (⋂ n, (E n)ᶜ)=0 := by
    rw [← compl_iUnion]
    exact ae_iff.mp hae
  have ht : Tendsto (fun n => μ ((E n)ᶜ)) atTop (𝓝 0) := by
    rw [← hzero]
    exact tendsto_measure_iInter_atTop (fun n => (hE n).compl.nullMeasurableSet)
      (fun n m hnm => compl_subset_compl.mpr (hmono hnm)) ⟨0,measure_ne_top μ _⟩
  have htR : Tendsto (fun n => μ.real ((E n)ᶜ)) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero,Function.comp_def,Measure.real] using (ENNReal.continuousAt_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp ht
  obtain ⟨n,hn⟩ := (htR.eventually (gt_mem_nhds hη)).exists
  refine ⟨E n,hE n,hn.le,1/((n : ℝ)+1),by positivity,?_⟩
  intro x hx r hr hrR
  obtain ⟨q,hq1,hq2⟩ := exists_rat_btwn (by linarith : r/2 < r)
  have hmass := hx q (lt_trans (by positivity) hq1) (hq2.trans hrR)
  have hsub : closedBall x (q : ℝ) ⊆ ball x r := fun y hy =>
    mem_ball.mpr ((mem_closedBall.mp hy).trans_lt hq2)
  exact (Real.rpow_le_rpow (by positivity) hq1.le he).trans
    (hmass.trans (measureReal_mono hsub))

end LocalMass
end EntropyRateDimension

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.EntropyDimension ----
namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace EntropyRateDimension.MeasureEntropy

theorem grid_le_of_quarter_power_ball_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {B s u d η : ℝ} (hB0 : 0 ≤ B) (hs : 0 < s) (hs1 : s ≤ 1)
    (hd : 0 ≤ d) (hη0 : 0 ≤ η)
    (hB : μ (Set.Icc (-B) B)ᶜ = 0) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (E : Set ℝ) (hη : μ.real Eᶜ ≤ η)
    (hball : ∀ x ∈ E, (s/4)^d ≤ μ.real (Metric.ball x (s/2))) :
    grid μ s u ≤ Real.log 6+d*Real.log 4+η*Real.log (2*B+3)+
      (d+η)*Real.log (1/s) := by
  have hq : 0 < (s/4)^d := Real.rpow_pos_of_pos (by positivity) _
  have hq1 : (s/4)^d ≤ 1 := Real.rpow_le_one (by positivity) (by linarith) hd
  have hh := grid_le_of_ball_mass μ hs hq hB hu E hη hball
  have hq3 : 1 ≤ 3/(s/4)^d := (le_div_iff₀ hq).mpr (by linarith)
  rw [max_eq_right hq3] at hh
  have hnum : 0 < 2*B+3 := by linarith
  have hcard := grid_support_card_le hB0 hs hs1
  have hbase : 1 ≤ (2*B+3)/s := (le_div_iff₀ hs).mpr (by linarith)
  have hlog : Real.log (max 1 ((Finset.Icc ⌊-B/s⌋ ⌊B/s+1⌋).card : ℝ)) ≤
      Real.log ((2*B+3)/s) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (max_le hbase hcard)
  have hm := mul_le_mul_of_nonneg_left hlog hη0
  have he : Real.log 2+Real.log (3/(s/4)^d)+η*Real.log ((2*B+3)/s) =
      Real.log 6+d*Real.log 4+η*Real.log (2*B+3)+(d+η)*Real.log (1/s) := by
    rw [Real.log_div (by norm_num) hq.ne',Real.log_rpow (by positivity),
      Real.log_div hs.ne' (by norm_num),Real.log_div hnum.ne' hs.ne',
      Real.log_div (by norm_num) hs.ne',Real.log_one]
    have h6 : Real.log (6 : ℝ)=Real.log 2+Real.log 3 := by
      rw [show (6 : ℝ)=2*3 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
    rw [h6]
    ring
  rw [← he]
  linarith

theorem entropy_bound_of_radial_limit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : CompactlyCarried μ) {d D : ℝ} (hd : 0 ≤ d) (hD : d < D)
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto
      (fun r => -Real.log (μ.real (Metric.closedBall x r)) / -Real.log r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds d)) :
    ∃ C : ℝ, ∀ s : ℝ, 0 < s → s < 1 → averaged μ s ≤ D*Real.log (1/s)+C := by
  let e := (d+D)/2
  let η := (D-d)/4
  have hde : d < e := by dsimp [e]; linarith
  have he : 0 ≤ e := le_trans hd hde.le
  have hη : 0 < η := by dsimp [η]; linarith
  have heη : e+η ≤ D := by dsimp [e,η]; linarith
  have hD0 : 0 ≤ D := hd.trans hD.le
  obtain ⟨E,hE,hEc,R,hR,hball⟩ := LocalMass.large_uniform_mass_set μ he hη (by
    filter_upwards [hlim,μ.support_mem_ae] with x hx hs
    exact LocalMass.eventual_lower_of_limit μ hs hde hx)
  obtain ⟨B,hB0,hB⟩ := hc
  let C₀ := Real.log 6+e*Real.log 4+η*Real.log (2*B+3)
  let C := max C₀ ((2*B+3)/R)
  refine ⟨C,?_⟩
  intro s hs hs1
  have hlog : 0 ≤ Real.log (1/s) := Real.log_nonneg ((one_le_div hs).mpr hs1.le)
  have hgrid : ∀ u ∈ Set.Icc (0 : ℝ) 1, grid μ s u ≤ D*Real.log (1/s)+C := by
    intro u hu
    by_cases hsR : s < R
    · have hh := grid_le_of_quarter_power_ball_mass μ hB0 hs hs1.le he hη.le hB hu E hEc
        (fun x hx => by
          have hr := hball x hx (s/2) (by positivity) (by linarith)
          simpa only [show s/2/2=s/4 by ring] using hr)
      have hm := mul_le_mul_of_nonneg_right heη hlog
      have hC : C₀ ≤ C := le_max_left _ _
      dsimp only [C₀] at hC
      linarith
    · have hRs : R ≤ s := le_of_not_gt hsR
      have hh := (grid_le_card μ hs hB hu).trans (grid_support_card_le hB0 hs hs1.le)
      have hdiv : (2*B+3)/s ≤ (2*B+3)/R :=
        div_le_div_of_nonneg_left (by linarith) hR hRs
      have hC : (2*B+3)/R ≤ C := le_max_right _ _
      have hm := mul_nonneg hD0 hlog
      linarith
  have hh := integral_mono_ae (grid_integrable μ ⟨B,hB0,hB⟩ hs)
    (integrable_const (D*Real.log (1/s)+C)) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      exact hgrid u hu)
  simpa [averaged,integral_const,Measure.real_def] using hh

end EntropyRateDimension.MeasureEntropy

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.Bernoulli ----
namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology

namespace EntropyRateDimension
namespace Bernoulli

variable {α : Type uα} [MeasurableSpace α]

theorem shift_measurable : Measurable (shift (α := α)) :=
  measurable_pi_iff.mpr fun n => measurable_pi_apply (n+1)

omit [MeasurableSpace α] in
theorem shift_iterate (n : ℕ) (ω : ℕ → α) (k : ℕ) :
    shift^[n] ω k = ω (k+n) := by
  induction n generalizing k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', shift, ih]
    congr 1
    omega

theorem shift_preserving (p : Measure α) [IsProbabilityMeasure p] :
    MeasurePreserving shift (Measure.infinitePi (fun _ : ℕ => p))
      (Measure.infinitePi (fun _ : ℕ => p)) where
  measurable := shift_measurable
  map_eq := by
    have hi : iIndepFun (fun n : ℕ => (@Function.eval ℕ (fun _ => α) n))
        (Measure.infinitePi fun _ : ℕ => p) :=
      iIndepFun_infinitePi (fun _ : ℕ => measurable_id)
    have hh := (hi.precomp Nat.succ_injective).map_fun_eq_infinitePi_map
      (fun n => measurable_pi_apply (n+1))
    change Measure.map (fun ω : ℕ → α => fun n => ω (n+1))
      (Measure.infinitePi fun _ : ℕ => p) = _
    simpa only [Measure.infinitePi_map_eval, Function.eval] using hh

theorem head_indep_tail (p : Measure α) [IsProbabilityMeasure p] :
    IndepFun (fun ω : ℕ → α => ω 0) shift (Measure.infinitePi fun _ : ℕ => p) := by
  let m : ℕ → MeasurableSpace (ℕ → α) := fun n =>
    MeasurableSpace.comap (fun ω : ℕ → α => ω n) inferInstance
  have hi : iIndep m (Measure.infinitePi fun _ : ℕ => p) :=
    iIndepFun_infinitePi (fun _ : ℕ => measurable_id)
  have h := indep_iSup_of_disjoint (fun n => (measurable_pi_apply n).comap_le) hi
    (S := {0}) (T := Set.range Nat.succ) (by
      apply Set.disjoint_left.mpr
      rintro n (hn : n = 0) ⟨k,hk⟩
      omega)
  apply indep_of_indep_of_le h
  · exact le_iSup_of_le 0 (le_iSup_of_le rfl le_rfl)
  · change MeasurableSpace.comap shift
      (⨆ k : ℕ, MeasurableSpace.comap (Function.eval k) (inferInstance : MeasurableSpace α)) ≤ _
    rw [MeasurableSpace.comap_iSup]
    apply iSup_le
    intro k
    rw [MeasurableSpace.comap_comp]
    exact le_iSup_of_le (k+1) (le_iSup_of_le ⟨k,rfl⟩ le_rfl)

theorem head_tail_law (p : Measure α) [IsProbabilityMeasure p] :
    (Measure.infinitePi fun _ : ℕ => p).map (fun ω => (ω 0,shift ω)) =
      p.prod (Measure.infinitePi fun _ : ℕ => p) := by
  rw [(head_indep_tail p).map_prod_eq_prod_map_map
    (measurable_pi_apply 0).aemeasurable shift_measurable.aemeasurable,
    Measure.infinitePi_map_eval, (shift_preserving p).map_eq]

theorem invariant_tail_measurable {s : Set (ℕ → α)} (hs : MeasurableSet s)
    (hinv : shift ⁻¹' s = s) :
    MeasurableSet[Filter.limsup (fun n : ℕ =>
      MeasurableSpace.comap (Function.eval n) (inferInstance : MeasurableSpace α)) atTop] s := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat']
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro n
  have hm : @Measurable (ℕ → α) (ℕ → α)
      (⨆ i : ℕ, MeasurableSpace.comap (fun ω : ℕ → α => ω (i+n)) (inferInstance : MeasurableSpace α))
      inferInstance (fun ω k => ω (k+n)) := by
    apply Measurable.of_comap_le
    change MeasurableSpace.comap (fun ω : ℕ → α => fun k => ω (k+n))
      (⨆ k : ℕ, MeasurableSpace.comap (Function.eval k) (inferInstance : MeasurableSpace α)) ≤ _
    rw [MeasurableSpace.comap_iSup]
    apply iSup_le
    intro k
    rw [MeasurableSpace.comap_comp]
    exact le_iSup (fun i : ℕ => MeasurableSpace.comap (fun ω : ℕ → α => ω (i+n))
      (inferInstance : MeasurableSpace α)) k
  have he : (fun ω : ℕ → α => fun k => ω (k+n)) = shift^[n] := by
    funext ω k
    exact (shift_iterate n ω k).symm
  rw [he] at hm
  have hi : (shift^[n]) ⁻¹' s = s := Function.IsFixedPt.preimage_iterate hinv n
  rw [← hi]
  exact hm hs

theorem shift_ergodic (p : Measure α) [IsProbabilityMeasure p] :
    Ergodic shift (Measure.infinitePi (fun _ : ℕ => p)) where
  toMeasurePreserving := shift_preserving p
  aeconst_set := by
    intro s hs hi
    have hind : iIndepFun (fun n : ℕ => (@Function.eval ℕ (fun _ => α) n))
        (Measure.infinitePi fun _ : ℕ => p) :=
      iIndepFun_infinitePi (fun _ : ℕ => measurable_id)
    have hz := measure_zero_or_one_of_measurableSet_limsup_atTop
      (fun n => (measurable_pi_apply n).comap_le) hind
      (invariant_tail_measurable hs hi)
    apply Filter.eventuallyConst_set.mpr
    rcases hz with h0 | h1
    · right
      exact measure_eq_zero_iff_ae_notMem.mp h0
    · left
      have hc : (Measure.infinitePi fun _ : ℕ => p) sᶜ = 0 := by
        rw [measure_compl hs (measure_ne_top _ _), h1]
        simp
      simpa only [mem_compl_iff, not_not] using measure_eq_zero_iff_ae_notMem.mp hc

end Bernoulli
end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.Coding ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
namespace EntropyRateDimension
namespace Coding
open Filter Set
open scoped Topology

variable {ι : Type uι} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem slope_shift (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    slope S ω (n+1) = S.ratio (ω 0) * slope S (shift ω) n := by
  simp only [slope, Finset.prod_range_succ', shift]
  ring

theorem point_shift (S : System ι) (ω : ℕ → ι) :
    point S ω = S.affine (ω 0) (point S (shift ω)) := by
  rw [point, (term_summable S ω).tsum_eq_zero_add]
  have he : (fun n => term S ω (n+1)) = fun n => S.ratio (ω 0)*term S (shift ω) n := by
    funext n
    simp only [term, slope_shift, shift]
    ring
  rw [he, tsum_mul_left]
  simp only [term, slope_zero, one_mul, System.affine, point]
  ring

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem head_tail_point_law (S : System ι) :
    (addressMeasure S).map (fun ω => (ω 0,point S (shift ω))) =
      (symbolMeasure S).prod (law S) := by
  have h := congrArg (Measure.map (Prod.map id (point S)))
    (Bernoulli.head_tail_law (symbolMeasure S))
  rw [Measure.map_map (measurable_id.prodMap (point_measurable S))
      ((measurable_pi_apply 0).prodMk Bernoulli.shift_measurable)] at h
  rw [← Measure.map_prod_map _ _ measurable_id (point_measurable S), Measure.map_id] at h
  exact h

theorem law_selfSimilar (S : System ι) : S.SelfSimilar (law S) := by
  classical
  let f : ι × ℝ → ℝ := fun z => S.affine z.1 z.2
  have hf : Measurable f := by
    exact ((measurable_of_finite S.ratio).comp measurable_fst).mul measurable_snd |>.add
      ((measurable_of_finite S.offset).comp measurable_fst)
  have hh := congrArg (Measure.map f) (head_tail_point_law S)
  have hp : Measurable (fun ω : ℕ → ι => (ω 0,point S (shift ω))) :=
    (measurable_pi_apply 0).prodMk ((point_measurable S).comp Bernoulli.shift_measurable)
  rw [Measure.map_map hf hp] at hh
  have he : f ∘ (fun ω => (ω 0,point S (shift ω))) = point S :=
    funext fun ω => (point_shift S ω).symm
  rw [he] at hh
  change law S = _ at hh
  change law S = _
  conv_lhs => rw [hh]
  change ((∑ i, ENNReal.ofReal (S.weight i) • Measure.dirac i).prod (law S)).map f = _
  rw [← Measure.sum_fintype, Measure.prod_sum_left, Measure.sum_fintype,
    Measure.map_finset_sum hf.aemeasurable]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Measure.prod_smul_left, Measure.map_smul _ _ f, Measure.dirac_prod,
    Measure.map_map hf measurable_prodMk_left]
  rfl

end Coding
end EntropyRateDimension

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.InvariantLaw ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
namespace EntropyRateDimension.System
open MeasureTheory Filter Set
open scoped Topology BigOperators
variable {ι : Type uι} [Fintype ι]

theorem average_continuous (S : System ι) {f : ℝ → ℝ} (hf : Continuous f) (n : ℕ) :
    Continuous (S.average f n) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    exact continuous_finsetSum _ fun i _ => continuous_const.mul (ih.comp (S.affine_continuous i))

theorem average_bound (S : System ι) {f : ℝ → ℝ} {C : ℝ}
    (hf : ∀ x, |f x| ≤ C) (n : ℕ) (x : ℝ) : |S.average f n x| ≤ C := by
  induction n generalizing x with
  | zero => exact hf x
  | succ n ih =>
    calc
      _ ≤ ∑ i, |S.weight i * S.average f n (S.affine i x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, S.weight i * C := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul,abs_of_nonneg (S.weight_nonneg i)]
        exact mul_le_mul_of_nonneg_left (ih _) (S.weight_nonneg i)
      _ = C := by rw [← Finset.sum_mul,S.weight_sum,one_mul]

theorem average_integrable (S : System ι) {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hb : ∀ x, |f x| ≤ C) (n : ℕ) (μ : Measure ℝ)
    [IsFiniteMeasure μ] : Integrable (S.average f n) μ := by
  apply Integrable.of_bound (S.average_continuous hf n).aestronglyMeasurable C
  exact ae_of_all μ fun x => by simpa only [Real.norm_eq_abs] using S.average_bound hb n x

theorem selfSimilar_integral (S : System ι) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : S.SelfSimilar μ) {f : ℝ → ℝ} {C : ℝ} (hf : Continuous f) (hb : ∀ x, |f x| ≤ C) :
    (∫ x, f x ∂μ) = ∑ i, S.weight i * ∫ x, f (S.affine i x) ∂μ := by
  have hi : ∀ i, Integrable f (μ.map (S.affine i)) := fun i =>
    Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs] using hb x)
  conv_lhs => rw [hμ]
  rw [integral_finsetSum_measure (fun i _ => (hi i).smul_measure (by simp))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure,integral_map (S.affine_continuous i).measurable.aemeasurable
    hf.aestronglyMeasurable,ENNReal.toReal_ofReal (S.weight_nonneg i)]
  rfl

theorem integral_average (S : System ι) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : S.SelfSimilar μ) {f : ℝ → ℝ} {C : ℝ} (hf : Continuous f) (hb : ∀ x, |f x| ≤ C)
    (n : ℕ) : (∫ x, S.average f n x ∂μ) = ∫ x, f x ∂μ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (∫ x, ∑ i, S.weight i * S.average f n (S.affine i x) ∂μ) = _
    rw [integral_finsetSum]
    · simp only [integral_const_mul]
      rw [← S.selfSimilar_integral μ hμ (S.average_continuous hf n) (S.average_bound hb n),ih]
    · intro i _
      apply Integrable.const_mul
      apply Integrable.of_bound ((S.average_continuous hf n).comp
        (S.affine_continuous i)).aestronglyMeasurable C
      exact ae_of_all μ fun x => by
        simpa only [Real.norm_eq_abs,Function.comp_def] using S.average_bound hb n (S.affine i x)

theorem average_difference (S : System ι) {f : ℝ → ℝ} {c ε δ : ℝ}
    (hc : 0 ≤ c) (hr : ∀ i, |S.ratio i| ≤ c)
    (hf : ∀ x y, |x-y| < δ → |f x-f y| ≤ ε) (n : ℕ) {x y : ℝ}
    (hxy : |x-y| *c^n < δ) : |S.average f n x-S.average f n y| ≤ ε := by
  induction n generalizing x y with
  | zero => simpa only [average,pow_zero,mul_one] using hf x y (by simpa using hxy)
  | succ n ih =>
    simp only [average,← Finset.sum_sub_distrib,← mul_sub]
    calc
      _ ≤ ∑ i, |S.weight i * (S.average f n (S.affine i x)-S.average f n (S.affine i y))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, S.weight i * ε := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul,abs_of_nonneg (S.weight_nonneg i)]
        apply mul_le_mul_of_nonneg_left _ (S.weight_nonneg i)
        apply ih
        have he : S.affine i x-S.affine i y = S.ratio i*(x-y) := by simp only [affine]; ring
        rw [he,abs_mul]
        calc
          _ ≤ (c*|x-y|)*c^n := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hr i) (abs_nonneg _)) (pow_nonneg hc n)
          _ = |x-y| *c^(n+1) := by rw [pow_succ]; ring
          _ < δ := hxy
      _ = ε := by rw [← Finset.sum_mul,S.weight_sum,one_mul]

variable [Nonempty ι]

theorem tendsto_average_at_zero (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) {f : ℝ → ℝ} {C : ℝ}
    (hf : UniformContinuous f) (hb : ∀ x, |f x| ≤ C) :
    Tendsto (fun n => S.average f n 0) atTop (𝓝 (∫ x, f x ∂μ)) := by
  obtain ⟨c,T,hc,hc1,_,hr,_⟩ := S.exists_uniform_bounds
  obtain ⟨B,hB,hBc⟩ := S.selfSimilar_compact μ hμ
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp hf (ε/2) (by linarith)
  have hlim : Tendsto (fun n : ℕ => B*c^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc1).const_mul B
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp hlim).2 δ hδ)
  refine ⟨N,fun n hn => ?_⟩
  have hai := S.average_integrable hf.continuous hb n μ
  have he : (∫ x, (S.average f n x-S.average f n 0) ∂μ) =
      (∫ x, f x ∂μ) - S.average f n 0 := by
    rw [integral_sub hai (integrable_const _),S.integral_average μ hμ hf.continuous hb]
    simp
  have hbound : ∀ᵐ x ∂μ, ‖S.average f n x-S.average f n 0‖ ≤ ε/2 := by
    filter_upwards [show ∀ᵐ x ∂μ, x ∈ Icc (-B) B from ae_iff.mpr hBc] with x hx
    rw [Real.norm_eq_abs]
    apply S.average_difference hc.le hr (fun x y h => (hd (by simpa [Real.dist_eq] using h)).le)
    calc
      |x-0| *c^n ≤ B*c^n := mul_le_mul_of_nonneg_right (by simpa using abs_le.mpr hx)
        (pow_nonneg hc.le n)
      _ < δ := hN n hn
  have hnorm := norm_integral_le_of_norm_le_const hbound
  rw [he] at hnorm
  have hh : |(∫ x, f x ∂μ)-S.average f n 0| ≤ ε/2 := by simpa using hnorm
  rw [Real.dist_eq,abs_sub_comm]
  linarith

theorem selfSimilar_unique (S : System ι) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : S.SelfSimilar μ) (hν : S.SelfSimilar ν) : μ = ν := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  have hf := f.hasCompactSupport.uniformContinuous_of_continuous f.continuous
  have hb : ∀ x, |f x| ≤ ‖f.toBoundedContinuousFunction‖ := fun x => by
    have hh := f.toBoundedContinuousFunction.norm_coe_le_norm x
    have he : f.toBoundedContinuousFunction x = f x := rfl
    rw [he,Real.norm_eq_abs] at hh
    exact hh
  exact tendsto_nhds_unique (S.tendsto_average_at_zero μ hμ hf hb)
    (S.tendsto_average_at_zero ν hν hf hb)

end EntropyRateDimension.System

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.BallRatios ----
namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace EntropyRateDimension
namespace BallRatios

theorem exists_small_ratio_bound : ∃ N : ℕ, ∀ (μ ν : Measure ℝ) (t : ℝ≥0∞)
    (E : Set ℝ),
    (∀ x ∈ E, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ν (closedBall x r) ≤ t*μ (closedBall x r)) →
    ν E ≤ N*t*μ univ := by
  classical
  obtain ⟨N,τ,hτ,hN⟩ := HasBesicovitchCovering.no_satelliteConfig (α := ℝ)
  refine ⟨N, ?_⟩
  intro μ ν t E hE
  choose r hr hr1 hrat using fun x : E => hE x.val x.property
  let q : Besicovitch.BallPackage E ℝ :=
    { c := Subtype.val, r := r, rpos := hr, r_bound := 1, r_le := hr1 }
  obtain ⟨s,hd,hcover⟩ := Besicovitch.exist_disjoint_covering_families hτ hN q
  have hcnt : ∀ i, (s i).Countable := by
    intro i
    apply (hd i).countable_of_nonempty_interior
    intro x hx
    exact ⟨x.val, ball_subset_interior_closedBall (mem_ball_self (hr x))⟩
  have hb : ∀ i, ν (⋃ x ∈ s i, ball (q.c x) (q.r x)) ≤ t*μ univ := by
    intro i
    calc
      _ ≤ ∑' x : s i, ν (closedBall (q.c x.val) (q.r x.val)) := by
        apply le_trans (measure_biUnion_le ν (hcnt i) _)
        exact ENNReal.tsum_le_tsum fun x => measure_mono ball_subset_closedBall
      _ ≤ ∑' x : s i, t*μ (closedBall (q.c x.val) (q.r x.val)) :=
        ENNReal.tsum_le_tsum fun x => hrat x.val
      _ = t * μ (⋃ x ∈ s i, closedBall (q.c x) (q.r x)) := by
        rw [ENNReal.tsum_mul_left, measure_biUnion (hcnt i) (hd i)
          (fun _ _ => measurableSet_closedBall)]
      _ ≤ t*μ univ := mul_le_mul' le_rfl (measure_mono (subset_univ _))
  calc
    ν E ≤ ν (⋃ i, ⋃ x ∈ s i, ball (q.c x) (q.r x)) := by
      apply measure_mono
      intro x hx
      exact hcover ⟨⟨x,hx⟩,rfl⟩
    _ ≤ ∑ i : Fin N, ν (⋃ x ∈ s i, ball (q.c x) (q.r x)) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin N, t*μ univ := Finset.sum_le_sum fun i _ => hb i
    _ = N*t*μ univ := by simp [mul_assoc]

theorem measurable_ball_mass (μ : Measure ℝ) [SFinite μ] (r : ℝ) :
    Measurable (fun x : ℝ => μ (closedBall x r)) := by
  have hs : MeasurableSet {p : ℝ × ℝ | dist p.2 p.1 ≤ r} :=
    measurableSet_le (measurable_snd.dist measurable_fst) measurable_const
  exact measurable_measure_prodMk_left hs

theorem maximal_measurable (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    Measurable (maximal μ ν) := by
  apply Measurable.iSup
  intro q
  exact (measurable_ball_mass μ _).div (measurable_ball_mass ν _)

theorem maximal_tail {N : ℕ}
    (hN : ∀ (μ ν : Measure ℝ) (t : ℝ≥0∞) (E : Set ℝ),
      (∀ x ∈ E, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ν (closedBall x r) ≤ t*μ (closedBall x r)) →
      ν E ≤ N*t*μ univ)
    (μ ν : Measure ℝ) [IsFiniteMeasure ν] (a : ℝ≥0∞) (ha : a ≠ 0) (hat : a ≠ ⊤) :
    ν {x | a < maximal μ ν x} ≤ N * a⁻¹ * μ univ := by
  apply hN
  intro x hx
  obtain ⟨q,hq⟩ : ∃ q : Radius, a < μ (closedBall x (q.val : ℝ)) /
      ν (closedBall x (q.val : ℝ)) := by
    simpa only [Set.mem_ofPred_eq, maximal, lt_iSup_iff] using hx
  refine ⟨q.val,q.property.1,q.property.2,?_⟩
  have hh := (ENNReal.lt_div_iff_mul_lt (Or.inr hat)
    (Or.inl (measure_ne_top ν _))).mp hq
  have := (ENNReal.le_div_iff_mul_le (Or.inl ha) (Or.inl hat)).mpr
    (show ν (closedBall x (q.val : ℝ)) * a ≤ μ (closedBall x (q.val : ℝ)) by
      simpa only [mul_comm] using hh.le)
  simpa only [div_eq_mul_inv,mul_comm] using this

theorem maximal_finite_ae (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∀ᵐ x ∂ν, maximal μ ν x ≠ ⊤ := by
  obtain ⟨N,hN⟩ := exists_small_ratio_bound
  apply ae_iff.mpr
  simp only [not_not]
  apply le_antisymm _ bot_le
  have hlim : Tendsto (fun n : ℕ => (N : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ * μ univ)
      atTop (𝓝 0) := by
    have hh := ENNReal.Tendsto.const_mul ENNReal.tendsto_nat_nhds_top.inv
      (Or.inr (show (N : ℝ≥0∞) ≠ ⊤ by simp))
    have hf := ENNReal.Tendsto.mul_const hh (Or.inr (measure_ne_top μ univ))
    simpa using hf
  apply ge_of_tendsto hlim
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  calc
    ν {x | maximal μ ν x = ⊤} ≤ ν {x | (n : ℝ≥0∞) < maximal μ ν x} := by
      apply measure_mono
      intro x (hx : maximal μ ν x = ⊤)
      change (n : ℝ≥0∞) < maximal μ ν x
      rw [hx]
      exact ENNReal.natCast_lt_top n
    _ ≤ _ := maximal_tail hN μ ν n (by exact_mod_cast hn.ne') (by simp)

theorem logEnvelope_nonneg (μ ν : Measure ℝ) (x : ℝ) : 0 ≤ logEnvelope μ ν x :=
  le_max_left _ _

theorem logEnvelope_measurable (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    Measurable (logEnvelope μ ν) :=
  measurable_const.max (maximal_measurable μ ν).ennreal_toReal.log

theorem logEnvelope_tail {N : ℕ}
    (hN : ∀ (μ ν : Measure ℝ) (t : ℝ≥0∞) (E : Set ℝ),
      (∀ x ∈ E, ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ν (closedBall x r) ≤ t*μ (closedBall x r)) →
      ν E ≤ N*t*μ univ)
    (μ ν : Measure ℝ) [IsFiniteMeasure ν] {t : ℝ} (ht : 0 ≤ t) :
    ν {x | t < logEnvelope μ ν x} ≤
      (N : ℝ≥0∞)*μ univ*ENNReal.ofReal (Real.exp (-t)) := by
  calc
    _ ≤ ν {x | ENNReal.ofReal (Real.exp t) < maximal μ ν x} := by
      apply measure_mono
      intro x hx
      have hh : t < Real.log (maximal μ ν x).toReal :=
        (lt_max_iff.mp hx).resolve_left (not_lt_of_ge ht)
      have hp : 0 < (maximal μ ν x).toReal := by
        apply lt_of_le_of_ne ENNReal.toReal_nonneg
        intro he
        simp [← he] at hh
        linarith
      have he := (Real.lt_log_iff_exp_lt hp).mp hh
      exact ((ENNReal.ofReal_lt_ofReal_iff hp).mpr he).trans_le ENNReal.ofReal_toReal_le
    _ ≤ (N : ℝ≥0∞)*(ENNReal.ofReal (Real.exp t))⁻¹*μ univ :=
      maximal_tail hN μ ν _ (by simp [Real.exp_pos]) (by simp)
    _ = _ := by rw [Real.exp_neg, ENNReal.ofReal_inv_of_pos (Real.exp_pos t)]; ring

theorem logEnvelope_integrable (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (logEnvelope μ ν) ν := by
  obtain ⟨N,hN⟩ := exists_small_ratio_bound
  refine ⟨(logEnvelope_measurable μ ν).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (logEnvelope_nonneg μ ν)),
    lintegral_eq_lintegral_meas_lt ν (Eventually.of_forall (logEnvelope_nonneg μ ν))
      (logEnvelope_measurable μ ν).aemeasurable]
  calc
    _ ≤ ∫⁻ t : ℝ in Ioi 0, (N : ℝ≥0∞)*μ univ*ENNReal.ofReal (Real.exp (-t)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact logEnvelope_tail hN μ ν ht.le
    _ = (N : ℝ≥0∞)*μ univ*∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (Real.exp (-t)) :=
      lintegral_const_mul _ (by fun_prop)
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) (measure_lt_top μ _))
      ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall
        (fun t : ℝ => (Real.exp_pos (-t)).le))).mp
          (integrableOn_exp_neg_Ioi 0).hasFiniteIntegral)

theorem tendsto_ball_mass_right (μ : Measure ℝ) [IsFiniteMeasure μ] (x r : ℝ) :
    Tendsto (fun t => μ (closedBall x t)) (𝓝[>] r) (𝓝 (μ (closedBall x r))) := by
  have h := tendsto_measure_biInter_gt (μ := μ) (a := r)
    (s := fun t : ℝ => closedBall x t)
    (fun _ _ => measurableSet_closedBall.nullMeasurableSet)
    (fun _ _ _ h => closedBall_subset_closedBall h)
    ⟨r+1,by linarith,measure_ne_top μ _⟩
  simpa only [biInter_gt_closedBall,Function.comp_def] using h

theorem ratio_le_maximal (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (x : ℝ) (hx : x ∈ ν.support) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    μ (closedBall x r) / ν (closedBall x r) ≤ maximal μ ν x := by
  obtain ⟨q,_hq,hqr,hql⟩ := (Rat.denseRange_cast (𝕜 := ℝ)).exists_seq_strictAnti_tendsto_of_lt
    Rat.cast_strictMono.monotone hr1
  have ht : Tendsto (fun n => (q n : ℝ)) atTop (𝓝[>] r) :=
    tendsto_nhdsWithin_iff.mpr ⟨hql,Eventually.of_forall fun n => (hqr n).1⟩
  have hp : ν (closedBall x r) ≠ 0 :=
    ne_of_gt ((Measure.mem_support_iff_forall x).mp hx _ (closedBall_mem_nhds x hr))
  have hlim := ENNReal.Tendsto.div ((tendsto_ball_mass_right μ x r).comp ht)
    (Or.inr hp) ((tendsto_ball_mass_right ν x r).comp ht) (Or.inl (measure_ne_top ν _))
  apply le_of_tendsto hlim
  exact Eventually.of_forall fun n =>
    le_iSup (fun q : Radius => μ (closedBall x (q.val : ℝ)) / ν (closedBall x (q.val : ℝ)))
      ⟨q n,lt_trans hr (hqr n).1,(hqr n).2.le⟩

theorem logRatio_measurable (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    Measurable (fun p : ℝ × ℝ => logRatio μ ν p.1 p.2) := by
  have hm (κ : Measure ℝ) [SFinite κ] :
      Measurable (fun p : ℝ × ℝ => κ (closedBall p.1 p.2)) := by
    have hs : MeasurableSet {z : (ℝ × ℝ) × ℝ | dist z.2 z.1.1 ≤ z.1.2} :=
      measurableSet_le (measurable_snd.dist (measurable_fst.fst)) (measurable_fst.snd)
    exact measurable_measure_prodMk_left hs
  exact ((hm μ).div (hm ν)).ennreal_toReal.log

theorem logRatio_bounds (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν ≤ μ) : ∀ᵐ x ∂ν, ∀ r : ℝ, 0 < r → r < 1 →
      0 ≤ logRatio μ ν x r ∧ logRatio μ ν x r ≤ logEnvelope μ ν x := by
  filter_upwards [ν.support_mem_ae,maximal_finite_ae μ ν] with x hx hmax
  intro r hr hr1
  have hp := (Measure.mem_support_iff_forall x).mp hx _ (closedBall_mem_nhds x hr)
  have hge : 1 ≤ μ (closedBall x r) / ν (closedBall x r) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hp.ne') (Or.inl (measure_ne_top ν _))).mpr
    simpa only [one_mul] using hν (closedBall x r)
  have htop := ne_top_of_le_ne_top hmax (ratio_le_maximal μ ν x hx hr hr1)
  have hreal : 1 ≤ (μ (closedBall x r) / ν (closedBall x r)).toReal := by
    exact_mod_cast (ENNReal.toReal_mono htop hge)
  refine ⟨Real.log_nonneg hreal,?_⟩
  apply le_trans _ (le_max_right 0 _)
  apply Real.log_le_log (lt_of_lt_of_le zero_lt_one hreal)
  exact ENNReal.toReal_mono hmax (ratio_le_maximal μ ν x hx hr hr1)

theorem ae_logRatio_limit (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ν ≤ μ) : ∀ᵐ x ∂ν,
      1 ≤ (μ.rnDeriv ν x).toReal ∧
      Tendsto (logRatio μ ν x) (𝓝[>] 0) (𝓝 (Real.log (μ.rnDeriv ν x).toReal)) := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv μ ν, μ.rnDeriv_ne_top ν,
    ν.support_mem_ae] with x hlim htop hx
  have hge : 1 ≤ μ.rnDeriv ν x := by
    apply ge_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    have hp := (Measure.mem_support_iff_forall x).mp hx _ (closedBall_mem_nhds x hr)
    apply (ENNReal.le_div_iff_mul_le (Or.inl hp.ne') (Or.inl (measure_ne_top ν _))).mpr
    simpa only [one_mul] using hν (closedBall x r)
  have hreal : 1 ≤ (μ.rnDeriv ν x).toReal := by
    simpa using ENNReal.toReal_mono htop hge
  refine ⟨hreal,?_⟩
  exact (Real.continuousAt_log (ne_of_gt (lt_of_lt_of_le zero_lt_one hreal))).tendsto.comp
    ((ENNReal.continuousAt_toReal htop).tendsto.comp hlim)

end BallRatios
end EntropyRateDimension

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.BallIntegrability ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace EntropyRateDimension
open MeasureTheory Metric Set Filter
open scoped Topology BigOperators
namespace System
variable {ι : Type uι} [Fintype ι]

theorem component_le (S : System ι) (μ : Measure ℝ) (hμ : S.SelfSimilar μ) (i : ι) :
    S.component μ i ≤ μ := by
  calc
    S.component μ i ≤ ∑ j, S.component μ j :=
      Finset.single_le_sum (fun j _ => Measure.zero_le _) (Finset.mem_univ i)
    _ = μ := hμ.symm

theorem affine_preimage_closedBall (S : System ι) (i : ι) (x r : ℝ) :
    S.affine i ⁻¹' closedBall (S.affine i x) (|S.ratio i| *r) = closedBall x r := by
  ext y
  simp only [mem_preimage,mem_closedBall,Real.dist_eq]
  have he : S.affine i y-S.affine i x = S.ratio i*(y-x) := by simp only [affine]; ring
  rw [he,abs_mul]
  exact mul_le_mul_iff_right₀ (S.ratio_pos i)

theorem component_ball (S : System ι) (μ : Measure ℝ) (i : ι) (x r : ℝ) :
    S.component μ i (closedBall (S.affine i x) (|S.ratio i| *r)) =
      ENNReal.ofReal (S.weight i) * μ (closedBall x r) := by
  rw [component,Measure.smul_apply,smul_eq_mul,Measure.map_apply
    (S.affine_continuous i).measurable isClosed_closedBall.measurableSet,
    S.affine_preimage_closedBall]

end System

namespace BallRatios
theorem massReal_pos (μ : Measure ℝ) [IsFiniteMeasure μ] {x r : ℝ}
    (hx : x ∈ μ.support) (hr : 0 < r) : 0 < μ.real (closedBall x r) := by
  exact ENNReal.toReal_pos (ne_of_gt ((Measure.mem_support_iff_forall x).mp hx _
    (closedBall_mem_nhds x hr))) (measure_ne_top μ _)

theorem information_component {ι : Type uι} [Fintype ι] (S : System ι)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : S.SelfSimilar μ) (i : ι)
    {x r : ℝ} (hx : x ∈ μ.support) (hr : 0 < r) :
    information μ (S.affine i x) (|S.ratio i| *r) =
      information μ x r - Real.log (S.weight i) -
        logRatio μ (S.component μ i) (S.affine i x) (|S.ratio i| *r) := by
  have hbase := massReal_pos μ hx hr
  have hcomp : (S.component μ i).real (closedBall (S.affine i x) (|S.ratio i| *r)) =
      S.weight i * μ.real (closedBall x r) := by
    simp only [Measure.real,S.component_ball,ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (S.weight_nonneg i)]
  have hcp : 0 < (S.component μ i).real (closedBall (S.affine i x) (|S.ratio i| *r)) := by
    rw [hcomp]; exact mul_pos (S.weight_pos i) hbase
  have htop : 0 < μ.real (closedBall (S.affine i x) (|S.ratio i| *r)) := by
    exact hcp.trans_le (ENNReal.toReal_mono (measure_ne_top μ _)
      (S.component_le μ hμ i _))
  have hl : logRatio μ (S.component μ i) (S.affine i x) (|S.ratio i| *r) =
      Real.log (μ.real (closedBall (S.affine i x) (|S.ratio i| *r))) -
        Real.log (S.weight i) - Real.log (μ.real (closedBall x r)) := by
    unfold logRatio
    rw [ENNReal.toReal_div]
    change Real.log (μ.real _ / (S.component μ i).real _) = _
    rw [Real.log_div htop.ne' hcp.ne']
    rw [hcomp,Real.log_mul (S.weight_pos i).ne' hbase.ne']
    ring
  rw [hl]
  unfold information
  ring
end BallRatios

namespace Coding
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem slope_ne_zero (S : System ι) (ω : ℕ → ι) (n : ℕ) : slope S ω n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact abs_pos.mp (S.ratio_pos (ω j))

omit [Nonempty ι] in
theorem abs_slope_pos (S : System ι) (ω : ℕ → ι) (n : ℕ) : 0 < |slope S ω n| :=
  abs_pos.mpr (slope_ne_zero S ω n)

theorem abs_slope_lt_one (S : System ι) (ω : ℕ → ι) {n : ℕ} (hn : 0 < n) :
    |slope S ω n| < 1 := by
  obtain ⟨c,T,hc,hc1,_,hr,_⟩ := S.exists_uniform_bounds
  exact (abs_slope_le S ω hc.le hr n).trans_lt (pow_lt_one₀ hc.le hc1 hn.ne')

theorem slope_tendsto_zero (S : System ι) (ω : ℕ → ι) :
    Tendsto (fun n => |slope S ω n|) atTop (𝓝 0) := by
  obtain ⟨c,T,hc,hc1,_,hr,_⟩ := S.exists_uniform_bounds
  exact squeeze_zero (fun n => abs_nonneg _) (abs_slope_le S ω hc.le hr)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc.le hc1)

end Coding
end EntropyRateDimension

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.CodingIntegrals ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter EntropyRateDimension.Bernoulli
open scoped Topology BigOperators ENNReal
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI
theorem head_point_measurable (S : System ι) :
    Measurable (fun ω : ℕ → ι => (ω 0,point S ω)) :=
  (measurable_pi_apply 0).prodMk (point_measurable S)

theorem head_point_law (S : System ι) :
    (addressMeasure S).map (fun ω => (ω 0,point S ω)) =
      ∑ i, (Measure.dirac i).prod (S.component (law S) i) := by
  classical
  let f : ι × ℝ → ι × ℝ := fun z => (z.1,S.affine z.1 z.2)
  have hf : Measurable f := by
    apply measurable_fst.prodMk
    exact (((measurable_of_finite S.ratio).comp measurable_fst).mul measurable_snd).add
      ((measurable_of_finite S.offset).comp measurable_fst)
  have hh := congrArg (Measure.map f) (head_tail_point_law S)
  have hp : Measurable (fun ω : ℕ → ι => (ω 0,point S (shift ω))) :=
    (measurable_pi_apply 0).prodMk ((point_measurable S).comp shift_measurable)
  rw [Measure.map_map hf hp] at hh
  have he : f ∘ (fun ω => (ω 0,point S (shift ω))) = fun ω => (ω 0,point S ω) := by
    funext ω
    exact Prod.ext rfl (point_shift S ω).symm
  rw [he] at hh
  rw [hh]
  change ((∑ i, ENNReal.ofReal (S.weight i) • Measure.dirac i).prod (law S)).map f = _
  rw [← Measure.sum_fintype,Measure.prod_sum_left,Measure.sum_fintype,
    Measure.map_finset_sum hf.aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.prod_smul_left,Measure.map_smul _ _ f,Measure.dirac_prod,
    Measure.map_map hf measurable_prodMk_left,System.component,Measure.prod_smul_right,
    Measure.dirac_prod,Measure.map_map measurable_prodMk_left (S.affine_continuous i).measurable]
  rfl

theorem ae_head_point (S : System ι) {P : ι → ℝ → Prop}
    (hP : ∀ i, ∀ᵐ x ∂S.component (law S) i, P i x) :
    ∀ᵐ ω ∂addressMeasure S, P (ω 0) (point S ω) := by
  have hh : ∀ᵐ z ∂(addressMeasure S).map (fun ω => (ω 0,point S ω)), P z.1 z.2 := by
    rw [head_point_law,ae_finsetSum_measure_iff]
    intro i _
    rw [Measure.dirac_prod,(measurableEmbedding_prodMk_left i).ae_map_iff]
    exact hP i
  exact ae_of_ae_map (head_point_measurable S).aemeasurable hh

theorem integrable_head_point (S : System ι) {f : ι → ℝ → ℝ}
    (hfm : ∀ i, Measurable (f i)) (hf : ∀ i, Integrable (f i) (S.component (law S) i)) :
    Integrable (fun ω => f (ω 0) (point S ω)) (addressMeasure S) := by
  have hm : Measurable (fun z : ι × ℝ => f z.1 z.2) :=
    measurable_from_prod_countable_right hfm
  have hi : Integrable (fun z : ι × ℝ => f z.1 z.2)
      ((addressMeasure S).map (fun ω => (ω 0,point S ω))) := by
    rw [head_point_law,integrable_finsetSum_measure]
    intro i _
    rw [Measure.dirac_prod,integrable_map_measure hm.aestronglyMeasurable
      measurable_prodMk_left.aemeasurable]
    exact hf i
  exact hi.comp_measurable (head_point_measurable S)

theorem envelope_joint_measurable (S : System ι) : Measurable (fun z : ι × ℝ =>
    BallRatios.logEnvelope (law S) (S.component (law S) z.1) z.2) := by
  apply measurable_from_prod_countable_right
  intro i
  exact BallRatios.logEnvelope_measurable (law S) (S.component (law S) i)

theorem envelope_measurable (S : System ι) : Measurable (envelope S) := by
  unfold envelope
  have hh := (envelope_joint_measurable S).comp (head_point_measurable S)
  exact hh

omit [Nonempty ι] in
theorem envelope_nonneg (S : System ι) (ω : ℕ → ι) : 0 ≤ envelope S ω :=
  BallRatios.logEnvelope_nonneg _ _ _

theorem envelope_integrable (S : System ι) : Integrable (envelope S) (addressMeasure S) :=
  integrable_head_point S (fun i => BallRatios.logEnvelope_measurable _ (S.component (law S) i))
    (fun i => BallRatios.logEnvelope_integrable _ (S.component (law S) i))

theorem corr_joint_measurable (S : System ι) : Measurable (fun z : ι × (ℝ × ℝ) =>
    BallRatios.logRatio (law S) (S.component (law S) z.1) z.2.1 z.2.2) := by
  apply measurable_from_prod_countable_right
  intro i
  exact BallRatios.logRatio_measurable (law S) (S.component (law S) i)

theorem corr_measurable (S : System ι) (n : ℕ) : Measurable (corr S n) := by
  unfold corr
  have hh := (corr_joint_measurable S).comp ((measurable_pi_apply 0).prodMk
    ((point_measurable S).prodMk (slope_measurable S n).abs))
  exact hh

theorem corrLimit_measurable (S : System ι) : Measurable (corrLimit S) := by
  have hm : Measurable (fun z : ι × ℝ =>
      Real.log ((law S).rnDeriv (S.component (law S) z.1) z.2).toReal) := by
    apply measurable_from_prod_countable_right
    intro i
    exact ((law S).measurable_rnDeriv (S.component (law S) i)).ennreal_toReal.log
  exact hm.comp (head_point_measurable S)

theorem ae_corr_bounds (S : System ι) : ∀ᵐ ω ∂addressMeasure S, ∀ n : ℕ, 0 < n →
    0 ≤ corr S n ω ∧ corr S n ω ≤ envelope S ω := by
  filter_upwards [ae_head_point S (fun i => BallRatios.logRatio_bounds _ _
    (S.component_le _ (law_selfSimilar S) i))] with ω hω
  intro n hn
  exact hω _ (abs_slope_pos S ω n) (abs_slope_lt_one S ω hn)

theorem ae_corr_limit (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => corr S n ω) atTop (𝓝 (corrLimit S ω)) := by
  filter_upwards [ae_head_point S (fun i => BallRatios.ae_logRatio_limit _ _
    (S.component_le _ (law_selfSimilar S) i))] with ω hω
  apply hω.2.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨slope_tendsto_zero S ω,
    Eventually.of_forall (abs_slope_pos S ω)⟩

end EntropyRateDimension.Coding

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.ErgodicAverages ----
namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators

namespace EntropyRateDimension
namespace ErgodicAux

variable {α : Type uα}

theorem maxSum_nonneg (T : α → α) (f : α → ℝ) (n : ℕ) (x : α) :
    0 ≤ maxSum T f n x := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

theorem maxSum_mono (T : α → α) (f : α → ℝ) (x : α) :
    Monotone (fun n => maxSum T f n x) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n generalizing x with
  | zero => exact maxSum_nonneg T f 1 x
  | succ n ih => exact max_le_max_left _ (by linarith [ih (T x)])

theorem birkhoffSum_le_maxSum (T : α → α) (f : α → ℝ) (n : ℕ) (x : α) :
    birkhoffSum T f n x ≤ maxSum T f n x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [birkhoffSum_succ', maxSum_succ]
    exact (show f x + birkhoffSum T f n (T x) ≤ f x + maxSum T f n (T x) by
      linarith [ih (T x)]).trans (le_max_right _ _)

variable [MeasurableSpace α] {μ : Measure α}

theorem maxSum_measurable {T : α → α} {f : α → ℝ}
    (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    Measurable (maxSum T f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max (hf.add (ih.comp hT))

theorem maxSum_integrable {T : α → α} {f : α → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    Integrable (maxSum T f n) μ := by
  induction n with
  | zero => exact integrable_zero α ℝ μ
  | succ n ih =>
    exact (integrable_zero α ℝ μ).sup (hf.add (hT.integrable_comp_of_integrable ih))

theorem integral_comp_preserving {T : α → α} {f : α → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    (∫ x, f (T x) ∂μ) = ∫ x, f x ∂μ := by
  have hm : AEStronglyMeasurable f (μ.map T) := by rw [hT.map_eq]; exact hf.1
  calc
    (∫ x, f (T x) ∂μ) = ∫ x, f x ∂μ.map T :=
      (integral_map hT.measurable.aemeasurable hm).symm
    _ = ∫ x, f x ∂μ := by rw [hT.map_eq]

theorem hopf_finite {T : α → α} {f : α → ℝ}
    (hT : MeasurePreserving T μ μ) (hfm : Measurable f) (hf : Integrable f μ)
    (n : ℕ) :
    0 ≤ ∫ x in {x | 0 < maxSum T f n x}, f x ∂μ := by
  cases n with
  | zero => simp
  | succ n =>
    let E := {x | 0 < maxSum T f (n+1) x}
    have hE : MeasurableSet E := measurableSet_lt measurable_const
      (maxSum_measurable hT.measurable hfm _)
    have hpoint : ∀ x, maxSum T f (n+1) x - maxSum T f n (T x) ≤ E.indicator f x := by
      intro x
      by_cases hx : x ∈ E
      · rw [Set.indicator_of_mem hx]
        have hp : 0 < maxSum T f (n+1) x := hx
        rw [maxSum_succ, lt_max_iff] at hp
        have hn : 0 ≤ f x + maxSum T f n (T x) := (hp.resolve_left (lt_irrefl _)).le
        rw [maxSum_succ, max_eq_right hn]
        linarith
      · rw [Set.indicator_of_notMem hx]
        have hz : maxSum T f (n+1) x = 0 := le_antisymm (not_lt.mp hx)
          (maxSum_nonneg T f _ x)
        rw [hz]
        linarith [maxSum_nonneg T f n (T x)]
    have hin := maxSum_integrable hT hf n
    have his := maxSum_integrable hT hf (n+1)
    have hmono : (∫ x, maxSum T f n x ∂μ) ≤ ∫ x, maxSum T f (n+1) x ∂μ :=
      integral_mono hin his (fun x => maxSum_mono T f x (Nat.le_succ n))
    have hle := integral_mono (his.sub (hT.integrable_comp_of_integrable hin))
      (hf.indicator hE) hpoint
    have hsub : (∫ x, maxSum T f (n+1) x - maxSum T f n (T x) ∂μ) =
        (∫ x, maxSum T f (n+1) x ∂μ) - (∫ x, maxSum T f n x ∂μ) := by
      calc
        _ = (∫ x, maxSum T f (n+1) x ∂μ) - (∫ x, maxSum T f n (T x) ∂μ) :=
          integral_sub his (hT.integrable_comp_of_integrable hin)
        _ = _ := by rw [integral_comp_preserving hT hin]
    have hnon : 0 ≤ ∫ x, maxSum T f (n+1) x - maxSum T f n (T x) ∂μ := by
      rw [hsub]
      exact sub_nonneg.mpr hmono
    exact (hnon.trans hle).trans_eq (integral_indicator hE)

omit [MeasurableSpace α] in
theorem bddAbove_range_nat_iff (u : ℕ → ℝ) :
    BddAbove (Set.range u) ↔ ∃ N : ℕ, ∀ n, u n ≤ N := by
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨N, hN⟩ := exists_nat_ge C
    exact ⟨N, fun n => (hC ⟨n,rfl⟩).trans hN⟩
  · rintro ⟨N,hN⟩
    exact ⟨N, fun _ ⟨n,hn⟩ => hn ▸ hN n⟩

theorem sum_measurable {T : α → α} {f : α → ℝ}
    (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    Measurable (birkhoffSum T f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have he : birkhoffSum T f (n+1) = fun x => f x + birkhoffSum T f n (T x) :=
      funext (birkhoffSum_succ' T f n)
    rw [he]
    exact hf.add (ih.comp hT)

theorem boundedSums_measurable {T : α → α} {f : α → ℝ}
    (hT : Measurable T) (hf : Measurable f) : MeasurableSet (boundedSums T f) := by
  have he : boundedSums T f = {x | ∃ N : ℕ, ∀ n : ℕ, birkhoffSum T f n x ≤ N} := by
    ext x
    exact bddAbove_range_nat_iff _
  rw [he]
  simp only [Set.ofPred_exists, Set.ofPred_forall]
  exact MeasurableSet.iUnion fun N => MeasurableSet.iInter fun n =>
    measurableSet_le (sum_measurable hT hf n) measurable_const

omit [MeasurableSpace α] in
theorem boundedSums_invariant (T : α → α) (f : α → ℝ) :
    T ⁻¹' boundedSums T f = boundedSums T f := by
  ext x
  change BddAbove (Set.range (fun n : ℕ => birkhoffSum T f n (T x))) ↔
    BddAbove (Set.range (fun n : ℕ => birkhoffSum T f n x))
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨max 0 (f x+C), ?_⟩
    rintro _ ⟨n,rfl⟩
    cases n with
    | zero => exact le_max_left (0 : ℝ) (f x+C)
    | succ n =>
      dsimp only
      rw [birkhoffSum_succ']
      exact (show f x+birkhoffSum T f n (T x) ≤ f x+C by
        linarith [hC ⟨n,rfl⟩]).trans (le_max_right _ _)
  · rintro ⟨C,hC⟩
    refine ⟨C-f x, ?_⟩
    rintro _ ⟨n,rfl⟩
    have hh := hC ⟨n+1,rfl⟩
    dsimp only at hh ⊢
    rw [birkhoffSum_succ'] at hh
    linarith

theorem hopf_of_ae_positive_sum {T : α → α} {f : α → ℝ}
    (hT : MeasurePreserving T μ μ) (hfm : Measurable f) (hf : Integrable f μ)
    (hpos : ∀ᵐ x ∂μ, ∃ n, 0 < maxSum T f n x) :
    0 ≤ ∫ x, f x ∂μ := by
  let E : ℕ → Set α := fun n => {x | 0 < maxSum T f n x}
  have hE : ∀ n, MeasurableSet (E n) := fun n =>
    measurableSet_lt measurable_const (maxSum_measurable hT.measurable hfm n)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => (E n).indicator f x) atTop (𝓝 (f x)) := by
    filter_upwards [hpos] with x hx
    obtain ⟨n, hn⟩ := hx
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with k hk
    have hxk : x ∈ E k := hn.trans_le (maxSum_mono T f x hk)
    exact (Set.indicator_of_mem hxk f).symm
  have hlimint := tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun n => (hf.indicator (hE n)).aestronglyMeasurable) hf.norm
    (fun n => ae_of_all μ fun x => by
      by_cases hx : x ∈ E n
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]) hlim
  apply ge_of_tendsto hlimint
  exact Eventually.of_forall fun n => by
    rw [integral_indicator (hE n)]
    exact hopf_finite hT hfm hf n

theorem ae_boundedSums_of_integral_neg {T : α → α} {f : α → ℝ}
    (hT : Ergodic T μ) (hfm : Measurable f) (hf : Integrable f μ)
    (hneg : (∫ x, f x ∂μ) < 0) : ∀ᵐ x ∂μ, x ∈ boundedSums T f := by
  rcases hT.toPreErgodic.ae_mem_or_ae_notMem
    (boundedSums_measurable hT.measurable hfm) (boundedSums_invariant T f) with h | h
  · exact h
  · have hp : ∀ᵐ x ∂μ, ∃ n, 0 < maxSum T f n x := by
      filter_upwards [h] with x hx
      obtain ⟨y, ⟨n,rfl⟩,hn⟩ := not_bddAbove_iff.mp hx 0
      exact ⟨n,hn.trans_le (birkhoffSum_le_maxSum T f n x)⟩
    exact (not_le_of_gt hneg (hopf_of_ae_positive_sum hT.toMeasurePreserving hfm hf hp)).elim

omit [MeasurableSpace α] in
theorem sum_sub_const (T : α → α) (f : α → ℝ) (c : ℝ) (n : ℕ) (x : α) :
    birkhoffSum T (fun y => f y-c) n x = birkhoffSum T f n x - n*c := by
  simp [birkhoffSum, Finset.sum_sub_distrib]

theorem ae_upper_average [IsProbabilityMeasure μ] {T : α → α} {f : α → ℝ}
    (hT : Ergodic T μ) (hfm : Measurable f) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, ∀ a : ℝ, (∫ x, f x ∂μ) < a →
      ∀ᶠ n : ℕ in atTop, birkhoffSum T f n x / (n : ℝ) < a := by
  have hb : ∀ q : ℚ, ∀ᵐ x ∂μ, (∫ x, f x ∂μ) < (q : ℝ) →
      x ∈ boundedSums T (fun y => f y - q) := by
    intro q
    by_cases hq : (∫ x, f x ∂μ) < (q : ℝ)
    · have hn : (∫ x, (f x - q) ∂μ) < 0 := by
        rw [integral_sub hf (integrable_const _)]
        simpa using sub_neg.mpr hq
      filter_upwards [ae_boundedSums_of_integral_neg hT
        (hfm.sub measurable_const) (hf.sub (integrable_const _)) hn] with x hx using
        fun _ => hx
    · exact ae_of_all μ fun _ h => (hq h).elim
  filter_upwards [ae_all_iff.mpr hb] with x hx
  intro a ha
  obtain ⟨q,hq,hqa⟩ := exists_rat_btwn ha
  obtain ⟨C,hC⟩ := hx q hq
  have hlim : Tendsto (fun n : ℕ => (q : ℝ)+C/n) atTop (𝓝 (q : ℝ)) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_atTop_nhds_zero_nat C)
  filter_upwards [(tendsto_order.mp hlim).2 a hqa, eventually_ge_atTop 1] with n hn hn1
  have hN : (0 : ℝ) < n := by exact_mod_cast hn1
  have hh := hC ⟨n,rfl⟩
  dsimp only at hh
  rw [sum_sub_const] at hh
  have he : birkhoffSum T f n x / (n : ℝ) ≤ (q : ℝ)+C/n := by
    apply (div_le_iff₀ hN).mpr
    have hre : ((q : ℝ)+C/n)*n = n*(q : ℝ)+C := by field_simp
    rw [hre]
    linarith
  exact he.trans_lt hn

theorem ae_tendsto_average [IsProbabilityMeasure μ] {T : α → α} {f : α → ℝ}
    (hT : Ergodic T μ) (hfm : Measurable f) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n : ℕ => birkhoffSum T f n x / (n : ℝ)) atTop
      (𝓝 (∫ x, f x ∂μ)) := by
  filter_upwards [ae_upper_average hT hfm hf, ae_upper_average hT hfm.neg hf.neg]
    with x hx hxneg
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hm : (∫ x, -f x ∂μ) < -a := by rw [integral_neg]; linarith
    filter_upwards [hxneg (-a) hm] with n hn
    have he : birkhoffSum T (fun y => -f y) n x = -birkhoffSum T f n x := by
      simp [birkhoffSum]
    change birkhoffSum T (fun y => -f y) n x / (n : ℝ) < -a at hn
    rw [he, neg_div] at hn
    linarith
  · exact hx

end ErgodicAux
end EntropyRateDimension

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.TriangularAverages ----
namespace OAI

universe uα

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace EntropyRateDimension.ErgodicAux

variable {α : Type uα}

theorem error_bound {f : ℕ → α → ℝ} {g F : α → ℝ}
    (hf : ∀ n x, |f n x| ≤ F x) (hg : ∀ x, |g x| ≤ F x) (n : ℕ) (x : α) :
    |f n x - g x| ≤ 2 * F x := by
  exact (abs_sub _ _).trans (by linarith [hf n x,hg x])

theorem tailError_bound {f : ℕ → α → ℝ} {g F : α → ℝ}
    (hf : ∀ n x, |f n x| ≤ F x) (hg : ∀ x, |g x| ≤ F x) (N : ℕ) (x : α) :
    tailError f g N x ≤ 2*F x :=
  ciSup_le fun k => error_bound hf hg (N+k) x

theorem error_le_tailError {f : ℕ → α → ℝ} {g F : α → ℝ}
    (hf : ∀ n x, |f n x| ≤ F x) (hg : ∀ x, |g x| ≤ F x) {N k : ℕ}
    (hk : N ≤ k) (x : α) : |f k x - g x| ≤ tailError f g N x := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
  exact le_ciSup (f := fun k : ℕ => |f (N+k) x - g x|)
    ⟨2*F x,fun _ ⟨k,hk⟩ => hk ▸ error_bound hf hg (N+k) x⟩ j

theorem tailError_nonneg {f : ℕ → α → ℝ} {g F : α → ℝ}
    (hf : ∀ n x, |f n x| ≤ F x) (hg : ∀ x, |g x| ≤ F x) (N : ℕ) (x : α) :
    0 ≤ tailError f g N x :=
  (abs_nonneg _).trans (error_le_tailError hf hg le_rfl x)

theorem tailError_tendsto {f : ℕ → α → ℝ} {g F : α → ℝ}
    (hf : ∀ n x, |f n x| ≤ F x) (hg : ∀ x, |g x| ≤ F x) {x : α}
    (hx : Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => tailError f g n x) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le (tailError_nonneg hf hg n x)
  · intro b hb
    obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp hx (b/2) (by linarith)
    filter_upwards [eventually_ge_atTop N] with n hn
    apply lt_of_le_of_lt (ciSup_le fun k => (hN (n+k) (by omega)).le) (by linarith)

variable [MeasurableSpace α] {μ : Measure α}

theorem tailError_measurable {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g) (N : ℕ) :
    Measurable (tailError f g N) :=
  Measurable.iSup fun k => ((hf (N+k)).sub hg).abs

theorem tailError_integrable {f : ℕ → α → ℝ} {g F : α → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hf : ∀ n x, |f n x| ≤ F x) (hg : ∀ x, |g x| ≤ F x)
    (hF : Integrable F μ) (N : ℕ) : Integrable (tailError f g N) μ := by
  apply (hF.const_mul 2).mono' (tailError_measurable hfm hgm N).aestronglyMeasurable
  exact ae_of_all μ fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (tailError_nonneg hf hg N x)]
    exact tailError_bound hf hg N x

theorem tailError_integral_tendsto {f : ℕ → α → ℝ} {g F : α → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hf : ∀ n x, |f n x| ≤ F x) (hg : ∀ x, |g x| ≤ F x)
    (hF : Integrable F μ) (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫ x, tailError f g n x ∂μ) atTop (𝓝 0) := by
  have ht := tendsto_integral_of_dominated_convergence (fun x => 2*F x)
    (fun n => (tailError_measurable hfm hgm n).aestronglyMeasurable) (hF.const_mul 2)
    (fun n => ae_of_all μ fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (tailError_nonneg hf hg n x)]
      exact tailError_bound hf hg n x)
    (hlim.mono fun x hx => tailError_tendsto hf hg hx)
  simpa using ht

omit [MeasurableSpace α] in
 theorem triangle_error_bound {f : ℕ → α → ℝ} {g F : α → ℝ}
    (hf : ∀ n x, |f n x| ≤ F x) (hg : ∀ x, |g x| ≤ F x)
    (T : α → α) (n N : ℕ) (x : α) :
    |(∑ j ∈ Finset.range (n+N), f (n+N-j) (T^[j] x)) - birkhoffSum T g (n+N) x| ≤
      birkhoffSum T (tailError f g N) (n+N) x +
        2 * (birkhoffSum T F (n+N) x - birkhoffSum T F n x) := by
  rw [birkhoffSum,← Finset.sum_sub_distrib]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  have hfirst : (∑ j ∈ Finset.range n, |f (n+N-j) (T^[j] x) - g (T^[j] x)|) ≤
      ∑ j ∈ Finset.range n, tailError f g N (T^[j] x) := by
    apply Finset.sum_le_sum
    intro j hj
    exact error_le_tailError hf hg (by have := Finset.mem_range.mp hj; omega) _
  have hlast : (∑ j ∈ Finset.range N, |f (n+N-(n+j)) (T^[n+j] x) - g (T^[n+j] x)|) ≤
      2 * ∑ j ∈ Finset.range N, F (T^[n+j] x) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => error_bound hf hg _ _
  have hn : 0 ≤ ∑ j ∈ Finset.range N, tailError f g N (T^[n+j] x) :=
    Finset.sum_nonneg fun _ _ => tailError_nonneg hf hg _ _
  simp only [birkhoffSum,Finset.sum_range_add]
  linarith

 theorem tendsto_shift_denominator {a : ℕ → ℝ} {L : ℝ}
    (ha : Tendsto (fun n => a n / (n : ℝ)) atTop (𝓝 L)) (N : ℕ) :
    Tendsto (fun n => a n / (n+N : ℕ)) atTop (𝓝 L) := by
  have hh := ha.mul (tendsto_natCast_div_add_atTop (N : ℝ))
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

 theorem ae_tendsto_triangle [IsProbabilityMeasure μ] {T : α → α}
    (hT : Ergodic T μ) {f : ℕ → α → ℝ} {g F : α → ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g) (hFm : Measurable F)
    (hf : ∀ n x, |f n x| ≤ F x) (hg : ∀ x, |g x| ≤ F x) (hF : Integrable F μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    ∀ᵐ x ∂μ, Tendsto (fun n => (∑ j ∈ Finset.range n, f (n-j) (T^[j] x)) / (n : ℝ))
      atTop (𝓝 (∫ x, g x ∂μ)) := by
  have hgi : Integrable g μ := hF.mono' hgm.aestronglyMeasurable
    (ae_of_all μ fun x => by simpa only [Real.norm_eq_abs] using hg x)
  have hb := tailError_integral_tendsto hfm hgm hf hg hF hlim
  filter_upwards [ae_tendsto_average hT hgm hgi,ae_tendsto_average hT hFm hF,
    ae_all_iff.mpr (fun N => ae_tendsto_average hT (tailError_measurable hfm hgm N)
      (tailError_integrable hfm hgm hf hg hF N))] with x hx hxF hxE
  have he : Tendsto (fun n => ((∑ j ∈ Finset.range n, f (n-j) (T^[j] x)) -
      birkhoffSum T g n x) / (n : ℝ)) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := ((tendsto_order.mp hb).2 (ε/2) (by linarith)).exists
    have hplus : Tendsto (fun n => birkhoffSum T F (n+N) x / (n+N : ℕ))
        atTop (𝓝 (∫ x, F x ∂μ)) := (tendsto_add_atTop_iff_nat N).mpr hxF
    have hdiff := hplus.sub (tendsto_shift_denominator hxF N)
    simp only [sub_self] at hdiff
    have hupper := ((tendsto_add_atTop_iff_nat N).mpr (hxE N)).add (hdiff.const_mul 2)
    simp only [mul_zero,add_zero] at hupper
    obtain ⟨k,hk⟩ := eventually_atTop.mp ((tendsto_order.mp hupper).2 ε (by linarith))
    refine ⟨max k 1 + N,?_⟩
    intro m hm
    obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le (show N ≤ m by omega)
    have hn : k ≤ n := by omega
    have hnp : 0 < N+n := by omega
    have hpos : (0 : ℝ) < (N+n : ℕ) := by exact_mod_cast hnp
    rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos hpos]
    have hc := triangle_error_bound hf hg T n N x
    have hle := div_le_div_of_nonneg_right hc (show (0 : ℝ) ≤ (n+N : ℕ) by positivity)
    have hu := hk n hn
    rw [add_comm N n]
    apply lt_of_le_of_lt hle
    simpa only [add_div,mul_div_assoc,sub_div] using hu
  have hz := he.add hx
  simp only [zero_add] at hz
  convert hz using 1
  funext n
  ring

end EntropyRateDimension.ErgodicAux

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.Clipping ----
namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace EntropyRateDimension.BallRatios
open MeasureTheory Metric Set Filter
open scoped Topology BigOperators

theorem information_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (x r : ℝ) :
    0 ≤ information μ x r := by
  unfold information
  exact neg_nonneg.mpr (Real.log_nonpos ENNReal.toReal_nonneg (measureReal_le_one))

theorem information_antitone (μ : Measure ℝ) [IsProbabilityMeasure μ] {x r s : ℝ}
    (hx : x ∈ μ.support) (hr : 0 < r) (hrs : r ≤ s) :
    information μ x s ≤ information μ x r := by
  apply neg_le_neg
  apply Real.log_le_log (massReal_pos μ hx hr)
  exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (closedBall_subset_closedBall hrs))

theorem information_one_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hK : IsCompact μ.support) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ μ.support, information μ x 1 ≤ C := by
  classical
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover (fun x : μ.support => ball (x : ℝ) (1/2))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (by norm_num)⟩)
  refine ⟨∑ z ∈ t, information μ z.val (1/2),
    Finset.sum_nonneg (fun _ _ => information_nonneg _ _ _),?_⟩
  intro x hx
  obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (ht hx)
  have hsub : closedBall y.val (1/2) ⊆ closedBall x 1 := by
    intro z hz
    have hzy : dist z y.val ≤ 1/2 := mem_closedBall.mp hz
    have hyx : dist y.val x < 1/2 := by simpa only [dist_comm] using mem_ball.mp hxy
    apply mem_closedBall.mpr
    calc
      dist z x ≤ dist z y.val + dist y.val x := dist_triangle _ _ _
      _ ≤ 1 := by linarith
  have hh : information μ x 1 ≤ information μ y.val (1/2) := by
    apply neg_le_neg
    exact Real.log_le_log (massReal_pos μ y.property (by norm_num))
      (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub))
  exact hh.trans (Finset.single_le_sum (fun z _ => information_nonneg μ z.val (1/2)) hy)

end EntropyRateDimension.BallRatios

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.BallLimits ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter
open EntropyRateDimension.Bernoulli EntropyRateDimension.ErgodicAux
open scoped Topology BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI_1
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI_1
theorem clippedCorr_measurable (S : System ι) (n : ℕ) : Measurable (clippedCorr S n) :=
  measurable_const.max ((envelope_measurable S).min (corr_measurable S n))
theorem clippedLimit_measurable (S : System ι) : Measurable (clippedLimit S) :=
  measurable_const.max ((envelope_measurable S).min (corrLimit_measurable S))

omit [Nonempty ι] in
theorem clip_bound {E x : ℝ} (hE : 0 ≤ E) : |max 0 (min E x)| ≤ E := by
  rw [abs_of_nonneg (le_max_left _ _)]
  exact max_le hE (min_le_left _ _)

omit [Nonempty ι] in
theorem clippedCorr_bound (S : System ι) (n : ℕ) (ω : ℕ → ι) :
    |clippedCorr S n ω| ≤ envelope S ω := clip_bound (envelope_nonneg S ω)
omit [Nonempty ι] in
theorem clippedLimit_bound (S : System ι) (ω : ℕ → ι) :
    |clippedLimit S ω| ≤ envelope S ω := clip_bound (envelope_nonneg S ω)

theorem ae_clipped_limit (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => clippedCorr S n ω) atTop (𝓝 (clippedLimit S ω)) := by
  filter_upwards [ae_corr_limit S] with ω hω
  exact tendsto_const_nhds.max (tendsto_const_nhds.min hω)

theorem ae_corr_triangle (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => (∑ j ∈ Finset.range n, corr S (n-j) (shift^[j] ω)) / (n : ℝ))
      atTop (𝓝 (∫ ω, clippedLimit S ω ∂addressMeasure S)) := by
  have hT : Ergodic shift (addressMeasure S) := shift_ergodic (symbolMeasure S)
  have ht := ae_tendsto_triangle hT (clippedCorr_measurable S) (clippedLimit_measurable S)
    (envelope_measurable S) (clippedCorr_bound S) (clippedLimit_bound S)
    (envelope_integrable S) (ae_clipped_limit S)
  have ha : ∀ᵐ ω ∂addressMeasure S, ∀ j : ℕ, ∀ n : ℕ, 0 < n →
      0 ≤ corr S n (shift^[j] ω) ∧ corr S n (shift^[j] ω) ≤ envelope S (shift^[j] ω) := by
    apply ae_all_iff.mpr
    intro j
    exact ((show MeasurePreserving shift (addressMeasure S) (addressMeasure S) from
      shift_preserving (symbolMeasure S)).iterate j).quasiMeasurePreserving.ae (ae_corr_bounds S)
  filter_upwards [ht,ha] with ω hω hbound
  convert hω using 1
  funext n
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : 0 < n-j := by have := Finset.mem_range.mp hj; omega
  obtain ⟨h0,h1⟩ := hbound j (n-j) hjn
  simp only [clippedCorr,min_eq_right h1,max_eq_right h0]

theorem prefixInfo_succ (S : System ι) (n : ℕ) (ω : ℕ → ι)
    (hω : point S (shift ω) ∈ (law S).support) :
    prefixInfo S (n+1) ω = prefixInfo S n (shift ω) + weightObs S ω - corr S (n+1) ω := by
  have he := BallRatios.information_component S (law S) (law_selfSimilar S) (ω 0)
    hω (abs_slope_pos S (shift ω) n)
  have hs : |slope S ω (n+1)| = |S.ratio (ω 0)| * |slope S (shift ω) n| := by
    rw [slope_shift,abs_mul]
  unfold prefixInfo weightObs corr
  rw [point_shift S ω,hs]
  exact he

omit [Nonempty ι] in
theorem triangle_succ (S : System ι) (n : ℕ) (ω : ℕ → ι) :
    (∑ j ∈ Finset.range (n+1), corr S (n+1-j) (shift^[j] ω)) =
      corr S (n+1) ω + ∑ j ∈ Finset.range n, corr S (n-j) (shift^[j] (shift ω)) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.add_sub_add_right,Function.iterate_succ_apply,Function.iterate_zero_apply,
    Nat.sub_zero]
  ring

theorem prefixInfo_telescope (S : System ι) (ω : ℕ → ι)
    (hω : ∀ j : ℕ, point S (shift^[j] ω) ∈ (law S).support) (n : ℕ) :
    prefixInfo S n ω = birkhoffSum shift (weightObs S) n ω -
      (∑ j ∈ Finset.range n, corr S (n-j) (shift^[j] ω)) +
      BallRatios.information (law S) (point S (shift^[n] ω)) 1 := by
  induction n generalizing ω with
  | zero => simp [prefixInfo,slope_zero,birkhoffSum]
  | succ n ih =>
    have htail : ∀ j : ℕ, point S (shift^[j] (shift ω)) ∈ (law S).support := by
      intro j
      simpa only [Function.iterate_succ_apply] using hω (j+1)
    rw [prefixInfo_succ S n ω (by simpa using hω 1),ih (shift ω) htail,
      triangle_succ,birkhoffSum_succ']
    simp only [Function.iterate_succ_apply]
    ring

omit [Nonempty ι] in
theorem head_integrable (S : System ι) (f : ι → ℝ) :
    Integrable (fun ω : ℕ → ι => f (ω 0)) (addressMeasure S) := by
  classical
  apply Integrable.of_bound ((measurable_of_finite f).comp (measurable_pi_apply 0)).aestronglyMeasurable
    (∑ i, |f i|)
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun i _ => abs_nonneg (f i)) (Finset.mem_univ (ω 0))

omit [Nonempty ι] in
theorem head_integral (S : System ι) (f : ι → ℝ) :
    (∫ ω, f (ω 0) ∂addressMeasure S) = ∑ i, S.weight i * f i := by
  have he : (addressMeasure S).map (fun ω => ω 0) = symbolMeasure S :=
    Measure.infinitePi_map_eval _ _
  have hm := measurable_of_finite f
  rw [← integral_map (measurable_pi_apply 0).aemeasurable hm.aestronglyMeasurable,he]
  unfold symbolMeasure
  rw [integral_finsetSum_measure (fun i _ =>
    (show Integrable f (Measure.dirac i) from Integrable.of_finite).smul_measure (by simp))]
  simp only [integral_smul_measure,integral_dirac,smul_eq_mul,
    ENNReal.toReal_ofReal (S.weight_nonneg _)]

theorem ae_point_support (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    ∀ j : ℕ, point S (shift^[j] ω) ∈ (law S).support := by
  apply ae_all_iff.mpr
  intro j
  have ha : ∀ᵐ ω ∂addressMeasure S, point S ω ∈ (law S).support :=
    ae_of_ae_map (point_measurable S).aemeasurable (law S).support_mem_ae
  exact ((show MeasurePreserving shift (addressMeasure S) (addressMeasure S) from
      shift_preserving (symbolMeasure S)).iterate j).quasiMeasurePreserving.ae ha

theorem law_support_compact (S : System ι) : IsCompact (law S).support := by
  obtain ⟨B,_,hB⟩ := S.selfSimilar_compact (law S) (law_selfSimilar S)
  exact isCompact_Icc.of_isClosed_subset (law S).isClosed_support
    (Measure.support_subset_of_isClosed isClosed_Icc hB)

theorem ae_prefixInfo_limit (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => prefixInfo S n ω / (n : ℝ)) atTop (𝓝 (infoRate S)) := by
  obtain ⟨C,hC,hCb⟩ := BallRatios.information_one_bound (law S) (law_support_compact S)
  have hT : Ergodic shift (addressMeasure S) := shift_ergodic (symbolMeasure S)
  have hb := ae_tendsto_average hT
    ((measurable_of_finite (fun i => -Real.log (S.weight i))).comp (measurable_pi_apply 0))
    (head_integrable S (fun i => -Real.log (S.weight i)))
  filter_upwards [hb,ae_corr_triangle S,ae_point_support S] with ω hweight hcorr hsupp
  have hend : Tendsto (fun n => BallRatios.information (law S)
      (point S (shift^[n] ω)) 1 / (n : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun n => div_nonneg (BallRatios.information_nonneg _ _ _) (Nat.cast_nonneg n))
      (fun n => div_le_div_of_nonneg_right (hCb _ (hsupp n)) (Nat.cast_nonneg n))
    exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hh := (hweight.sub hcorr).add hend
  convert hh using 1
  · funext n
    rw [prefixInfo_telescope S ω hsupp,add_div,sub_div]
    rfl
  · simp only [infoRate,weightObs,add_zero,Function.comp_def]

end EntropyRateDimension.Coding

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.RadiusGrowth ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter
open EntropyRateDimension.ErgodicAux
open scoped Topology BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI_2
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI_2
omit [Fintype ι] [Nonempty ι] in
theorem shift_iterate (n : ℕ) (ω : ℕ → ι) (k : ℕ) : shift^[n] ω k = ω (k+n) :=
  Bernoulli.shift_iterate n ω k

omit [Nonempty ι] in
theorem contraction_integral (S : System ι) :
    (∫ ω, contractionObs S ω ∂addressMeasure S) = S.lyapunov * Real.log 2 := by
  change (∫ ω, -Real.log |S.ratio (ω 0)| ∂addressMeasure S) = _
  rw [head_integral S (fun i => -Real.log |S.ratio i|)]
  unfold System.lyapunov
  rw [neg_mul,Finset.sum_mul]
  simp only [mul_assoc,div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne',
    mul_neg,Finset.sum_neg_distrib]

omit [Nonempty ι] in
theorem slope_log_sum (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    -Real.log |slope S ω n| = birkhoffSum shift (contractionObs S) n ω := by
  induction n with
  | zero => simp [slope_zero,birkhoffSum]
  | succ n ih =>
    rw [slope_succ,abs_mul,Real.log_mul (abs_slope_pos S ω n).ne' (S.ratio_pos _).ne',
      neg_add,ih,birkhoffSum_succ]
    simp only [contractionObs,shift_iterate,zero_add]

omit [Nonempty ι] in
theorem ae_slope_log_limit (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => -Real.log |slope S ω n| / (n : ℝ)) atTop
      (𝓝 (S.lyapunov * Real.log 2)) := by
  have hT : Ergodic shift (addressMeasure S) := Bernoulli.shift_ergodic (symbolMeasure S)
  have hm : Measurable (contractionObs S) :=
    (measurable_of_finite (fun i => -Real.log |S.ratio i|)).comp (measurable_pi_apply 0)
  have hi : Integrable (contractionObs S) (addressMeasure S) := head_integrable S (fun i => -Real.log |S.ratio i|)
  have hh := ae_tendsto_average hT hm hi
  rw [contraction_integral] at hh
  simpa only [slope_log_sum] using hh

theorem infoRate_nonneg (S : System ι) : 0 ≤ infoRate S := by
  obtain ⟨ω,hω⟩ := (ae_prefixInfo_limit S).exists
  exact ge_of_tendsto' hω (fun n => div_nonneg
    (BallRatios.information_nonneg _ _ _) (Nat.cast_nonneg n))

theorem exponent_nonneg (S : System ι) : 0 ≤ exponent S :=
  div_nonneg (infoRate_nonneg S) (mul_pos S.lyapunov_pos (Real.log_pos (by norm_num))).le

theorem ae_prefix_exponent (S : System ι) : ∀ᵐ ω ∂addressMeasure S,
    Tendsto (fun n => prefixInfo S n ω / -Real.log |slope S ω n|) atTop (𝓝 (exponent S)) := by
  filter_upwards [ae_prefixInfo_limit S,ae_slope_log_limit S] with ω hI hR
  have hh := hI.div hR (mul_pos S.lyapunov_pos (Real.log_pos (by norm_num))).ne'
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  dsimp only [Pi.div_apply]
  field_simp

end EntropyRateDimension.Coding

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.Interpolation ----
namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
open Set Filter
open scoped Topology

namespace EntropyRateDimension
namespace Interpolation

theorem tendsto_div_of_bounded_gaps {F : ℝ → ℝ} {t : ℕ → ℝ} {C d : ℝ}
    (hF : Monotone F) (ht : Monotone t) (ht0 : t 0 = 0)
    (hstep : ∀ n, t (n+1) ≤ t n+C) (htop : Tendsto t atTop atTop)
    (hlim : Tendsto (fun n => F (t n) / t n) atTop (𝓝 d)) :
    Tendsto (fun s => F s / s) atTop (𝓝 d) := by
  have hex : ∀ s : ℝ, ∃ n : ℕ, s < t n := fun s =>
    (htop.eventually (eventually_gt_atTop s)).exists
  let I : ℝ → ℕ := fun s => Nat.find (hex s)
  have hI : ∀ s, s < t (I s) := fun s => Nat.find_spec (hex s)
  have hItop : Tendsto I atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro N
    filter_upwards [eventually_ge_atTop (t N)] with s hs
    by_contra hn
    have hm := ht (le_of_not_ge hn)
    linarith [hI s]
  have hPtop : Tendsto (fun s => I s-1) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro N
    filter_upwards [(Filter.tendsto_atTop.mp hItop) (N+1)] with s hs
    omega
  have hbracket : ∀ s : ℝ, 0 ≤ s →
      t (I s-1) ≤ s ∧ s < t (I s) ∧ t (I s) ≤ s+C ∧ s-C ≤ t (I s-1) := by
    intro s hs
    have hi : 0 < I s := by
      by_contra hn
      have hz : I s = 0 := by omega
      have hh := hI s
      rw [hz,ht0] at hh
      linarith
    have hprev : t (I s-1) ≤ s := by
      exact le_of_not_gt (Nat.find_min (hex s) (by change I s-1 < I s; omega))
    have hst := hstep (I s-1)
    rw [Nat.sub_add_cancel hi] at hst
    exact ⟨hprev,hI s,by linarith,by linarith [hI s]⟩
  have hsmall : Tendsto (fun s : ℝ => C/s) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hUdiff : Tendsto (fun s : ℝ => t (I s)/s-1) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hsmall
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
      exact sub_nonneg.mpr ((le_div_iff₀ hs).mpr (by simpa using (hI s).le))
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
      have hh := (div_le_div_of_nonneg_right (hbracket s hs.le).2.2.1 hs.le)
      rw [add_div,div_self hs.ne'] at hh
      linarith
  have hU : Tendsto (fun s : ℝ => t (I s)/s) atTop (𝓝 1) := by
    have hh := hUdiff.add_const 1
    simpa only [sub_add_cancel,zero_add] using hh
  have hLdiff : Tendsto (fun s : ℝ => 1-t (I s-1)/s) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hsmall
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
      exact sub_nonneg.mpr ((div_le_one hs).mpr (hbracket s hs.le).1)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
      have hh := div_le_div_of_nonneg_right (hbracket s hs.le).2.2.2 hs.le
      rw [sub_div,div_self hs.ne'] at hh
      linarith
  have hL : Tendsto (fun s : ℝ => t (I s-1)/s) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub hLdiff
    simpa only [sub_sub_cancel,sub_zero] using hh
  have hUF : Tendsto (fun s : ℝ => F (t (I s))/s) atTop (𝓝 d) := by
    have hh := (hlim.comp hItop).mul hU
    rw [mul_one] at hh
    apply hh.congr'
    filter_upwards [(htop.comp hItop).eventually (eventually_gt_atTop (0 : ℝ))] with s hs
    have htne := hs.ne'
    dsimp [Function.comp_def] at htne
    dsimp only [Function.comp_def]
    field_simp
  have hLF : Tendsto (fun s : ℝ => F (t (I s-1))/s) atTop (𝓝 d) := by
    have hh := (hlim.comp hPtop).mul hL
    rw [mul_one] at hh
    apply hh.congr'
    filter_upwards [(htop.comp hPtop).eventually (eventually_gt_atTop (0 : ℝ))] with s hs
    have htne := hs.ne'
    dsimp [Function.comp_def] at htne
    dsimp only [Function.comp_def]
    field_simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLF hUF
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact div_le_div_of_nonneg_right (hF (hbracket s hs.le).1) hs.le
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact div_le_div_of_nonneg_right (hF (hI s).le) hs.le

end Interpolation
end EntropyRateDimension

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.RadialLimit ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
open Set Filter
open scoped Topology
namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter
open scoped Topology BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI_3
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI_3
omit [Nonempty ι] in
theorem slope_log_succ (S : System ι) (ω : ℕ → ι) (n : ℕ) :
    -Real.log |slope S ω (n+1)| = -Real.log |slope S ω n| + -Real.log |S.ratio (ω n)| := by
  rw [slope_succ,abs_mul,Real.log_mul (abs_slope_pos S ω n).ne' (S.ratio_pos _).ne',neg_add]

omit [Nonempty ι] in
theorem ratio_log_pos (S : System ι) (i : ι) : 0 < -Real.log |S.ratio i| :=
  neg_pos.mpr (Real.log_neg (S.ratio_pos i) (S.ratio_lt_one i))

theorem radial_limit_of_prefix (S : System ι) (ω : ℕ → ι)
    (hx : point S ω ∈ (law S).support)
    (hlim : Tendsto (fun n => prefixInfo S n ω / -Real.log |slope S ω n|)
      atTop (𝓝 (exponent S))) :
    Tendsto (fun r => BallRatios.information (law S) (point S ω) r / -Real.log r)
      (𝓝[>] 0) (𝓝 (exponent S)) := by
  let F : ℝ → ℝ := fun t => BallRatios.information (law S) (point S ω) (Real.exp (-t))
  let t : ℕ → ℝ := fun n => -Real.log |slope S ω n|
  have hF : Monotone F := by
    intro a b hab
    exact BallRatios.information_antitone _ hx (Real.exp_pos _)
      (Real.exp_le_exp.mpr (neg_le_neg hab))
  have ht : Monotone t := monotone_nat_of_le_succ fun n => by
    dsimp only [t]
    rw [slope_log_succ]
    exact le_add_of_nonneg_right (ratio_log_pos S _).le
  have ht0 : t 0=0 := by simp [t,slope_zero]
  have hstep : ∀ n, t (n+1) ≤ t n + ∑ i, -Real.log |S.ratio i| := by
    intro n
    dsimp only [t]
    rw [slope_log_succ]
    exact add_le_add_right (Finset.single_le_sum (fun i _ => (ratio_log_pos S i).le)
      (Finset.mem_univ (ω n))) _
  have hrtop : Tendsto (fun n => |slope S ω n|) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨slope_tendsto_zero S ω,
      Eventually.of_forall (fun n => abs_slope_pos S ω n)⟩
  have htop : Tendsto t atTop atTop :=
    tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hrtop)
  have hlim' : Tendsto (fun n => F (t n)/t n) atTop (𝓝 (exponent S)) := by
    simpa only [F,t,neg_neg,Real.exp_log (abs_slope_pos S ω _),prefixInfo] using hlim
  have hfull := Interpolation.tendsto_div_of_bounded_gaps hF ht ht0 hstep htop hlim'
  have hlog : Tendsto (fun r : ℝ => -Real.log r) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  apply (hfull.comp hlog).congr'
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  simp only [Function.comp_def,F,neg_neg,Real.exp_log hr]

theorem ae_radial_sequence (S : System ι) : ∀ᵐ x ∂law S,
    Tendsto (fun n : ℕ => BallRatios.information (law S) x (Real.exp (-(n : ℝ))) / (n : ℝ))
      atTop (𝓝 (exponent S)) := by
  have hseq : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝[>] 0) :=
    Real.tendsto_exp_atBot_nhdsGT.comp
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
  have hm (n : ℕ) : Measurable (fun x : ℝ =>
      BallRatios.information (law S) x (Real.exp (-(n : ℝ))) / (n : ℝ)) := by
    have hs : MeasurableSet {z : ℝ × ℝ | dist z.2 z.1 ≤ Real.exp (-(n : ℝ))} :=
      measurableSet_le (measurable_snd.dist measurable_fst) measurable_const
    have hmass := measurable_measure_prodMk_left (ν := law S) hs
    exact hmass.ennreal_toReal.log.neg.div_const _
  apply (ae_map_iff (point_measurable S).aemeasurable (measurableSet_tendsto _ hm)).mpr
  filter_upwards [ae_prefix_exponent S,ae_point_support S] with ω hlim hs
  have hr := (radial_limit_of_prefix S ω (by simpa using hs 0) hlim).comp hseq
  simpa only [Function.comp_def,Real.log_exp,neg_neg] using hr

end EntropyRateDimension.Coding

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.ExactDimension ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
open MeasureTheory Metric Set Filter
open scoped ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology BigOperators
open Set Filter
open scoped Topology
namespace EntropyRateDimension.BallRatios
open MeasureTheory Metric Set Filter
open scoped Topology

theorem radial_limit_of_integer (μ : Measure ℝ) [IsProbabilityMeasure μ] {x d : ℝ}
    (hx : x ∈ μ.support)
    (hlim : Tendsto (fun n : ℕ => information μ x (Real.exp (-(n : ℝ))) / (n : ℝ))
      atTop (𝓝 d)) :
    Tendsto (fun r => information μ x r / -Real.log r) (𝓝[>] 0) (𝓝 d) := by
  let F : ℝ → ℝ := fun s => information μ x (Real.exp (-s))
  have hF : Monotone F := fun a b hab => information_antitone μ hx (Real.exp_pos _)
    (Real.exp_le_exp.mpr (neg_le_neg hab))
  have hfull := Interpolation.tendsto_div_of_bounded_gaps hF Nat.mono_cast (by simp)
    (C := 1) (fun n => by push_cast; exact le_rfl) tendsto_natCast_atTop_atTop hlim
  apply (hfull.comp (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)).congr'
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  simp only [Function.comp_def,F,neg_neg,Real.exp_log hr]

end EntropyRateDimension.BallRatios

namespace EntropyRateDimension.Coding
open MeasureTheory Metric Set Filter
open scoped Topology
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI_4
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI_4
theorem ae_radial_limit (S : System ι) : ∀ᵐ x ∂law S,
    Tendsto (fun r => BallRatios.information (law S) x r / -Real.log r)
      (𝓝[>] 0) (𝓝 (exponent S)) := by
  filter_upwards [ae_radial_sequence S,(law S).support_mem_ae] with x hlim hx
  exact BallRatios.radial_limit_of_integer _ hx hlim

end EntropyRateDimension.Coding

namespace EntropyRateDimension.System
open MeasureEntropy
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.System.instMeasurableSpace
attribute [local instance] OAI.EntropyRateDimension.System.instMeasurableSingletonClass
theorem selfSimilar_radial (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r => -Real.log (μ.real (Metric.closedBall x r)) / -Real.log r)
      (𝓝[>] 0) (𝓝 (Coding.exponent S)) := by
  have he := S.selfSimilar_unique μ (Coding.law S) hμ (Coding.law_selfSimilar S)
  subst μ
  exact Coding.ae_radial_limit S

theorem selfSimilar_entropy_bound (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) {D : ℝ} (hD : Coding.exponent S < D) :
    ∃ C : ℝ, ∀ s : ℝ, 0 < s → s < 1 → averaged μ s ≤ D*Real.log (1/s)+C :=
  entropy_bound_of_radial_limit μ (by obtain ⟨B,hB,hc⟩ := S.selfSimilar_compact μ hμ; exact ⟨B,hB.le,hc⟩)
    (Coding.exponent_nonneg S) hD (S.selfSimilar_radial μ hμ)

end EntropyRateDimension.System

end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.UpperBound ----
namespace OAI

universe uι uM

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

theorem sum_words_cons {M : Type uM} [AddCommMonoid M] {n : ℕ}
    (f : (Fin (n+1) → ι) → M) :
    (∑ w, f w) = ∑ i, ∑ w : Fin n → ι, f (Fin.cons i w) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => ι)).sum_comp f,Fintype.sum_prod_type]
  rfl

theorem completeMap_cons (S : System ι) {n : ℕ} (i : ι) (w : Fin n → ι) :
    S.completeMap (Fin.cons i w) = (S.ratio i*(S.completeMap w).1,
      S.ratio i*(S.completeMap w).2+S.offset i) := by
  simp only [completeMap,List.ofFn_cons,wordAffine]

theorem wordWeight_cons (S : System ι) {n : ℕ} (i : ι) (w : Fin n → ι) :
    S.wordWeight (Fin.cons i w) = S.weight i*S.wordWeight w := by
  simp only [wordWeight,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]

theorem wordMap_cons (S : System ι) {n : ℕ} (i : ι) (w : Fin n → ι) :
    S.wordMap (Fin.cons i w) = S.affine i ∘ S.wordMap w := by
  funext x
  simp only [wordMap,completeMap_cons,affine,Function.comp_apply]
  ring

theorem selfSimilar_words (S : System ι) (μ : Measure ℝ) (hμ : S.SelfSimilar μ) (n : ℕ) :
    μ = ∑ w : Fin n → ι, ENNReal.ofReal (S.wordWeight w) • μ.map (S.wordMap w) := by
  classical
  induction n with
  | zero =>
    have hm : S.wordMap (default : Fin 0 → ι) = id := by
      funext x
      simp [wordMap,completeMap,wordAffine]
    simp [wordWeight,hm]
  | succ n ih =>
    rw [sum_words_cons]
    calc
      μ = ∑ i, ENNReal.ofReal (S.weight i) • μ.map (S.affine i) := hμ
      _ = ∑ i, ∑ w : Fin n → ι,
          ENNReal.ofReal (S.wordWeight (Fin.cons i w)) • μ.map (S.wordMap (Fin.cons i w)) := by
        apply Finset.sum_congr rfl
        intro i _
        conv_lhs => rw [ih]
        rw [Measure.map_finset_sum (S.affine_continuous i).measurable.aemeasurable,Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro w _
        rw [Measure.map_smul _ _ (S.affine i),
          smul_smul,wordWeight_cons,ENNReal.ofReal_mul (S.weight_nonneg i),
          Measure.map_map (S.affine_continuous i).measurable (S.wordMap_measurable w),wordMap_cons]

theorem wordWeight_expect_sum (S : System ι) (f : ι → ℝ) (n : ℕ) :
    (∑ w : Fin n → ι, S.wordWeight w * ∑ j, f (w j)) =
      (n : ℝ)*∑ i, S.weight i*f i := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_words_cons]
    simp only [wordWeight_cons,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,
      mul_add,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,
      S.wordWeight_sum,one_mul,ih,S.weight_sum]
    push_cast
    ring

theorem completeMap_log_slope (S : System ι) {n : ℕ} (w : Fin n → ι) :
    Real.log |(S.completeMap w).1| = ∑ j, Real.log |S.ratio (w j)| := by
  rw [completeMap_slope,Finset.abs_prod,Real.log_prod]
  exact fun j _ => (S.ratio_pos (w j)).ne'

end EntropyRateDimension.System

namespace EntropyRateDimension.Coding
open MeasureTheory
open scoped BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSpace_oAI_5
attribute [local instance] OAI.EntropyRateDimension.Coding.instMeasurableSingletonClass_oAI_5
end EntropyRateDimension.Coding

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.System.instMeasurableSpace_1
attribute [local instance] OAI.EntropyRateDimension.System.instMeasurableSingletonClass_1
end EntropyRateDimension.System

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.Conditioning ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uα uβ

namespace EntropyRateDimension.FairPairs
open MeasureTheory FiniteEntropy
open scoped BigOperators ENNReal

theorem Law.smul_sum_ofObservable {α : Type uα} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 < p a) (hp1 : ∑ a ∈ s, p a=1) (f : α → ℝ)
    (F : ℝ → Measure ℝ) :
    (∑ x : (Law.ofObservable s p hp hp1 f).support,
      ENNReal.ofReal ((Law.ofObservable s p hp hp1 f).prob x) • F x) =
      ∑ a ∈ s, ENNReal.ofReal (p a) • F (f a) := by
  classical
  change (∑ x : s.image f, ENNReal.ofReal (mass s p f x) • F x)=_
  rw [Finset.sum_coe_sort (s.image f) (fun x => ENNReal.ofReal (mass s p f x) • F x)]
  change (∑ x ∈ s.image f, ENNReal.ofReal (mass s p f x) • F x)=_
  simp only [mass,ENNReal.ofReal_sum_of_nonneg (fun a ha => (hp a (Finset.mem_filter.mp ha).1).le),
    Finset.sum_smul]
  calc
    _ = ∑ x ∈ s.image f, ∑ a ∈ s.filter (fun a => f a=x), ENNReal.ofReal (p a) • F (f a) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem f ha) _

end EntropyRateDimension.FairPairs

namespace EntropyRateDimension.FiniteCondition
open FiniteEntropy FairPairs MeasureTheory
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem mass_eq_of_tag (p : α → ℝ) (tag : α → β) {a v : α} (h : tag a=tag v) :
    mass p tag a=mass p tag v := by simp only [mass,fiber,h]

theorem posterior_uncondition (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (v : α) :
    ∑ a, p a*posterior p tag a v=p v := by
  classical
  have he : ∀ a, p a*posterior p tag a v=
      if tag a=tag v then p a*p v/mass p tag v else 0 := by
    intro a
    by_cases h : tag a=tag v
    · simp only [posterior,ite_eq_left h.symm,ite_eq_left h,mass_eq_of_tag p tag h]
      ring
    · simp [posterior,h,Ne.symm h]
  simp_rw [he]
  rw [← Finset.sum_filter,← Finset.sum_div,← Finset.sum_mul]
  change mass p tag v*p v/mass p tag v=p v
  exact mul_div_cancel_left₀ _ (mass_pos p hp tag v).ne'

theorem law_entropy_mean (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (f : α → ℝ) :
    (∑ a, p a*(law p hp tag a f).shannonEntropy)*Real.log 2=
      FiniteEntropy.conditionalEntropy Finset.univ p f tag := by
  classical
  simp only [law,Law.ofObservable_entropy,← mul_div_assoc,← Finset.sum_div,
    div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne']
  rw [conditionalEntropy_eq_sum _ _ _ _ (fun a _ => (hp a).le)]
  symm
  convert FiniteEntropy.sum_mass_mul Finset.univ (Finset.univ.image tag) p tag
    (fun c => observableEntropy (Finset.univ.filter (fun a => tag a=c))
      (fun a => p a/FiniteEntropy.mass Finset.univ p tag c) f)
    (fun a ha => Finset.mem_image_of_mem tag ha) using 1
  rfl

theorem law_smul_sum (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (a : α)
    (f : α → ℝ) (F : ℝ → Measure ℝ) :
    (∑ x : (law p hp tag a f).support, ENNReal.ofReal ((law p hp tag a f).prob x) • F x)=
      ∑ v, ENNReal.ofReal (posterior p tag a v) • F (f v) := by
  classical
  rw [law,Law.smul_sum_ofObservable]
  simp only [posterior,apply_ite ENNReal.ofReal,ENNReal.ofReal_zero,ite_smul,zero_smul,
    ← Finset.sum_filter]
  rfl

theorem posterior_smul_uncondition (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β)
    (F : α → Measure ℝ) :
    (∑ a, ENNReal.ofReal (p a) • ∑ v, ENNReal.ofReal (posterior p tag a v) • F v)=
      ∑ v, ENNReal.ofReal (p v) • F v := by
  simp only [Finset.smul_sum,smul_smul,← ENNReal.ofReal_mul (hp _).le]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Finset.sum_smul,← ENNReal.ofReal_sum_of_nonneg
    (fun a _ => mul_nonneg (hp a).le (posterior_nonneg p hp tag a v)),posterior_uncondition p hp tag]

end EntropyRateDimension.FiniteCondition

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.PairGain ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.MeasureEntropy
open MeasureTheory
open scoped BigOperators ENNReal

theorem CompactlyCarried.shiftLaw {μ : Measure ℝ} (hμ : CompactlyCarried μ) (b : ℝ) :
    CompactlyCarried (shiftLaw μ b) := by simpa only [one_mul,MeasureEntropy.shiftLaw] using hμ.map_affine 1 b

theorem window_shiftLaw (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (b : ℝ) :
    window (shiftLaw μ b) s t = window μ s t := by
  simp only [window,shiftLaw,averaged_translate μ hμ hs,averaged_translate μ hμ ht]

theorem CompactlyCarried.pairLaw {μ : Measure ℝ} (hμ : CompactlyCarried μ) (x y : ℝ) :
    CompactlyCarried (pairLaw μ x y) := by
  have hh := CompactlyCarried.mixture (fun i : Fin 2 => MeasureEntropy.shiftLaw μ (if i=0 then x else y))
    (fun i => hμ.shiftLaw _) (fun _ => (1/2 : ℝ))
  simpa [Fin.sum_univ_two,MeasureEntropy.pairLaw] using hh

theorem pairLaw_comm (μ : Measure ℝ) (x y : ℝ) : pairLaw μ x y=pairLaw μ y x := add_comm _ _

theorem pairLaw_eq_shift_fair (μ : Measure ℝ) (x y : ℝ) :
    pairLaw μ x y = shiftLaw (fairShift μ (y-x)) x := by
  simp only [pairLaw,shiftLaw,fairShift,Fin.sum_univ_two,Fin.val_zero,Fin.val_one,
    Nat.cast_zero,Nat.cast_one,zero_mul,one_mul,add_zero]
  rw [Measure.map_add _ _ (by fun_prop),
    Measure.map_smul (f := fun z : ℝ => z+x) _ _,
    Measure.map_smul (f := fun z : ℝ => z+x) _ _,
    Measure.map_map (g := fun z : ℝ => z+x) (f := fun z : ℝ => z) (by fun_prop) (by fun_prop),
    Measure.map_map (g := fun z : ℝ => z+x) (f := fun z : ℝ => z+(y-x)) (by fun_prop) (by fun_prop)]
  have he : (fun z : ℝ => z+x) ∘ (fun z => z+(y-x))=(fun z => z+y) := by
    funext z; simp; ring
  rw [he]
  rfl

theorem pairLaw_gain (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    {s t x y : ℝ} (hs : 0 < s) (hsv : s < |y-x|) (hvt : |y-x| < t) :
    deficit μ |y-x|-(s/|y-x|+|y-x|/t)*Real.log 2 ≤
      window (pairLaw μ x y) s t-window μ s t := by
  have hv : 0 < |y-x| := hs.trans hsv
  have ht : 0 < t := hv.trans hvt
  let (v : ℝ) : IsProbabilityMeasure (fairShift μ v) := fairShift_probability μ v
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonneg (sub_nonneg.mpr hxy)] at *
    rw [pairLaw_eq_shift_fair,window_shiftLaw _ (hμ.fairShift _) hs ht]
    exact two_point_gain μ hμ hs hsv hvt
  · have he : |y-x|=x-y := by rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hyx)]
    have hsv' : s < x-y := he ▸ hsv
    have hvt' : x-y < t := he ▸ hvt
    rw [he,pairLaw_comm,pairLaw_eq_shift_fair,window_shiftLaw _ (hμ.fairShift _) hs ht]
    exact two_point_gain μ hμ hs hsv' hvt'

theorem CompactlyCarried.finiteConv {μ : Measure ℝ} (hμ : CompactlyCarried μ)
    (ν : FairPairs.Law) (a : ℝ) : CompactlyCarried (finiteConv ν a μ) :=
  CompactlyCarried.mixture _ (fun _ => hμ.shiftLaw _) _

theorem finiteConv_window_mono (ν : FairPairs.Law) (a : ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) :
    window μ s (N*s) ≤ window (finiteConv ν a μ) s (N*s) :=
  averaged_nested_translate_mixture μ hμ (fun x : ν.support => ν.prob x)
    (fun x => (ν.prob_pos x x.property).le) ν.subtype_sum (fun x => a*x) hs hN

theorem deficit_mixture {α : Type uα} [Fintype α]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (ν : α → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : ∀ i, CompactlyCarried (ν i))
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1)
    (hm : μ=∑ i, ENNReal.ofReal (p i) • ν i) {v : ℝ} (hv : 0 < v) :
    deficit μ v ≤ ∑ i, p i*deficit (ν i) v := by
  have hh := averaged_nested_mixture μ hμ ν hν p hp hm hv (by norm_num : 0 < (2 : ℕ))
  simp only [deficit,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hp1,one_mul]
  push_cast at hh
  simp only [mul_sub,Finset.sum_sub_distrib] at hh
  linarith

theorem deficit_scale (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    {v a : ℝ} (hv : 0 < v) (ha : a ≠ 0) :
    deficit (μ.map (fun x => a*x)) v=deficit μ (v/|a|) := by
  rw [deficit,averaged_scale μ hμ hv ha,averaged_scale μ hμ (by positivity) ha,deficit]
  congr 2
  ring_nf

end EntropyRateDimension.MeasureEntropy

namespace EntropyRateDimension.FairPairs
open MeasureTheory MeasureEntropy
open scoped BigOperators ENNReal

theorem incident_smul_sum (ν : Law) (ℓ : ℤ) (w : ν.edges ℓ → ℝ) (hw : ∀ e, 0 ≤ w e)
    (f : ℝ → Measure ℝ) :
    (∑ x ∈ ν.support, ENNReal.ofReal (incident w x) • f x) =
      ∑ e, (ENNReal.ofReal (w e/2) • f e.val.1+ENNReal.ofReal (w e/2) • f e.val.2) := by
  classical
  have hw2 : ∀ e, 0 ≤ w e/2 := fun e => div_nonneg (hw e) (by norm_num)
  have hv : ∀ x e, 0 ≤ (if e.val.1=x then w e/2 else 0)+(if e.val.2=x then w e/2 else 0) := by
    intro x e
    have hwe := hw2 e
    split_ifs <;> positivity
  simp only [incident,ENNReal.ofReal_sum_of_nonneg (fun e _ => hv _ e),Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have hh : ∀ x, ENNReal.ofReal ((if e.val.1=x then w e/2 else 0)+
      (if e.val.2=x then w e/2 else 0)) • f x =
      (if e.val.1=x then ENNReal.ofReal (w e/2) • f e.val.1 else 0)+
      (if e.val.2=x then ENNReal.ofReal (w e/2) • f e.val.2 else 0) := by
    intro x
    have hwe := hw2 e
    rw [ENNReal.ofReal_add (by split_ifs <;> positivity) (by split_ifs <;> positivity)]
    rw [add_smul]
    congr 1 <;> split_ifs <;> simp_all only [ENNReal.ofReal_zero,zero_smul]
  simp_rw [hh,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq,edge_mem_left e,edge_mem_right e,ite_true]

theorem residual_nonneg {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w)
    (x : ν.support) : 0 ≤ residual w x := sub_nonneg.mpr (hw.2 x x.property)

theorem residual_total {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) :
    (∑ x : ν.support, residual w x)+(∑ e, w e)=1 := by
  classical
  simp only [residual,Finset.sum_sub_distrib,ν.subtype_sum,
    Finset.sum_coe_sort ν.support (fun x => incident w x),incident_sum]
  ring

theorem decompositionWeight_nonneg {ν : Law} {ℓ : ℤ} {w : ν.edges ℓ → ℝ} (hw : Feasible w) :
    ∀ z, 0 ≤ decompositionWeight w z := by
  intro z
  cases z with
  | inl e => exact hw.1 e
  | inr x => exact residual_nonneg hw x

theorem decompositionWeight_sum {ν : Law} {ℓ : ℤ} (w : ν.edges ℓ → ℝ) :
    ∑ z, decompositionWeight w z=1 := by
  rw [Fintype.sum_sum_type]
  exact (add_comm _ _).trans (residual_total w)

theorem decompositionLaw_compact {ν : Law} {ℓ : ℤ} (μ : Measure ℝ) (hμ : CompactlyCarried μ)
    (a : ℝ) (z : ν.edges ℓ ⊕ ν.support) : CompactlyCarried (decompositionLaw μ a z) := by
  cases z with
  | inl e => exact hμ.pairLaw _ _
  | inr x => exact hμ.shiftLaw _

theorem finiteConv_decomposition (ν : Law) (ℓ : ℤ) (w : ν.edges ℓ → ℝ) (hw : Feasible w)
    (μ : Measure ℝ) (a : ℝ) :
    finiteConv ν a μ = ∑ z, ENNReal.ofReal (decompositionWeight w z) • decompositionLaw μ a z := by
  classical
  rw [Fintype.sum_sum_type]
  change finiteConv ν a μ=(∑ e, ENNReal.ofReal (w e) • pairLaw μ (a*e.val.1) (a*e.val.2))+
    ∑ x : ν.support, ENNReal.ofReal (residual w x) • shiftLaw μ (a*x)
  have he : ∀ e : ν.edges ℓ, ENNReal.ofReal (w e) • pairLaw μ (a*e.val.1) (a*e.val.2)=
      ENNReal.ofReal (w e/2) • shiftLaw μ (a*e.val.1)+
      ENNReal.ofReal (w e/2) • shiftLaw μ (a*e.val.2) := by
    intro e
    simp only [pairLaw,smul_add,smul_smul,← ENNReal.ofReal_mul (hw.1 e)]
    congr 2 <;> congr 1 <;> ring
  simp_rw [he]
  rw [← incident_smul_sum ν ℓ w hw.1 (fun x => shiftLaw μ (a*x)),← Finset.sum_coe_sort ν.support (fun x =>
    ENNReal.ofReal (incident w x) • shiftLaw μ (a*x)),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hi : 0 ≤ incident w x := by
    apply Finset.sum_nonneg
    intro e _
    have hre := hw.1 e
    split_ifs <;> positivity
  rw [← add_smul,← ENNReal.ofReal_add hi (residual_nonneg hw x)]
  simp only [residual,add_sub_cancel]

end EntropyRateDimension.FairPairs

namespace EntropyRateDimension.MeasureEntropy
open MeasureTheory FairPairs
open scoped BigOperators ENNReal

theorem finiteConv_gain (ν : FairPairs.Law) (a : ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ) {ℓ : ℤ}
    (w : ν.edges ℓ → ℝ) (hw : FairPairs.Feasible w)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N)
    (hv : ∀ e : ν.edges ℓ, s < |a*e.val.2-a*e.val.1| ∧ |a*e.val.2-a*e.val.1| < N*s) :
    (∑ e, w e*(deficit μ |a*e.val.2-a*e.val.1|-
      (s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2)) ≤
      window (finiteConv ν a μ) s (N*s)-window μ s (N*s) := by
  classical
  have ht : 0 < (N : ℝ)*s := mul_pos (by exact_mod_cast hN) hs
  have hh := averaged_nested_mixture (finiteConv ν a μ) (hμ.finiteConv ν a)
    (decompositionLaw (ν := ν) (ℓ := ℓ) μ a) (decompositionLaw_compact μ hμ a)
    (decompositionWeight w) (decompositionWeight_nonneg hw)
    (finiteConv_decomposition ν ℓ w hw μ a) hs hN
  change (∑ z, decompositionWeight w z*window (decompositionLaw μ a z) s (N*s)) ≤ _ at hh
  have hid : (∑ z, decompositionWeight w z*window (decompositionLaw μ a z) s (N*s))-
      window μ s (N*s) =
      ∑ e, w e*(window (pairLaw μ (a*e.val.1) (a*e.val.2)) s (N*s)-window μ s (N*s)) := by
    calc
      _ = (∑ z, decompositionWeight w z*window (decompositionLaw μ a z) s (N*s))-
          ∑ z, decompositionWeight w z*window μ s (N*s) := by
        rw [← Finset.sum_mul,decompositionWeight_sum,one_mul]
      _ = ∑ z, decompositionWeight w z*(window (decompositionLaw μ a z) s (N*s)-
          window μ s (N*s)) := by simp only [mul_sub,Finset.sum_sub_distrib]
      _ = _ := by
        rw [Fintype.sum_sum_type]
        simp only [decompositionWeight,decompositionLaw,Sum.elim_inl,Sum.elim_inr,
          window_shiftLaw μ hμ hs ht,sub_self,mul_zero,Finset.sum_const_zero,add_zero]
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun (e : ν.edges ℓ) _ =>
    mul_le_mul_of_nonneg_left (pairLaw_gain μ hμ hs (hv e).1 (hv e).2) (hw.1 e))
  rw [← hid] at hl
  exact hl.trans (sub_le_sub_right hh _)

theorem finiteConv_mean_gain {β : Type uβ} [Fintype β]
    (ν : FairPairs.Law) (a b : ℝ) (hb : b ≠ 0)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    (τ : β → Measure ℝ) [∀ z, IsProbabilityMeasure (τ z)]
    (hτ : ∀ z, CompactlyCarried (τ z))
    (p : β → ℝ) (hp : ∀ z, 0 ≤ p z) (hp1 : ∑ z, p z=1)
    (hm : μ.map (fun x => b*x) = ∑ z, ENNReal.ofReal (p z) • τ z)
    {δ η s : ℝ} (hδ : ∀ v, 0 < v → δ ≤ deficit μ v) (hs : 0 < s)
    {N : ℕ} (hN : 0 < N) (ℓ : ℤ)
    (hv : ∀ e : ν.edges ℓ, s < |a*e.val.2-a*e.val.1| ∧ |a*e.val.2-a*e.val.1| < N*s)
    (herr : ∀ e : ν.edges ℓ,
      (s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2 ≤ η) :
    (δ-η)*FairPairs.capacity ν ℓ ≤
      ∑ z, p z*(window (finiteConv ν a (τ z)) s (N*s)-window (τ z) s (N*s)) := by
  classical
  obtain ⟨w,hw,he⟩ := FairPairs.capacity_attained ν ℓ
  let : IsProbabilityMeasure (μ.map (fun x => b*x)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_const.mul measurable_id).aemeasurable).2 inferInstance
  have hmcomp : CompactlyCarried (μ.map (fun x => b*x)) := by
    simpa only [add_zero] using hμ.map_affine b 0
  have hdef (e : ν.edges ℓ) : δ ≤ ∑ z, p z*deficit (τ z) |a*e.val.2-a*e.val.1| := by
    have hpv := hs.trans (hv e).1
    have hd := deficit_mixture (μ.map (fun x => b*x)) hmcomp τ hτ p hp hp1 hm hpv
    rw [deficit_scale μ hμ hpv hb] at hd
    exact (hδ _ (div_pos hpv (abs_pos.mpr hb))).trans hd
  have hz (z : β) := finiteConv_gain ν a (τ z) (hτ z) w hw hs hN hv
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hz z) (hp z))
  simp_rw [Finset.mul_sum] at hsum
  rw [Finset.sum_comm] at hsum
  have hlo : (δ-η)*FairPairs.capacity ν ℓ ≤
      ∑ e, ∑ z, p z*(w e*(deficit (τ z) |a*e.val.2-a*e.val.1|-
        (s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2)) := by
    rw [← he,mul_comm,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro e _
    have hh : ∑ z, p z*(w e*(deficit (τ z) |a*e.val.2-a*e.val.1|-
        (s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2)) =
        w e*((∑ z, p z*deficit (τ z) |a*e.val.2-a*e.val.1|)-
        (s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2) := by
      simp_rw [show ∀ z, p z*(w e*(deficit (τ z) |a*e.val.2-a*e.val.1|-
        (s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2)) =
        w e*(p z*deficit (τ z) |a*e.val.2-a*e.val.1|)-
        w e*p z*((s/|a*e.val.2-a*e.val.1|+|a*e.val.2-a*e.val.1|/(N*s))*Real.log 2) by intro z; ring]
      rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,← Finset.mul_sum,hp1]
      ring
    rw [hh]
    exact mul_le_mul_of_nonneg_left (sub_le_sub (hdef e) (herr e)) (hw.1 e)
  exact hlo.trans hsum

end EntropyRateDimension.MeasureEntropy

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.TypedLaw ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ uγ uM

namespace EntropyRateDimension.FiniteCondition
open scoped BigOperators ENNReal
open MeasureTheory

theorem mass_pi {α : Type uα} {β : Type uβ} {γ : Type uγ} [Fintype α] [Fintype γ] [DecidableEq γ] [DecidableEq β]
    (p : α → ℝ) (tag : α → β) (w : γ → α) :
    mass (fun v : γ → α => ∏ j, p (v j)) (fun v j => tag (v j)) w =
      ∏ j, mass p tag (w j) := by
  classical
  simp only [mass,fiber,Finset.sum_filter]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : (fun j => tag (v j))=(fun j => tag (w j))
  · simp only [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro j _
    rw [ite_eq_left (congrFun h j)]
  · rw [ite_eq_right h]
    symm
    obtain ⟨j,hj⟩ : ∃ j, tag (v j)≠tag (w j) := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

theorem posterior_pi {α : Type uα} {β : Type uβ} {γ : Type uγ} [Fintype α] [Fintype γ] [DecidableEq γ] [DecidableEq β]
    (p : α → ℝ) (tag : α → β) (w v : γ → α) :
    posterior (fun u : γ → α => ∏ j, p (u j)) (fun u j => tag (u j)) w v =
      ∏ j, posterior p tag (w j) (v j) := by
  classical
  rw [posterior,mass_pi]
  by_cases h : (fun j => tag (v j))=(fun j => tag (w j))
  · rw [ite_eq_left h,← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [posterior,ite_eq_left (congrFun h j)]
  · rw [ite_eq_right h]
    symm
    obtain ⟨j,hj⟩ : ∃ j, tag (v j)≠tag (w j) := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [posterior,ite_eq_right hj])

end EntropyRateDimension.FiniteCondition

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

theorem sum_words_append {M : Type uM} [AddCommMonoid M] (m n : ℕ)
    (f : (Fin (m+n) → ι) → M) :
    (∑ w, f w)=∑ u : Fin m → ι, ∑ v : Fin n → ι, f (Fin.append u v) := by
  classical
  rw [← (Fin.appendEquiv m n).sum_comp f,Fintype.sum_prod_type]
  rfl

theorem completeMap_append (S : System ι) {m n : ℕ} (u : Fin m → ι) (v : Fin n → ι) :
    S.completeMap (Fin.append u v)=
      ((S.completeMap u).1*(S.completeMap v).1,
        (S.completeMap u).1*(S.completeMap v).2+(S.completeMap u).2) := by
  simp only [completeMap,List.ofFn_fin_append,wordAffine_append]

theorem wordWeight_append (S : System ι) {m n : ℕ} (u : Fin m → ι) (v : Fin n → ι) :
    S.wordWeight (Fin.append u v)=S.wordWeight u*S.wordWeight v := by
  simp only [wordWeight,Fin.prod_univ_add,Fin.append_left,Fin.append_right]

theorem wordMap_append (S : System ι) {m n : ℕ} (u : Fin m → ι) (v : Fin n → ι) :
    S.wordMap (Fin.append u v)=S.wordMap u ∘ S.wordMap v := by
  funext x
  simp only [wordMap,completeMap_append,Function.comp_apply]
  ring

end EntropyRateDimension.System

namespace EntropyRateDimension.Typed
open MeasureTheory FairPairs FiniteCondition
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem prob_as_posterior (S : System α) (tag : α → β) {n : ℕ} (w v : Fin n → α) :
    prob S tag w v=posterior S.wordWeight (tagWord tag) w v :=
  (posterior_pi S.weight tag w v).symm

theorem prob_append (S : System α) (tag : α → β) {m n : ℕ}
    (w u : Fin m → α) (z v : Fin n → α) :
    prob S tag (Fin.append w z) (Fin.append u v)=prob S tag w u*prob S tag z v := by
  simp only [prob,Fin.prod_univ_add,Fin.append_left,Fin.append_right]

theorem prob_slope (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    {n : ℕ} {w v : Fin n → α} (h : prob S tag w v≠0) :
    (S.completeMap v).1=(S.completeMap w).1 := by
  rw [S.completeMap_slope,S.completeMap_slope]
  apply Finset.prod_congr rfl
  intro j hj
  apply hr
  by_contra ht
  apply h
  apply Finset.prod_eq_zero hj
  exact ite_eq_right ht

theorem tail_compact (S : System α) (tag : α → β) (μ : Measure ℝ)
    (hμ : MeasureEntropy.CompactlyCarried μ) {n : ℕ} (w : Fin n → α) :
    MeasureEntropy.CompactlyCarried (tail S tag μ w) := by
  apply MeasureEntropy.CompactlyCarried.mixture
  intro v
  exact hμ.map_affine _ _

theorem tail_mean (S : System α) (tag : α → β) (μ : Measure ℝ)
    (hμ : S.SelfSimilar μ) (n : ℕ) :
    (∑ w : Fin n → α, ENNReal.ofReal (S.wordWeight w) • tail S tag μ w)=μ := by
  simp only [tail,prob_as_posterior]
  rw [posterior_smul_uncondition S.wordWeight (fun v => S.wordWeight_pos v)]
  exact (S.selfSimilar_words μ hμ n).symm

theorem tail_append (S : System α) (tag : α → β) (μ : Measure ℝ)
    {m n : ℕ} (w : Fin m → α) (z : Fin n → α) :
    tail S tag μ (Fin.append w z)=tail S tag (tail S tag μ z) w := by
  classical
  rw [tail,System.sum_words_append]
  simp only [tail]
  apply Finset.sum_congr rfl
  intro u _
  rw [Measure.map_finset_sum (S.wordMap_measurable u).aemeasurable,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro v _
  rw [prob_append,ENNReal.ofReal_mul (prob_nonneg S tag w u),
    Measure.map_smul _ _ (S.wordMap u),smul_smul,
    Measure.map_map (S.wordMap_measurable u) (S.wordMap_measurable v),S.wordMap_append]

end EntropyRateDimension.Typed

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.TailConvolution ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs FiniteCondition
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem scaledTail_compact (S : System α) (tag : α → β) (μ : Measure ℝ)
    (hμ : CompactlyCarried μ) (a : ℝ) {n : ℕ} (w : Fin n → α) :
    CompactlyCarried (scaledTail S tag μ a w) := by
  simpa only [scaledTail,add_zero] using (tail_compact S tag μ hμ w).map_affine a 0

theorem scaledTail_mean (S : System α) (tag : α → β) (μ : Measure ℝ)
    (hμ : S.SelfSimilar μ) (a : ℝ) (n : ℕ) :
    (∑ w : Fin n → α, ENNReal.ofReal (S.wordWeight w) • scaledTail S tag μ a w)=
      μ.map (fun x => a*x) := by
  calc
    _ = (∑ w : Fin n → α, ENNReal.ofReal (S.wordWeight w) • tail S tag μ w).map
        (fun x => a*x) := by
      rw [Measure.map_finset_sum (show AEMeasurable (fun x : ℝ => a*x) _ from
        (measurable_const.mul measurable_id).aemeasurable)]
      simp only [Measure.map_smul (f := fun x : ℝ => a*x),scaledTail]
    _ = _ := by rw [tail_mean S tag μ hμ n]

theorem scaled_tail_convolution (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) (a : ℝ) {n : ℕ} (w : Fin n → α) :
    scaledTail S tag μ a w =
      finiteConv (law S tag w) a (μ.map (fun x => (a*(S.completeMap w).1)*x)) := by
  classical
  have he := law_smul_sum S.wordWeight (fun v : Fin n → α => S.wordWeight_pos v)
    (tagWord tag) w (fun v => (S.completeMap v).2)
    (fun x => shiftLaw (μ.map (fun y => (a*(S.completeMap w).1)*y)) (a*x))
  change finiteConv (law S tag w) a (μ.map (fun x => (a*(S.completeMap w).1)*x)) = _ at he
  rw [he]
  unfold scaledTail tail
  rw [Measure.map_finset_sum (show AEMeasurable (fun x : ℝ => a*x) _ from
    (measurable_const.mul measurable_id).aemeasurable)]
  simp only [Measure.map_smul (f := fun x : ℝ => a*x)]
  apply Finset.sum_congr rfl
  intro v _
  rw [← prob_as_posterior]
  by_cases h : prob S tag w v=0
  · simp only [h,ENNReal.ofReal_zero,zero_smul]
  · rw [shiftLaw,Measure.map_map (show Measurable (fun x : ℝ => a*x) from
        measurable_const.mul measurable_id) (S.wordMap_measurable v),
      Measure.map_map (show Measurable (fun x : ℝ => x+a*(S.completeMap v).2) from
        measurable_id.add_const _) (show Measurable
        (fun x : ℝ => (a*(S.completeMap w).1)*x) from measurable_const.mul measurable_id)]
    congr 2
    funext x
    simp only [Function.comp_apply,System.wordMap,prob_slope S tag hr h]
    ring

theorem scaledTail_append (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) (a : ℝ) {m n : ℕ} (w : Fin m → α) (z : Fin n → α) :
    scaledTail S tag μ a (Fin.append w z)=
      finiteConv (law S tag w) a (scaledTail S tag μ (a*(S.completeMap w).1) z) := by
  change (tail S tag μ (Fin.append w z)).map (fun x => a*x)=_
  rw [tail_append]
  exact scaled_tail_convolution S tag hr _ a w

end EntropyRateDimension.Typed

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteVariance ----
namespace OAI

universe uα

namespace EntropyRateDimension.System
open scoped BigOperators
variable {α : Type uα} [Fintype α]

theorem wordWeight_square_sum (S : System α) (f : α → ℝ)
    (hf : ∑ a, S.weight a*f a=0) (n : ℕ) :
    (∑ w : Fin n → α, S.wordWeight w*(∑ j, f (w j))^2)=
      (n : ℝ)*∑ a, S.weight a*(f a)^2 := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
    have hmean := S.wordWeight_expect_sum f n
    rw [hf,mul_zero] at hmean
    rw [sum_words_cons]
    simp only [wordWeight_cons,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,add_sq]
    simp_rw [mul_add]
    have ha : (∑ a, ∑ w : Fin n → α, S.weight a*S.wordWeight w*(f a)^2)=
        ∑ a, S.weight a*(f a)^2 := by
      apply Finset.sum_congr rfl
      intro a _
      simp_rw [mul_right_comm (S.weight a)]
      rw [← Finset.mul_sum,S.wordWeight_sum,mul_one]
    have hb : (∑ a, ∑ w : Fin n → α,
        S.weight a*S.wordWeight w*(2*f a*∑ j, f (w j)))=0 := by
      apply Finset.sum_eq_zero
      intro a _
      have he (w : Fin n → α) :
          S.weight a*S.wordWeight w*(2*f a*∑ j, f (w j))=
            (2*S.weight a*f a)*(S.wordWeight w*∑ j, f (w j)) := by ring
      simp only [he,← Finset.mul_sum,hmean,mul_zero]
    have hc : (∑ a, ∑ w : Fin n → α,
        S.weight a*S.wordWeight w*(∑ j, f (w j))^2)=
          (n : ℝ)*∑ a, S.weight a*(f a)^2 := by
      simp only [mul_assoc,← Finset.mul_sum,ih,← Finset.sum_mul,S.weight_sum,one_mul]
    simp_rw [Finset.sum_add_distrib]
    rw [ha,hb,hc]
    push_cast
    ring

theorem wordDepth_sum (S : System α) {n : ℕ} (w : Fin n → α) :
    S.wordDepth w=∑ j, S.letterDepth (w j) := by
  simp only [wordDepth,letterDepth,S.completeMap_log_slope,← Finset.sum_div,← Finset.sum_neg_distrib]

theorem letterDepth_mean (S : System α) :
    ∑ a, S.weight a*S.letterDepth a=S.lyapunov := by
  simp only [letterDepth,lyapunov,neg_div,mul_neg,Finset.sum_neg_distrib]

theorem letterDepth_pos (S : System α) (a : α) : 0 < S.letterDepth a :=
  div_pos (neg_pos.mpr (Real.log_neg (S.ratio_pos a) (S.ratio_lt_one a)))
    (Real.log_pos (by norm_num))

theorem wordDepth_centered_square (S : System α) (n : ℕ) :
    (∑ w : Fin n → α, S.wordWeight w*(S.wordDepth w-n*S.lyapunov)^2)=
      (n : ℝ)*S.depthVariance := by
  have hf : ∑ a, S.weight a*(S.letterDepth a-S.lyapunov)=0 := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,S.weight_sum,one_mul,S.letterDepth_mean,sub_self]
  have he (w : Fin n → α) : (∑ j, (S.letterDepth (w j)-S.lyapunov))=
      S.wordDepth w-n*S.lyapunov := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,S.wordDepth_sum]
  simpa only [he,depthVariance] using S.wordWeight_square_sum (fun a => S.letterDepth a-S.lyapunov) hf n

theorem depth_bad_mass_bound (S : System α) {A : ℝ} (hA : S.lyapunov < A)
    {n : ℕ} (hn : 0 < n) :
    (∑ w : Fin n → α, if A*n < S.wordDepth w then S.wordWeight w else 0) ≤
      S.depthVariance/((n : ℝ)*(A-S.lyapunov)^2) := by
  classical
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hd : 0 < A-S.lyapunov := sub_pos.mpr hA
  have hh : (∑ w : Fin n → α, if A*n < S.wordDepth w then S.wordWeight w else 0)*
      ((n : ℝ)*(A-S.lyapunov))^2 ≤ (n : ℝ)*S.depthVariance := by
    rw [← S.wordDepth_centered_square,Finset.sum_mul]
    apply Finset.sum_le_sum
    intro w _
    split_ifs with h
    · have ht : (n : ℝ)*(A-S.lyapunov) < S.wordDepth w-n*S.lyapunov := by nlinarith
      exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (mul_pos hnR hd).le ((mul_pos hnR hd).le.trans ht.le)).mpr ht.le)
        (S.wordWeight_pos w).le
    · simp only [zero_mul]
      exact mul_nonneg (S.wordWeight_pos w).le (sq_nonneg _)
  apply (le_div_iff₀ (mul_pos hnR (sq_pos_of_pos hd))).mpr
  have he : (∑ w : Fin n → α, if A*n < S.wordDepth w then S.wordWeight w else 0)*
      ((n : ℝ)*(A-S.lyapunov))^2 =
      (n : ℝ)*((∑ w : Fin n → α, if A*n < S.wordDepth w then S.wordWeight w else 0)*
        ((n : ℝ)*(A-S.lyapunov)^2)) := by ring
  rw [he] at hh
  exact (mul_le_mul_iff_right₀ hnR).mp hh

end EntropyRateDimension.System

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.SuffixLaw ----
namespace OAI

universe uα uβ uγ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

omit [Fintype α] [DecidableEq β] in
theorem apply_word_congr {γ : Type uγ} (F : (n : ℕ) → (Fin n → α) → γ)
    {m n : ℕ} (h : m=n) (v : Fin m → α) (w : Fin n → α)
    (he : ∀ i, v i=w (Fin.cast h i)) : F m v=F n w := by
  subst n
  exact congrArg (F m) (funext he)

theorem listLaw_ofFn (S : System α) (tag : α → β) {n : ℕ} (w : Fin n → α) :
    listLaw S tag (List.ofFn w)=law S tag w := by
  apply apply_word_congr (fun _ v => law S tag v) (List.length_ofFn ..)
  intro i
  simp only [List.get_eq_getElem,List.getElem_ofFn]
  rfl

theorem listTail_ofFn (S : System α) (tag : α → β) (μ : Measure ℝ) {n : ℕ} (w : Fin n → α) :
    listTail S tag μ (List.ofFn w)=tail S tag μ w := by
  apply apply_word_congr (fun _ v => tail S tag μ v) (List.length_ofFn ..)
  intro i
  simp only [List.get_eq_getElem,List.getElem_ofFn]
  rfl

theorem listScaledTail_ofFn (S : System α) (tag : α → β) (μ : Measure ℝ)
    (a : ℝ) {n : ℕ} (w : Fin n → α) :
    listScaledTail S tag μ a (List.ofFn w)=scaledTail S tag μ a w := by
  simp only [listScaledTail,listTail_ofFn,scaledTail]

theorem listScaledTail_compact (S : System α) (tag : α → β) (μ : Measure ℝ)
    (hμ : CompactlyCarried μ) (a : ℝ) (W : List α) :
    CompactlyCarried (listScaledTail S tag μ a W) := scaledTail_compact S tag μ hμ a W.get

theorem listScaledTail_append (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) (a : ℝ) (U V : List α) :
    listScaledTail S tag μ a (U++V)=
      finiteConv (listLaw S tag U) a (listScaledTail S tag μ (a*(S.wordAffine U).1) V) := by
  have h := scaledTail_append S tag hr μ a U.get V.get
  rw [← listScaledTail_ofFn,← listScaledTail_ofFn,← listLaw_ofFn] at h
  simpa only [List.ofFn_fin_append,List.ofFn_get,System.completeMap] using h

theorem suffixLaw_compact (S : System α) (tag : α → β) (μ : Measure ℝ)
    (hμ : CompactlyCarried μ) (W : List α) (j : ℕ) : CompactlyCarried (suffixLaw S tag μ W j) :=
  listScaledTail_compact S tag μ hμ _ _

theorem suffixLaw_convolution (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) (W : List α) (j n : ℕ) :
    suffixLaw S tag μ W j=finiteConv (listLaw S tag ((W.drop j).take n))
      (S.wordAffine (W.take j)).1 (suffixLaw S tag μ W (j+n)) := by
  have h := listScaledTail_append S tag hr μ (S.wordAffine (W.take j)).1
    ((W.drop j).take n) ((W.drop j).drop n)
  rw [List.take_append_drop,List.drop_drop] at h
  simpa only [suffixLaw,List.take_add,System.wordAffine_append] using h

theorem suffixWindow_antitone (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) (W : List α) :
    Antitone (suffixWindow S tag μ s N W) := by
  intro j k hjk
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hjk
  change window (suffixLaw S tag μ W (j+n)) s (N*s) ≤ window (suffixLaw S tag μ W j) s (N*s)
  rw [suffixLaw_convolution S tag hr μ W j n]
  exact finiteConv_window_mono _ _ _ (suffixLaw_compact S tag μ hμ W (j+n)) hs hN

theorem suffixWindow_bounds (S : System α) (tag : α → β)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : CompactlyCarried μ)
    {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N) (W : List α) (j : ℕ) :
    0 ≤ suffixWindow S tag μ s N W j ∧ suffixWindow S tag μ s N W j ≤ Real.log N :=
  averaged_nested_bounds _ (suffixLaw_compact S tag μ hμ W j) hs hN

end EntropyRateDimension.Typed

namespace EntropyRateDimension.System
open scoped BigOperators
variable {α : Type uα} [Fintype α]

theorem listDepth_nonneg (S : System α) (W : List α) : 0 ≤ S.listDepth W :=
  List.sum_nonneg (by intro x hx; obtain ⟨a,_,rfl⟩ := List.mem_map.mp hx; exact (S.letterDepth_pos a).le)

theorem listDepth_ofFn (S : System α) {n : ℕ} (w : Fin n → α) :
    S.listDepth (List.ofFn w)=S.wordDepth w := by
  simp only [listDepth,List.map_ofFn,List.sum_ofFn,wordDepth_sum,Function.comp_apply]

theorem listDepth_append (S : System α) (U V : List α) : S.listDepth (U++V)=S.listDepth U+S.listDepth V := by
  simp only [listDepth,List.map_append,List.sum_append]

theorem listDepth_take_add (S : System α) (W : List α) (j n : ℕ) :
    S.listDepth (W.take (j+n))=S.listDepth (W.take j)+S.listDepth ((W.drop j).take n) := by
  rw [List.take_add,listDepth_append]

theorem listDepth_monotone (S : System α) (W : List α) : Monotone (fun j => S.listDepth (W.take j)) := by
  intro j k hjk
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hjk
  dsimp only
  rw [listDepth_take_add]
  exact le_add_of_nonneg_right (S.listDepth_nonneg _)

theorem exists_depth_bound (S : System α) : ∃ D : ℝ, 0 < D ∧ ∀ a, S.letterDepth a ≤ D := by
  let D := 1+∑ a, S.letterDepth a
  have hn : 0 ≤ ∑ a, S.letterDepth a := Finset.sum_nonneg (fun a _ => (S.letterDepth_pos a).le)
  refine ⟨D,by dsimp [D]; linarith,fun a => ?_⟩
  have hh := Finset.single_le_sum (fun a (_ : a ∈ Finset.univ) => (S.letterDepth_pos a).le) (Finset.mem_univ a)
  dsimp [D]
  linarith

theorem listDepth_le (S : System α) {D : ℝ} (hD : ∀ a, S.letterDepth a ≤ D) (W : List α) :
    S.listDepth W ≤ D*W.length := by
  induction W with
  | nil => simp [listDepth]
  | cons a W ih =>
    simp only [listDepth,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one] at ih ⊢
    nlinarith [hD a]

theorem listDepth_take_le (S : System α) {D : ℝ} (hD : 0 ≤ D) (hd : ∀ a, S.letterDepth a ≤ D)
    (W : List α) (j : ℕ) : S.listDepth (W.take j) ≤ D*j := by
  have hh := S.listDepth_le hd (W.take j)
  rw [List.length_take] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_left j W.length) hD)

end EntropyRateDimension.System

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.WordAverage ----
namespace OAI

universe uι uα

namespace EntropyRateDimension.System
open scoped BigOperators
variable {α : Type uα} [Fintype α]

theorem wordAverage_mono (S : System α) (n : ℕ) {f g : List α → ℝ}
    (h : ∀ W, W.length=n → f W ≤ g W) : S.wordAverage n f ≤ S.wordAverage n g := by
  exact Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left
    (h (List.ofFn w) (List.length_ofFn ..)) (S.wordWeight_pos w).le)

theorem wordAverage_const (S : System α) (n : ℕ) (c : ℝ) : S.wordAverage n (fun _ => c)=c := by
  rw [wordAverage,← Finset.sum_mul,S.wordWeight_sum,one_mul]

theorem wordAverage_mul (S : System α) (n : ℕ) (c : ℝ) (f : List α → ℝ) :
    S.wordAverage n (fun W => c*f W)=c*S.wordAverage n f := by
  simp only [wordAverage,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem wordAverage_finset_sum {ι : Type uι} (S : System α) (n : ℕ) (s : Finset ι) (f : ι → List α → ℝ) :
    S.wordAverage n (fun W => ∑ i ∈ s, f i W)=∑ i ∈ s, S.wordAverage n (f i) := by
  simp only [wordAverage,Finset.mul_sum]
  exact Finset.sum_comm

theorem wordAverage_append (S : System α) (m n : ℕ) (f : List α → ℝ) :
    S.wordAverage (m+n) f =
      ∑ u : Fin m → α, S.wordWeight u*∑ v : Fin n → α, S.wordWeight v*f (List.ofFn u++List.ofFn v) := by
  rw [wordAverage,sum_words_append]
  simp only [wordWeight_append,List.ofFn_fin_append,Finset.mul_sum,mul_assoc]

theorem wordAverage_future_le (S : System α) (m n : ℕ) (f g : List α → ℝ)
    (h : ∀ u : Fin m → α,
      (∑ v : Fin n → α, S.wordWeight v*f (List.ofFn u++List.ofFn v)) ≤
      ∑ v : Fin n → α, S.wordWeight v*g (List.ofFn u++List.ofFn v)) :
    S.wordAverage (m+n) f ≤ S.wordAverage (m+n) g := by
  rw [wordAverage_append,wordAverage_append]
  exact Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_left (h u) (S.wordWeight_pos u).le)

theorem wordAverage_segment (S : System α) {H j n : ℕ} (hH : j+n ≤ H) (f : List α → ℝ) :
    S.wordAverage H (fun W => f ((W.drop j).take n))=S.wordAverage n f := by
  classical
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hH
  rw [wordAverage_append]
  rw [sum_words_append j n]
  simp only [wordWeight_append,List.ofFn_fin_append]
  have he (u : Fin j → α) (w : Fin n → α) (z : Fin t → α) :
      (((List.ofFn u++List.ofFn w)++List.ofFn z).drop j).take n=List.ofFn w := by
    have h1 : ((List.ofFn u++List.ofFn w)++List.ofFn z).drop j=List.ofFn w++List.ofFn z := by
      rw [List.append_assoc]
      simpa only [List.length_ofFn] using (List.drop_append_length (l₁ := List.ofFn u) (l₂ := List.ofFn w++List.ofFn z))
    rw [h1]
    simpa only [List.length_ofFn] using (List.take_append_length (l₁ := List.ofFn w) (l₂ := List.ofFn z))
  simp_rw [he,← Finset.sum_mul,S.wordWeight_sum,one_mul]
  simp only [mul_assoc,← Finset.mul_sum]
  rw [← Finset.sum_mul,S.wordWeight_sum,one_mul]
  rfl

end EntropyRateDimension.System

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.KernelEntropy ----
namespace OAI

universe uα uβ uX

namespace EntropyRateDimension.MeasureEntropy
open MeasureTheory
open scoped BigOperators ENNReal

theorem finite_entropy_integral {X : Type uX} {β : Type uβ} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (s : Finset β) (p : X → β → ℝ)
    (hm : ∀ b ∈ s, Measurable (fun y => p y b))
    (hp : ∀ b ∈ s, ∀ y, 0 ≤ p y b ∧ p y b ≤ 1) :
    (∫ y, ∑ b ∈ s, Real.negMulLog (p y b) ∂μ) ≤
      ∑ b ∈ s, Real.negMulLog (∫ y, p y b ∂μ) := by
  have hi (b) (hb : b ∈ s) : Integrable (fun y => p y b) μ :=
    (integrable_const (1 : ℝ)).mono' (hm b hb).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun y => by rw [Real.norm_eq_abs,abs_of_nonneg (hp b hb y).1]; exact (hp b hb y).2))
  have hni (b) (hb : b ∈ s) : Integrable (fun y => Real.negMulLog (p y b)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (Real.continuous_negMulLog.measurable.comp (hm b hb)).aestronglyMeasurable
    filter_upwards [] with y
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.negMulLog_nonneg (hp b hb y).1 (hp b hb y).2)]
    exact (Real.negMulLog_le_one_sub_self (hp b hb y).1).trans (sub_le_self _ (hp b hb y).1)
  rw [integral_finsetSum s hni]
  apply Finset.sum_le_sum
  intro b hb
  exact Real.concaveOn_negMulLog.le_map_integral Real.continuous_negMulLog.continuousOn
    isClosed_Ici (Filter.Eventually.of_forall (fun y => (hp b hb y).1)) (hi b hb) (hni b hb)

theorem random_observation_entropy {X : Type uX} {α : Type uα} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (p : α → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1)
    (F : α → X → ℝ) (hF : ∀ i, Measurable (F i))
    (hm : ν=∑ i, ENNReal.ofReal (p i) • μ.map (F i))
    (f : ℝ → ℤ) (hf : Measurable f) (s : Finset ℤ)
    (hs : ∀ i, ∀ᵐ y ∂μ, f (F i y) ∈ s) :
    (∫ y, FiniteEntropy.observableEntropy Finset.univ p (fun i => f (F i y)) ∂μ) ≤ entropy ν f := by
  classical
  let K : X → ℤ → ℝ := fun y b => FiniteEntropy.mass Finset.univ p (fun i => f (F i y)) b
  have hk (y : X) (b : ℤ) : K y b=∑ i, if f (F i y)=b then p i else 0 := by
    simp only [K,FiniteEntropy.mass,Finset.sum_filter]
  have hmK (b : ℤ) : Measurable (fun y => K y b) := by
    simp_rw [hk]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.ite
      (measurableSet_eq_fun (hf.comp (hF i)) measurable_const) measurable_const)
  have hpK (y : X) (b : ℤ) : 0 ≤ K y b ∧ K y b ≤ 1 := by
    refine ⟨FiniteEntropy.mass_nonneg _ _ _ (fun i _ => hp i) _,?_⟩
    change (∑ i ∈ Finset.univ.filter (fun i => f (F i y)=b), p i) ≤ 1
    rw [← hp1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hp i)
  have hmi (i : α) : IsProbabilityMeasure (μ.map (F i)) :=
    (Measure.isProbabilityMeasure_map_iff (hF i).aemeasurable).2 inferInstance
  let := hmi
  have hsupport : ∀ᵐ x ∂ν, f x ∈ s := by
    rw [hm]
    rw [ae_iff]
    simp only [Measure.coe_finsetSum,Finset.sum_apply,Measure.smul_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hh : ∀ᵐ x ∂μ.map (F i), f x ∈ s :=
      (ae_map_iff (hF i).aemeasurable (hf (s.finite_toSet.measurableSet))).mpr (hs i)
    rw [ae_iff] at hh
    rw [hh,smul_zero]
  have hmasses (b : ℤ) : (∫ y, K y b ∂μ)=mass ν f b := by
    rw [mass_mixture ν (fun i => μ.map (F i)) p hp hm f]
    simp_rw [hk]
    have hint (i : α) : Integrable (fun y => if f (F i y)=b then p i else 0) μ := by
      have hh : MeasurableSet {y | f (F i y)=b} :=
        measurableSet_eq_fun (hf.comp (hF i)) (measurable_const (a := b))
      have h := (integrable_const (p i) : Integrable (fun _ : X => p i) μ).indicator hh
      exact h.congr (Filter.Eventually.of_forall (fun y => by
        rw [Set.indicator_apply]
        rfl))
    rw [integral_finsetSum Finset.univ (fun i _ => hint i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [mass_map μ _ (hF i) f hf]
    have hind : (fun y => if f (F i y)=b then p i else 0) =
        ({y | f (F i y)=b} : Set X).indicator (fun _ => p i) := by
          funext y
          rw [Set.indicator_apply]
          rfl
    rw [hind,integral_indicator_const (p i) (show MeasurableSet {y | f (F i y)=b} from
      measurableSet_eq_fun (hf.comp (hF i)) (measurable_const (a := b)))]
    simp only [smul_eq_mul,mass,Function.comp_apply,mul_comm]
  have he : (fun y => FiniteEntropy.observableEntropy Finset.univ p (fun i => f (F i y))) =ᵐ[μ]
      fun y => ∑ b ∈ s, Real.negMulLog (K y b) := by
    filter_upwards [ae_all_iff.mpr hs] with y hy
    exact FiniteEntropy.observableEntropy_on_superset Finset.univ s p _ (fun i _ => hy i)
  rw [integral_congr_ae he,entropy_eq_sum ν f s hsupport]
  simpa only [hmasses] using finite_entropy_integral μ s K (fun b _ => hmK b) (fun b _ y => hpK y b)

theorem random_observation_integrable {X : Type uX} {α : Type uα} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [IsProbabilityMeasure μ] (p : α → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i=1)
    (f : α → X → ℤ) (hf : ∀ i, Measurable (f i)) (s : Finset ℤ)
    (hs : ∀ i, ∀ᵐ y ∂μ, f i y ∈ s) :
    Integrable (fun y => FiniteEntropy.observableEntropy Finset.univ p (fun i => f i y)) μ := by
  classical
  let K : X → ℤ → ℝ := fun y b => FiniteEntropy.mass Finset.univ p (fun i => f i y) b
  have hk (y : X) (b : ℤ) : K y b=∑ i, if f i y=b then p i else 0 := by
    simp only [K,FiniteEntropy.mass,Finset.sum_filter]
  have hmK (b : ℤ) : Measurable (fun y => K y b) := by
    simp_rw [hk]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.ite
      (measurableSet_eq_fun (hf i) measurable_const) measurable_const)
  have hpK (y : X) (b : ℤ) : 0 ≤ K y b ∧ K y b ≤ 1 := by
    refine ⟨FiniteEntropy.mass_nonneg _ _ _ (fun i _ => hp i) _,?_⟩
    change (∑ i ∈ Finset.univ.filter (fun i => f i y=b), p i) ≤ 1
    rw [← hp1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hp i)
  have hi (b : ℤ) : Integrable (fun y => Real.negMulLog (K y b)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (Real.continuous_negMulLog.measurable.comp (hmK b)).aestronglyMeasurable
    filter_upwards [] with y
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.negMulLog_nonneg (hpK y b).1 (hpK y b).2)]
    exact (Real.negMulLog_le_one_sub_self (hpK y b).1).trans (sub_le_self _ (hpK y b).1)
  apply (integrable_finsetSum s (fun b _ => hi b)).congr
  filter_upwards [ae_all_iff.mpr hs] with y hy
  exact (FiniteEntropy.observableEntropy_on_superset Finset.univ s p _ (fun i _ => hy i)).symm

end EntropyRateDimension.MeasureEntropy

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.TypedEntropy ----
namespace OAI

universe uα uβ uγ

namespace EntropyRateDimension.FiniteCondition
open scoped BigOperators
open FiniteEntropy

theorem entropy_expectation {α : Type uα} {β : Type uβ} {γ : Type uγ} [Fintype α] [DecidableEq β] [DecidableEq γ]
    (p : α → ℝ) (hp : ∀ a, 0 < p a) (tag : α → β) (f : α → γ) :
    (∑ a, p a*observableEntropy (fiber tag a) (fun v => p v/mass p tag a) f)=
      conditionalEntropy Finset.univ p f tag := by
  classical
  rw [conditionalEntropy_eq_sum _ _ _ _ (fun a _ => (hp a).le)]
  symm
  convert FiniteEntropy.sum_mass_mul Finset.univ (Finset.univ.image tag) p tag
    (fun c => observableEntropy (Finset.univ.filter (fun a => tag a=c))
      (fun a => p a/FiniteEntropy.mass Finset.univ p tag c) f)
    (fun a ha => Finset.mem_image_of_mem tag ha) using 1
  rfl

end EntropyRateDimension.FiniteCondition

namespace EntropyRateDimension.FiniteEntropy
open scoped BigOperators
open MeasureEntropy

theorem shifted_grid_compare {α : Type uα} (s : Finset α) (p f : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) (hp1 : ∑ a ∈ s, p a=1)
    {ρ : ℝ} (hρ : 0 < ρ) (u v : ℝ) :
    observableEntropy s p (fun a => label ρ u (f a)) ≤
      observableEntropy s p (fun a => label ρ v (f a))+Real.log 2 := by
  classical
  let g := fun a => label ρ v (f a)
  let r := fun a => relativeLabel ρ ρ u v (f a)
  have hr : ∀ a ∈ s, r a ∈ Finset.Icc (0 : ℤ) 1 := by
    intro a _
    simpa only [div_self hρ.ne',Int.ceil_one] using relativeLabel_mem hρ hρ u v (f a)
  have he := observableEntropy_le_of_fibers s p (fun a => label ρ u (f a))
    (fun a => (g a,r a)) hp (by
      intro a _ b _ hab
      obtain ⟨h1,h2⟩ := Prod.mk.inj hab
      dsimp [r,relativeLabel] at h2
      change label ρ v (f a)=label ρ v (f b) at h1
      rw [h1] at h2
      linarith)
  have hh := observableEntropy_pair_le s p g r hp hp1
  have hle := observableEntropy_le_log_on_superset s (Finset.Icc (0 : ℤ) 1) p r hr hp hp1
  norm_num at hle
  change observableEntropy s p r ≤ Real.log 2 at hle
  change _ ≤ observableEntropy s p g+Real.log 2
  linarith

end EntropyRateDimension.FiniteEntropy

namespace EntropyRateDimension.Typed
open MeasureTheory FairPairs FiniteCondition FiniteEntropy MeasureEntropy
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem expected_grid_comparison (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    {n : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (y : ℝ) :
    (∑ w : Fin n → α, S.wordWeight w*(law S tag w).gridEntropy ρ)*Real.log 2 ≤
      observableEntropy Finset.univ (S.wordWeight (n := n)) (fun v => ⌊S.wordMap v y/ρ⌋)+Real.log 2 := by
  classical
  let p := S.wordWeight (n := n)
  let t := tagWord tag (n := n)
  have hp : ∀ v, 0 < p v := S.wordWeight_pos
  have hlocal (w : Fin n → α) :
      (law S tag w).gridEntropy ρ*Real.log 2 ≤
        observableEntropy (fiber t w) (fun v => p v/FiniteCondition.mass p t w)
          (fun v => ⌊S.wordMap v y/ρ⌋)+Real.log 2 := by
    have hc := shifted_grid_compare (fiber t w) (fun v => p v/FiniteCondition.mass p t w)
      (fun v => (S.completeMap v).2)
      (fun v _ => (div_pos (hp v) (mass_pos p hp t w)).le) (fiber_normalized_sum p hp t w)
      hρ 0 ((S.completeMap w).1*y/ρ)
    have hobs : observableEntropy (fiber t w) (fun v => p v/FiniteCondition.mass p t w)
        (fun v => label ρ ((S.completeMap w).1*y/ρ) (S.completeMap v).2) =
        observableEntropy (fiber t w) (fun v => p v/FiniteCondition.mass p t w)
          (fun v => ⌊S.wordMap v y/ρ⌋) := by
      apply observableEntropy_congr _ _ _ _ _ (fun _ _ => rfl)
      intro v hv
      have hv' : t v=t w := (Finset.mem_filter.mp hv).2
      have hsl : (S.completeMap v).1=(S.completeMap w).1 := by
        rw [S.completeMap_slope,S.completeMap_slope]
        exact Finset.prod_congr rfl (fun j _ => hr _ _ (congrFun hv' j))
      unfold label System.wordMap
      rw [hsl]
      congr 1
      ring
    rw [hobs] at hc
    simpa only [law,FiniteCondition.law,Law.ofObservable_gridEntropy,
      div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne',label,add_zero] using hc
  have hsum := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hlocal w) (S.wordWeight_pos w).le)
  simp only [mul_add,Finset.sum_add_distrib,← mul_assoc,← Finset.sum_mul,S.wordWeight_sum,one_mul] at hsum
  rw [entropy_expectation p hp t] at hsum
  have hh := conditionalEntropy_le Finset.univ p (fun v => ⌊S.wordMap v y/ρ⌋) t
    (fun w _ => (hp w).le) (S.wordWeight_sum n)
  exact hsum.trans (by linarith)

theorem word_map_ae (S : System α) (μ : Measure ℝ) (hμ : S.SelfSimilar μ)
    {n : ℕ} (w : Fin n → α) {P : ℝ → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ x ∂μ.map (S.wordMap w), P x := by
  classical
  rw [ae_iff] at hP ⊢
  have hle : ENNReal.ofReal (S.wordWeight w) • μ.map (S.wordMap w) ≤ μ := by
    conv_rhs => rw [S.selfSimilar_words μ hμ n]
    exact Finset.single_le_sum (fun v (_ : v ∈ Finset.univ) =>
      (bot_le : (0 : Measure ℝ) ≤ ENNReal.ofReal (S.wordWeight v) • μ.map (S.wordMap v)))
      (Finset.mem_univ w)
  have hz : ENNReal.ofReal (S.wordWeight w)*(μ.map (S.wordMap w)) {x | ¬P x}=0 := by
    apply le_antisymm _ (zero_le : (0 : ℝ≥0∞) ≤ _)
    simpa only [Measure.smul_apply,smul_eq_mul,hP] using hle {x | ¬P x}
  exact (mul_eq_zero.mp hz).resolve_left (ENNReal.ofReal_ne_zero_iff.mpr (S.wordWeight_pos w))

theorem expected_grid_upper (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (hc : CompactlyCarried μ) (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∑ w : Fin n → α, S.wordWeight w*(law S tag w).gridEntropy ρ)*Real.log 2 ≤
      grid μ ρ 0+Real.log 2 := by
  classical
  obtain ⟨B,_,hB⟩ := hc
  let s := Finset.Icc ⌊-B/ρ+(0 : ℝ)⌋ ⌊B/ρ+(0 : ℝ)⌋
  have hs (w : Fin n → α) : ∀ᵐ y ∂μ, label ρ 0 (S.wordMap w y) ∈ s := by
    apply (ae_map_iff (S.wordMap_measurable w).aemeasurable
      ((label_measurable ρ 0) s.finite_toSet.measurableSet)).mp
    exact word_map_ae S μ hμ w (label_ae_finite μ hρ hB)
  have hj := random_observation_entropy μ μ S.wordWeight (fun w => (S.wordWeight_pos w).le)
    (S.wordWeight_sum n) S.wordMap S.wordMap_measurable (S.selfSimilar_words μ hμ n)
    (label ρ 0) (label_measurable ρ 0) s hs
  have hi := random_observation_integrable μ S.wordWeight (fun w => (S.wordWeight_pos w).le)
    (S.wordWeight_sum n) (fun w y => label ρ 0 (S.wordMap w y))
    (fun w => (label_measurable ρ 0).comp (S.wordMap_measurable w)) s hs
  have hpoint := integral_mono (integrable_const
    ((∑ w : Fin n → α, S.wordWeight w*(law S tag w).gridEntropy ρ)*Real.log 2))
    (hi.add (integrable_const (Real.log 2)))
    (fun y => by
      change _ ≤ observableEntropy Finset.univ S.wordWeight
        (fun v => label ρ 0 (S.wordMap v y))+Real.log 2
      simpa only [label,add_zero] using expected_grid_comparison S tag hr hρ y)
  change (∫ _ : ℝ, (∑ w : Fin n → α, S.wordWeight w*(law S tag w).gridEntropy ρ)*Real.log 2 ∂μ) ≤
    (∫ y, observableEntropy Finset.univ S.wordWeight (fun v => label ρ 0 (S.wordMap v y))+Real.log 2 ∂μ) at hpoint
  rw [integral_add hi (integrable_const _)] at hpoint
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hpoint
  exact hpoint.trans (by simpa only [grid,add_comm] using add_le_add_right hj (Real.log 2))

end EntropyRateDimension.Typed

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.EntropyBudget ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open FiniteEntropy FairPairs FiniteCondition MeasureEntropy MeasureTheory
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [Fintype β] [DecidableEq β]

theorem expected_entropy_lower (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v) (n : ℕ) :
    S.walkEntropy n*Real.log 2-(n : ℝ)*Real.log (Fintype.card β) ≤
      (∑ w : Fin n → α, S.wordWeight w*(law S tag w).shannonEntropy)*Real.log 2 := by
  classical
  rw [show (∑ w : Fin n → α, S.wordWeight w*(law S tag w).shannonEntropy)*Real.log 2=
    conditionalEntropy Finset.univ S.wordWeight (fun w => (S.completeMap w).2) (tagWord tag) from
      law_entropy_mean S.wordWeight S.wordWeight_pos (tagWord tag) _]
  have he := observableEntropy_le_of_fibers Finset.univ (S.wordWeight (n := n))
    S.completeMap (fun w => ((S.completeMap w).2,tagWord tag w))
    (fun w _ => (S.wordWeight_pos w).le) (by
      intro w _ v _ h
      apply Prod.ext
      · rw [S.completeMap_slope,S.completeMap_slope]
        exact Finset.prod_congr rfl (fun j _ => hr _ _ (congrFun (Prod.mk.inj h).2 j))
      · exact (Prod.mk.inj h).1)
  have ht := observableEntropy_le_log_on_superset Finset.univ Finset.univ
    (S.wordWeight (n := n)) (tagWord tag) (fun _ _ => Finset.mem_univ _)
    (fun w _ => (S.wordWeight_pos w).le) (S.wordWeight_sum n)
  simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,Real.log_pow] at ht
  rw [S.map_entropy_as_observation] at he
  unfold conditionalEntropy
  linarith

omit [Fintype β] in
theorem entropyLoss_le (S : System α) (tag : α → β) {n : ℕ}
    (w : Fin n → α) (ρ : ℝ) :
    entropyLoss S tag w ρ ≤ (n : ℝ)*Real.log (Fintype.card α) := by
  classical
  let p := fun v : Fin n → α => S.wordWeight v / FiniteCondition.mass S.wordWeight (tagWord tag) w
  let s := fiber (tagWord tag) w
  have hp : ∀ v ∈ s, 0 ≤ p v := fun v _ =>
    (div_pos (S.wordWeight_pos v) (mass_pos S.wordWeight S.wordWeight_pos (tagWord tag) w)).le
  have hp1 : ∑ v ∈ s, p v=1 := fiber_normalized_sum S.wordWeight S.wordWeight_pos (tagWord tag) w
  have hle := (observableEntropy_le s p (fun v => (S.completeMap v).2) hp).trans
    (entropy_le_log_card s p hp hp1)
  have hs : (0 : ℝ)<s.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨w,by simp [s,fiber]⟩
  have ht : (s.card : ℝ) ≤ (Fintype.card α : ℝ)^n := by
    have hc := Finset.card_le_card (Finset.subset_univ s)
    simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow] using
      (show (s.card : ℝ) ≤ (Finset.card (Finset.univ : Finset (Fin n → α)) : ℝ) by exact_mod_cast hc)
  have hlog := Real.log_le_log hs ht
  rw [Real.log_pow] at hlog
  let f := fun v : Fin n → α => ⌊(S.completeMap v).2/ρ⌋
  have hm : ∀ b, 0 ≤ FiniteEntropy.mass s p f b := FiniteEntropy.mass_nonneg s p f hp
  have hnon : 0 ≤ observableEntropy s p f := by
    apply FiniteEntropy.entropy_nonneg _ _ (fun b _ => hm b)
    intro b hb
    exact (Finset.single_le_sum (fun c _ => hm c) hb).trans_eq
      ((FiniteEntropy.mass_sum s p f).trans hp1)
  dsimp only [entropyLoss,law,FiniteCondition.law]
  rw [Law.ofObservable_entropy,Law.ofObservable_gridEntropy]
  have hl : Real.log 2≠0 := (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne'
  change (observableEntropy s p (fun v => (S.completeMap v).2)/Real.log 2-
    observableEntropy s p (fun v => ⌊(S.completeMap v).2/ρ⌋)/Real.log 2)*Real.log 2 ≤ _
  field_simp
  linarith

theorem expected_entropyLoss_lower (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (hc : CompactlyCarried μ) (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    S.walkEntropy n*Real.log 2-(n : ℝ)*Real.log (Fintype.card β)-grid μ ρ 0-Real.log 2 ≤
      ∑ w : Fin n → α, S.wordWeight w*entropyLoss S tag w ρ := by
  have he := expected_entropy_lower S tag hr n
  have hg := expected_grid_upper S tag hr μ hμ hc n hρ
  have hid : (∑ w : Fin n → α, S.wordWeight w*entropyLoss S tag w ρ)=
      (∑ w : Fin n → α, S.wordWeight w*(law S tag w).shannonEntropy)*Real.log 2-
      (∑ w : Fin n → α, S.wordWeight w*(law S tag w).gridEntropy ρ)*Real.log 2 := by
    simp only [entropyLoss,mul_sub,sub_mul,← mul_assoc,Finset.sum_sub_distrib,Finset.sum_mul]
  rw [hid]
  linarith

end EntropyRateDimension.Typed

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.RetainedLoss ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.MeasureEntropy
open MeasureTheory

theorem grid_le_averaged_add_log_two (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : CompactlyCarried μ) {s : ℝ} (hs : 0 < s) (u : ℝ) :
    grid μ s u ≤ averaged μ s+Real.log 2 := by
  have hh := intervalIntegral.integral_mono zero_le_one
    (intervalIntegrable_const (c := grid μ s u))
    ((grid_intervalIntegrable μ hμ hs 0 1).add intervalIntegrable_const)
    (fun v => grid_le_grid_add_log_two μ hμ hs hs le_rfl u v)
  rw [intervalIntegral.integral_const,intervalIntegral.integral_add
    (grid_intervalIntegrable μ hμ hs 0 1) intervalIntegrable_const,
    intervalIntegral.integral_const,← averaged_eq_intervalIntegral] at hh
  simpa only [sub_zero,one_smul] using hh

end EntropyRateDimension.MeasureEntropy

namespace EntropyRateDimension.Typed
open FairPairs MeasureTheory MeasureEntropy
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]

theorem fineScale_pos (A : ℝ) (n : ℕ) : 0 < fineScale A n := zpow_pos (by norm_num) _

theorem fineScale_lt_one {A : ℝ} (hA : 0 < A) {n : ℕ} (hn : 0 < n) : fineScale A n < 1 := by
  have ht : 0 < ⌈A*n⌉ := Int.ceil_pos.mpr (mul_pos hA (by exact_mod_cast hn))
  change (2 : ℝ)^(-⌈A*n⌉) < (2 : ℝ)^(0 : ℤ)
  exact (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ)<2)).mpr (by omega)

theorem fineScale_log (A : ℝ) (n : ℕ) :
    Real.log (1/fineScale A n)=(⌈A*n⌉ : ℝ)*Real.log 2 := by
  rw [one_div,Real.log_inv,fineScale,Real.log_zpow,Int.cast_neg,neg_mul,neg_neg]

theorem expected_loss_linear (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    {D C A : ℝ} (hD : 0 ≤ D) (hA : 0 < A)
    (hb : ∀ s, 0 < s → s < 1 → averaged μ s ≤ D*Real.log (1/s)+C)
    {n : ℕ} (hn : 0 < n) :
    (n : ℝ)*(S.entropyRate*Real.log 2-Real.log (Fintype.card β)-D*A*Real.log 2)-
        (D*Real.log 2+C+2*Real.log 2) ≤
      ∑ w : Fin n → α, S.wordWeight w*entropyLoss S tag w (fineScale A n) := by
  obtain ⟨B,hB,hc⟩ := S.selfSimilar_compact μ hμ
  have hc' : CompactlyCarried μ := ⟨B,hB.le,hc⟩
  have he := expected_entropyLoss_lower S tag hr μ hμ hc' n (fineScale_pos A n)
  have hg : grid μ (fineScale A n) 0 ≤ D*Real.log (1/fineScale A n)+C+Real.log 2 := by
    have h1 := grid_le_averaged_add_log_two μ hc' (fineScale_pos A n) 0
    have h2 := hb _ (fineScale_pos A n) (fineScale_lt_one hA hn)
    linarith
  rw [fineScale_log] at hg
  have hh := S.entropyRate_le (n-1)
  rw [Nat.sub_add_cancel hn] at hh
  have hh' := mul_le_mul_of_nonneg_right
    ((le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ)<n)).mp hh)
    (Real.log_pos (by norm_num : (1 : ℝ)<2)).le
  have hhceil := mul_le_mul_of_nonneg_right (Int.ceil_lt_add_one (A*n)).le
    (mul_nonneg hD (Real.log_pos (by norm_num : (1 : ℝ)<2)).le)
  nlinarith

omit [Fintype β] in
theorem discarded_loss_bound (S : System α) (tag : α → β)
    {A' : ℝ} (hA' : S.lyapunov < A') {n : ℕ} (hn : 0 < n) (ρ : ℝ) :
    (∑ w : Fin n → α, if A'*n < S.wordDepth w then
      S.wordWeight w*entropyLoss S tag w ρ else 0) ≤
        Real.log (Fintype.card α)*S.depthVariance/(A'-S.lyapunov)^2 := by
  classical
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  have hcard : (1 : ℝ) ≤ Fintype.card α := by
    exact_mod_cast Fintype.card_pos
  have hl : 0 ≤ Real.log (Fintype.card α) := Real.log_nonneg hcard
  have hbound := S.depth_bad_mass_bound hA' hn
  calc
    _ ≤ (n : ℝ)*Real.log (Fintype.card α)*
        ∑ w : Fin n → α, if A'*n < S.wordDepth w then S.wordWeight w else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro w _
      split_ifs
      · simpa only [mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_left (entropyLoss_le S tag w ρ) (S.wordWeight_pos w).le
      · simp
    _ ≤ (n : ℝ)*Real.log (Fintype.card α)*
        (S.depthVariance/((n : ℝ)*(A'-S.lyapunov)^2)) :=
      mul_le_mul_of_nonneg_left hbound (mul_nonneg hnR.le hl)
    _ = _ := by field_simp

theorem retained_loss_linear (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    {D C A A' : ℝ} (hD : 0 ≤ D) (hA : 0 < A) (hA' : S.lyapunov < A')
    (hb : ∀ s, 0 < s → s < 1 → averaged μ s ≤ D*Real.log (1/s)+C)
    (hgap : D*A*Real.log 2 < S.entropyRate*Real.log 2-Real.log (Fintype.card β)) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, 0 < N ∧ ∀ n, N ≤ n →
      ε*n ≤ retainedLoss S tag A A' n := by
  classical
  let γ := S.entropyRate*Real.log 2-Real.log (Fintype.card β)-D*A*Real.log 2
  have hγ : 0 < γ := sub_pos.mpr hgap
  let K := D*Real.log 2+C+2*Real.log 2+
    Real.log (Fintype.card α)*S.depthVariance/(A'-S.lyapunov)^2
  obtain ⟨N,hN⟩ := exists_nat_gt (max 1 (2*K/γ))
  have hNpos : 0 < N := by
    have := (le_max_left _ _).trans_lt hN
    exact_mod_cast (lt_trans zero_lt_one this)
  refine ⟨γ/2,by positivity,N,hNpos,fun n hn => ?_⟩
  have hn0 := hNpos.trans_le hn
  have he := expected_loss_linear S tag hr μ hμ hD hA hb hn0
  have hd := discarded_loss_bound S tag hA' hn0 (fineScale A n)
  have hid : retainedLoss S tag A A' n+
      (∑ w : Fin n → α, if A'*n < S.wordDepth w then
        S.wordWeight w*entropyLoss S tag w (fineScale A n) else 0)=
      ∑ w : Fin n → α, S.wordWeight w*entropyLoss S tag w (fineScale A n) := by
    rw [retainedLoss,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    by_cases h : S.wordDepth w ≤ A'*n <;> simp [h,not_lt_of_ge,lt_of_not_ge]
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hNK := (div_lt_iff₀ hγ).mp ((le_max_right _ _).trans_lt hN)
  change (n : ℝ)*γ-(D*Real.log 2+C+2*Real.log 2) ≤ _ at he
  dsimp only [K] at hNK
  nlinarith

end EntropyRateDimension.Typed

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.TypedSumset ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open FairPairs FiniteCondition
open scoped BigOperators
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

omit [DecidableEq β] in

theorem translation_coefficients (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    {n : ℕ} (w : Fin n → α) :
    ∃ R : Fin n → ℝ, ∀ v, tagWord tag v=tagWord tag w →
      (S.completeMap v).2=∑ j, R j*S.offset (v j) := by
  induction n with
  | zero =>
    refine ⟨Fin.elim0,fun v _ => ?_⟩
    simp [System.completeMap,System.wordAffine]
  | succ n ih =>
    obtain ⟨R,hR⟩ := ih (fun j => w j.succ)
    refine ⟨Fin.cons 1 (fun j => S.ratio (w 0)*R j),fun v hv => ?_⟩
    have ht : tagWord tag (fun j => v j.succ)=tagWord tag (fun j => w j.succ) :=
      funext (fun j => congrFun hv j.succ)
    have hr0 := hr (v 0) (w 0) (congrFun hv 0)
    conv_lhs => rw [← Fin.cons_self_tail v,S.completeMap_cons]
    simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,one_mul]
    rw [hR (Fin.tail v) ht,hr0]
    simp only [Finset.mul_sum,mul_assoc,Fin.tail]
    ring

theorem support_digit_representation (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    {n : ℕ} (w : Fin n → α) :
    ∃ R : Fin n → ℝ, ∀ x ∈ (law S tag w).support,
      ∃ v : Fin n → α, x=∑ j, R j*S.offset (v j) := by
  obtain ⟨R,hR⟩ := translation_coefficients S tag hr w
  refine ⟨R,fun x hx => ?_⟩
  change x ∈ (fiber (tagWord tag) w).image (fun v => (S.completeMap v).2) at hx
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
  exact ⟨v,hR v (Finset.mem_filter.mp hv).2⟩

theorem sumset_card_bound (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    {n : ℕ} (w : Fin n → α) (k : ℕ) :
    ((law S tag w).sumset k).card ≤ (k+1)^(n*Fintype.card α) := by
  obtain ⟨R,hR⟩ := support_digit_representation S tag hr w
  simpa only [Fintype.card_fin, DigitSumset.sumset, Law.sumset] using
    DigitSumset.card_sumset_le (law S tag w).support (fun j a => R j*S.offset a) hR k

theorem sumset_log_bound (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    {n : ℕ} (w : Fin n → α) (k : ℕ) :
    Real.log ((law S tag w).sumset k).card ≤ (n : ℝ)*Fintype.card α*Real.log (k+1) := by
  classical
  obtain ⟨x,hx⟩ := (law S tag w).support_nonempty
  have hs : ((law S tag w).sumset k).Nonempty :=
    Finset.image_nonempty.mpr (Finset.univ_nonempty_iff.mpr ⟨fun _ : Fin k => ⟨x,hx⟩⟩)
  have hb : (((law S tag w).sumset k).card : ℝ) ≤ ((k : ℝ)+1)^(n*Fintype.card α) := by
    exact_mod_cast sumset_card_bound S tag hr w k
  have hh := Real.log_le_log (show (0 : ℝ)<((law S tag w).sumset k).card by
    exact_mod_cast Finset.card_pos.mpr hs) hb
  rw [Real.log_pow,Nat.cast_mul] at hh
  exact hh

end EntropyRateDimension.Typed

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.PairBands ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension
open scoped BigOperators Topology
open Filter

theorem exists_nat_log_small {ε : ℝ} (hε : 0 < ε) (K : ℝ) :
    ∃ k : ℕ, 0 < k ∧ K*Real.log (k+1) < ε*k := by
  have ht : Tendsto (fun k : ℕ => K*(Real.log ((k : ℝ)+1)/(k : ℝ))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    simpa only [pow_one,one_mul,Function.comp_apply,add_neg_cancel_right,mul_zero] using h.const_mul K
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  let k := max N 1
  have hk : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  refine ⟨k,hk,?_⟩
  have hh := hN k (le_max_left _ _)
  have hp : (0 : ℝ)<k := by exact_mod_cast hk
  rw [← mul_div_assoc] at hh
  exact (div_lt_iff₀ hp).mp hh

namespace Typed
open FairPairs
variable {α : Type uα} {β : Type uβ} [Fintype α] [Nonempty α] [DecidableEq β]

omit [Nonempty α] in
theorem fineScale_band_condition (A : ℝ) (n : ℕ) (ℓ : ℤ) :
    (2 : ℝ)^(-ℓ) ≤ 2*fineScale A n ↔ bandStart A n ≤ ℓ := by
  have he : 2*fineScale A n=(2 : ℝ)^(1-⌈A*n⌉) := by
    rw [sub_eq_add_neg,zpow_add₀ (by norm_num : (2 : ℝ)≠0),zpow_one]
    rfl
  rw [he,zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ)<2)]
  dsimp only [bandStart]
  omega

omit [Nonempty α] in
theorem exists_band_pair_bound (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (A : ℝ) (n k : ℕ) (hk : 1 ≤ k) :
    ∃ B : ℤ, bandStart A n ≤ B ∧ ∀ w : Fin n → α,
      (k : ℝ)*entropyLoss S tag w (fineScale A n) ≤
        (n : ℝ)*Fintype.card α*Real.log (k+1)+60000*k^4*Real.log 2*
          ∑ ℓ ∈ Finset.Icc (bandStart A n) B, capacity (law S tag w) ℓ := by
  classical
  let J := insert (bandStart A n) (Finset.univ.biUnion (fun w : Fin n → α => (law S tag w).bandSupport))
  have hJ : J.Nonempty := Finset.insert_nonempty _ _
  let B := J.max' hJ
  have hab : bandStart A n ≤ B := Finset.le_max' J _ (Finset.mem_insert_self _ _)
  refine ⟨B,hab,fun w => ?_⟩
  have hh := pair_bound_natural (law S tag w) k hk (fineScale A n) (fineScale_pos A n)
  have hs : ∑ ℓ ∈ (law S tag w).bandSupport.filter (fun ℓ => (2 : ℝ)^(-ℓ) ≤ 2*fineScale A n),
      capacity (law S tag w) ℓ ≤
      ∑ ℓ ∈ Finset.Icc (bandStart A n) B, capacity (law S tag w) ℓ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ℓ hℓ
      obtain ⟨hℓ,hrℓ⟩ := Finset.mem_filter.mp hℓ
      apply Finset.mem_Icc.mpr
      refine ⟨(fineScale_band_condition A n ℓ).mp hrℓ,?_⟩
      apply Finset.le_max' J ℓ
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨w,Finset.mem_univ _,hℓ⟩)
    · intro ℓ _ _
      exact capacity_nonneg _ _
  have hc : 0 ≤ 60000*(k : ℝ)^4*Real.log 2 := by positivity
  have hl := sumset_log_bound S tag hr w k
  have hid : entropyLoss S tag w (fineScale A n)=
      FiniteEntropy.entropy (law S tag w).support (law S tag w).prob-
        FiniteEntropy.observableEntropy (law S tag w).support (law S tag w).prob (fun x => ⌊x/fineScale A n⌋) := by
    dsimp only [entropyLoss,Law.shannonEntropy,Law.gridEntropy]
    field_simp
  rw [hid]
  exact hh.trans (add_le_add hl (mul_le_mul_of_nonneg_left hs hc))

omit [Nonempty α] in
theorem pair_bands_of_retained_loss (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (A A' : ℝ) {ε : ℝ} (hε : 0 < ε) {N : ℕ}
    (he : ∀ n, N ≤ n → ε*n ≤ retainedLoss S tag A A' n) :
    ∃ c : ℝ, 0 < c ∧ ∀ n, N ≤ n → ∃ B : ℤ, bandStart A n ≤ B ∧
      c*n ≤ pairBudget S tag A' (bandStart A n) B n := by
  classical
  obtain ⟨k,hk,hl⟩ := exists_nat_log_small hε (Fintype.card α)
  let K : ℝ := Fintype.card α*Real.log (k+1)
  let C : ℝ := 60000*k^4*Real.log 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hgap : 0 < ε*k-K := sub_pos.mpr hl
  refine ⟨(ε*k-K)/C,div_pos hgap hC,fun n hn => ?_⟩
  obtain ⟨B,hB,hb⟩ := exists_band_pair_bound S tag hr A n k hk
  refine ⟨B,hB,?_⟩
  have hK : 0 ≤ K := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) k; linarith))
  have hp : (k : ℝ)*retainedLoss S tag A A' n ≤ (n : ℝ)*K+C*pairBudget S tag A' (bandStart A n) B n := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun (w : Fin n → α) _ =>
      show (k : ℝ)*(if S.wordDepth w ≤ A'*n then S.wordWeight w*entropyLoss S tag w (fineScale A n) else 0) ≤
        S.wordWeight w*((n : ℝ)*K)+C*(if S.wordDepth w ≤ A'*n then S.wordWeight w*
          ∑ ℓ ∈ Finset.Icc (bandStart A n) B, capacity (law S tag w) ℓ else 0) from by
        split_ifs
        · have h := mul_le_mul_of_nonneg_left (hb w) (S.wordWeight_pos w).le
          dsimp only [K,C]
          nlinarith
        · simp only [mul_zero,add_zero]
          exact mul_nonneg (S.wordWeight_pos w).le (mul_nonneg (Nat.cast_nonneg _) hK))
    simpa only [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.sum_mul,
      S.wordWeight_sum,one_mul,retainedLoss,pairBudget] using hh
  have hh := mul_le_mul_of_nonneg_left (he n hn) (by positivity : (0 : ℝ)≤k)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hC).mpr
  nlinarith

end Typed
end EntropyRateDimension

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.WindowCount ----
namespace OAI

namespace EntropyRateDimension.Windows
open scoped BigOperators

theorem retained_sum_le {q : ℕ} (n K : Fin q → ℕ) (a B : Fin q → ℤ) (A' : ℝ)
    (hsep : ∀ i h : Fin q, h < i → (B h : ℝ)<(a i : ℝ)-A'*n i-1)
    (σ : ℕ → ℝ) (hσ : Monotone σ) (L : ℤ)
    (g : ℕ → ℝ) (hg : Antitone g) (hgn : ∀ j, 0 ≤ g j) :
    (∑ i, ∑ k ∈ Finset.range (K i),
      if Retained σ A' (n i) (a i) (B i) L (k*n i) then
        g (k*n i)-g (k*n i+n i) else 0) ≤ g 0 := by
  classical
  let s := (Finset.univ.sigma (fun i : Fin q => Finset.range (K i))).filter
    (fun x => Retained σ A' (n x.1) (a x.1) (B x.1) L (x.2*n x.1))
  let u := fun x : (i : Fin q) × ℕ => x.2*n x.1
  let v := fun x : (i : Fin q) × ℕ => x.2*n x.1+n x.1
  have hd : (↑s : Set ((i : Fin q) × ℕ)).PairwiseDisjoint (fun x => Finset.Ico (u x) (v x)) := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    rcases x with ⟨i,k⟩
    rcases y with ⟨h,l⟩
    dsimp only [u,v]
    dsimp only at hx' hy'
    by_cases he : i=h
    · subst h
      exact multiples_disjoint (show k≠l by intro hkl; subst l; exact hxy rfl)
    · rcases lt_or_gt_of_ne he with hil | hli
      · have hb := finer_window_before hσ hy'.1 hy'.2.1 hx'.2.2 (hsep h i hil)
        apply Finset.disjoint_left.mpr
        intro t ht hu
        obtain ⟨ht1,ht2⟩ := Finset.mem_Ico.mp ht
        obtain ⟨hu1,hu2⟩ := Finset.mem_Ico.mp hu
        dsimp only at ht1 ht2 hu1 hu2
        omega
      · have hb := finer_window_before hσ hx'.1 hx'.2.1 hy'.2.2 (hsep i h hli)
        apply Finset.disjoint_left.mpr
        intro t ht hu
        obtain ⟨ht1,ht2⟩ := Finset.mem_Ico.mp ht
        obtain ⟨hu1,hu2⟩ := Finset.mem_Ico.mp hu
        dsimp only at ht1 ht2 hu1 hu2
        omega
  have hh := sum_disjoint_drops_le s u v (fun x _ => Nat.le_add_right _ _) hd g hg hgn
  simpa only [s,Finset.sum_filter,Finset.sum_sigma,u,v] using hh

theorem sum_target_shift (f : ℤ → ℝ) (a B c T : ℤ)
    (ha : 1 ≤ a) (hc : 0 ≤ c) (hB : B+c ≤ T) :
    (∑ L ∈ Finset.Icc 1 T, if a ≤ L-c ∧ L-c ≤ B then f (L-c) else 0)=
      ∑ ℓ ∈ Finset.Icc a B, f ℓ := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun L _ => L-c)
  · intro L hL
    exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hL).2
  · intro L hL L' hL' hh
    omega
  · intro ℓ hℓ
    have hl := Finset.mem_Icc.mp hℓ
    refine ⟨ℓ+c,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩,by omega⟩
  · intro L _
    rfl

end EntropyRateDimension.Windows

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.ScaleGain ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension
open scoped BigOperators ENNReal
open MeasureTheory FairPairs MeasureEntropy

theorem scaled_band_distance (ν : Law) {a : ℝ} (ha : a ≠ 0) (L : ℤ)
    (e : ν.edges (L-⌈-Real.log |a|/Real.log 2⌉)) :
    (2 : ℝ)^(-L) ≤ |a*e.val.2-a*e.val.1| ∧
      |a*e.val.2-a*e.val.1| < 4*(2 : ℝ)^(-L) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hap : 0 < |a| := abs_pos.mpr ha
  let σ := -Real.log |a|/Real.log 2
  let c := ⌈σ⌉
  have hp : 0 < |a| *(2 : ℝ)^c := mul_pos hap (zpow_pos (by norm_num) _)
  have hlog : Real.log (|a| *(2 : ℝ)^c)=Real.log |a|+(c : ℝ)*Real.log 2 := by
    rw [Real.log_mul hap.ne' (zpow_ne_zero _ (by norm_num : (2 : ℝ)≠0)),Real.log_zpow]
  have hc1 := (div_le_iff₀ hl).mp (Int.le_ceil σ)
  have hc2 := Int.ceil_lt_add_one σ
  have hid : σ*Real.log 2= -Real.log |a| := div_mul_cancel₀ _ hl.ne'
  have ha1 : 1 ≤ |a| *(2 : ℝ)^c := by
    apply (Real.log_nonneg_iff hp).mp
    rw [hlog]
    dsimp only [c]
    linarith
  have ha2 : |a| *(2 : ℝ)^c < 2 := by
    apply (Real.log_lt_log_iff hp (by norm_num : (0 : ℝ)<2)).mp
    rw [hlog]
    have hh := mul_lt_mul_of_pos_right hc2 hl
    dsimp only [c]
    nlinarith
  have he := (Finset.mem_filter.mp e.property).2
  have hxy : 0 < e.val.2-e.val.1 := sub_pos.mpr he.1
  have habs : |a*e.val.2-a*e.val.1|=|a| *(e.val.2-e.val.1) := by
    rw [← mul_sub,abs_mul,abs_of_pos hxy]
  have hz1 : (2 : ℝ)^(-(L-c))=(2 : ℝ)^c*(2 : ℝ)^(-L) := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ)≠0)]
    congr 1
    ring
  have hz2 : (2 : ℝ)^(1-(L-c))=2*((2 : ℝ)^c*(2 : ℝ)^(-L)) := by
    rw [show 1-(L-c)=1+(-(L-c)) by ring,zpow_add₀ (by norm_num : (2 : ℝ)≠0),zpow_one,hz1]
  change _ ∧ (2 : ℝ)^(-(L-c)) ≤ _ ∧ _ < (2 : ℝ)^(1-(L-c)) at he
  rw [hz1,hz2] at he
  rw [habs]
  have hr : 0 < (2 : ℝ)^(-L) := zpow_pos (by norm_num) _
  have hlow := mul_le_mul_of_nonneg_left he.2.1 hap.le
  have hupp := mul_lt_mul_of_pos_left he.2.2 hap
  have hlow' := mul_le_mul_of_nonneg_right ha1 hr.le
  have hupp' := mul_lt_mul_of_pos_right ha2 (by positivity : 0 < 2*(2 : ℝ)^(-L))
  constructor <;> nlinarith

theorem distance_window_bounds {r v : ℝ} (hr : 0 < r) (hv : r ≤ v) (hv4 : v < 4*r)
    {M : ℕ} (hM : 4 < M) :
    r/M < v ∧ v < ((M*M : ℕ) : ℝ)*(r/M) ∧
      (r/M)/v+v/(((M*M : ℕ) : ℝ)*(r/M)) ≤ 5/(M : ℝ) := by
  have hMR : (4 : ℝ)<M := by exact_mod_cast hM
  have hMp : (0 : ℝ)<M := by linarith
  have hvp : 0 < v := hr.trans_le hv
  have hid : ((M*M : ℕ) : ℝ)*(r/M)=(M : ℝ)*r := by push_cast; field_simp
  rw [hid]
  refine ⟨?_,?_,?_⟩
  · apply (div_lt_iff₀ hMp).mpr
    nlinarith
  · nlinarith
  · have h1 : (r/M)/v ≤ 1/(M : ℝ) := by
      apply (div_le_div_iff₀ hvp hMp).mpr
      rw [div_mul_cancel₀ _ hMp.ne']
      simpa only [one_mul] using hv
    have h2 : v/((M : ℝ)*r) ≤ 4/(M : ℝ) := by
      apply (div_le_div_iff₀ (mul_pos hMp hr) hMp).mpr
      nlinarith
    have hh : 1/(M : ℝ)+4/(M : ℝ)=5/(M : ℝ) := by ring
    linarith

namespace Typed
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem conditional_gain (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (hc : CompactlyCarried μ) {δ : ℝ}
    (hδ : ∀ v, 0 < v → δ ≤ deficit μ v) {M : ℕ} (hM : 4 < M)
    (he : 5/(M : ℝ)*Real.log 2 ≤ δ/2)
    {j n : ℕ} (u : Fin j → α) (w : Fin n → α) (t : ℕ) (L : ℤ) :
    δ/2*capacity (law S tag w) (L-⌈S.wordDepth u⌉) ≤
      ∑ z : Fin t → α, S.wordWeight z*
        (window (scaledTail S tag μ (S.completeMap u).1 (Fin.append w z))
          ((2 : ℝ)^(-L)/M) (((M*M : ℕ) : ℝ)*((2 : ℝ)^(-L)/M))-
        window (scaledTail S tag μ ((S.completeMap u).1*(S.completeMap w).1) z)
          ((2 : ℝ)^(-L)/M) (((M*M : ℕ) : ℝ)*((2 : ℝ)^(-L)/M))) := by
  have ha : (S.completeMap u).1≠0 := S.completeMap_slope_ne_zero u
  have hb : (S.completeMap u).1*(S.completeMap w).1≠0 := mul_ne_zero ha (S.completeMap_slope_ne_zero w)
  have hMp : (0 : ℝ)<M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  have hs : 0 < (2 : ℝ)^(-L)/(M : ℝ) := div_pos (zpow_pos (by norm_num) _) hMp
  have hv (e : (law S tag w).edges (L-⌈S.wordDepth u⌉)) :=
    scaled_band_distance (law S tag w) ha L e
  have hd (e : (law S tag w).edges (L-⌈S.wordDepth u⌉)) :=
    distance_window_bounds (zpow_pos (by norm_num : (0 : ℝ)<2) (-L)) (hv e).1 (hv e).2 hM
  have hg := finiteConv_mean_gain (law S tag w) (S.completeMap u).1
    ((S.completeMap u).1*(S.completeMap w).1) hb μ hc
    (scaledTail S tag μ ((S.completeMap u).1*(S.completeMap w).1))
    (fun z : Fin t → α => scaledTail_compact S tag μ hc _ z)
    S.wordWeight (fun z => (S.wordWeight_pos z).le) (S.wordWeight_sum t)
    (scaledTail_mean S tag μ hμ _ t).symm hδ hs (by positivity : 0 < M*M)
    (L-⌈S.wordDepth u⌉) (fun e => ⟨(hd e).1,(hd e).2.1⟩)
    (fun e => (mul_le_mul_of_nonneg_right (hd e).2.2 (Real.log_pos (by norm_num : (1 : ℝ)<2)).le).trans he)
  simp only [← scaledTail_append S tag hr] at hg
  convert hg using 1
  ring

end Typed
end EntropyRateDimension

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.WindowGain ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs Windows
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

omit [Fintype α] [DecidableEq β] in
theorem three_segment {j n t : ℕ} (u : Fin j → α) (w : Fin n → α) (z : Fin t → α) :
    (((List.ofFn u++List.ofFn w)++List.ofFn z).drop j).take n=List.ofFn w := by
  have h1 : ((List.ofFn u++List.ofFn w)++List.ofFn z).drop j=List.ofFn w++List.ofFn z := by
    rw [List.append_assoc]
    simpa only [List.length_ofFn] using (List.drop_append_length (l₁ := List.ofFn u) (l₂ := List.ofFn w++List.ofFn z))
  rw [h1]
  simpa only [List.length_ofFn] using (List.take_append_length (l₁ := List.ofFn w) (l₂ := List.ofFn z))

omit [Fintype α] [DecidableEq β] in
theorem three_take {j n t : ℕ} (u : Fin j → α) (w : Fin n → α) (z : Fin t → α) :
    ((List.ofFn u++List.ofFn w)++List.ofFn z).take j=List.ofFn u := by
  rw [List.append_assoc]
  simpa only [List.length_ofFn] using (List.take_append_length (l₁ := List.ofFn u) (l₂ := List.ofFn w++List.ofFn z))

theorem three_retained (S : System α) (A' : ℝ) (a B L : ℤ)
    {j n t : ℕ} (u : Fin j → α) (w : Fin n → α) (z : Fin t → α) :
    Retained (fun i => S.listDepth (((List.ofFn u++List.ofFn w)++List.ofFn z).take i)) A' n a B L j ↔
      S.wordDepth w ≤ A'*n ∧ a ≤ L-⌈S.wordDepth u⌉ ∧ L-⌈S.wordDepth u⌉ ≤ B := by
  simp only [Retained,S.listDepth_take_add,add_sub_cancel_left,three_segment,three_take,S.listDepth_ofFn]

theorem suffixLaw_at_append (S : System α) (tag : α → β) (μ : Measure ℝ) (U V : List α) :
    suffixLaw S tag μ (U++V) U.length=listScaledTail S tag μ (S.wordAffine U).1 V := by
  simp only [suffixLaw,List.take_append_length,List.drop_append_length]

theorem three_suffix_start (S : System α) (tag : α → β) (μ : Measure ℝ)
    {j n t : ℕ} (u : Fin j → α) (w : Fin n → α) (z : Fin t → α) :
    suffixLaw S tag μ ((List.ofFn u++List.ofFn w)++List.ofFn z) j=
      scaledTail S tag μ (S.completeMap u).1 (Fin.append w z) := by
  rw [List.append_assoc]
  have h := suffixLaw_at_append S tag μ (List.ofFn u) (List.ofFn w++List.ofFn z)
  simp only [List.length_ofFn] at h
  rw [h,← List.ofFn_fin_append,listScaledTail_ofFn]
  rfl

theorem three_suffix_end (S : System α) (tag : α → β) (μ : Measure ℝ)
    {j n t : ℕ} (u : Fin j → α) (w : Fin n → α) (z : Fin t → α) :
    suffixLaw S tag μ ((List.ofFn u++List.ofFn w)++List.ofFn z) (j+n)=
      scaledTail S tag μ ((S.completeMap u).1*(S.completeMap w).1) z := by
  have h := suffixLaw_at_append S tag μ (List.ofFn u++List.ofFn w) (List.ofFn z)
  simp only [List.length_append,List.length_ofFn] at h
  rw [h,listScaledTail_ofFn,S.wordAffine_append]
  rfl

theorem expected_retained_gain (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (hc : CompactlyCarried μ) {δ : ℝ}
    (hδ : ∀ v, 0 < v → δ ≤ deficit μ v) {M : ℕ} (hM : 4 < M)
    (he : 5/(M : ℝ)*Real.log 2 ≤ δ/2)
    {H j n : ℕ} (hH : j+n ≤ H) (A' : ℝ) (a B L : ℤ) :
    δ/2*S.wordAverage H (fun W => retainedCapacity S tag A' n a B L W j) ≤
      S.wordAverage H (fun W => retainedDrop S tag μ M A' n a B L W j) := by
  classical
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hH
  rw [← S.wordAverage_mul]
  apply S.wordAverage_future_le (j+n) t
  intro v
  obtain ⟨⟨u,w⟩,rfl⟩ := (Fin.appendEquiv j n).surjective v
  change (∑ z : Fin t → α, S.wordWeight z*(δ/2*retainedCapacity S tag A' n a B L
    (List.ofFn (Fin.append u w)++List.ofFn z) j)) ≤
    ∑ z : Fin t → α, S.wordWeight z*retainedDrop S tag μ M A' n a B L
      (List.ofFn (Fin.append u w)++List.ofFn z) j
  simp only [List.ofFn_fin_append]
  have hgain := conditional_gain S tag hr μ hμ hc hδ hM he u w t L
  simp only [retainedCapacity,retainedDrop,three_retained,three_segment,three_take,
    S.listDepth_ofFn,listLaw_ofFn,suffixWindow,three_suffix_start,three_suffix_end]
  split_ifs
  · simpa only [← Finset.sum_mul,S.wordWeight_sum,one_mul] using hgain
  · simp only [mul_zero,Finset.sum_const_zero,le_refl]

theorem expected_capacity_targets (S : System α) (tag : α → β)
    {H j n : ℕ} (hH : j+n ≤ H) (A' : ℝ) (a B T : ℤ)
    (ha : 1 ≤ a)
    (hcover : ∀ W : List α, 0 ≤ ⌈S.listDepth (W.take j)⌉ ∧ B+⌈S.listDepth (W.take j)⌉ ≤ T) :
    (∑ L ∈ Finset.Icc 1 T, S.wordAverage H (fun W => retainedCapacity S tag A' n a B L W j))=
      pairBudget S tag A' a B n := by
  classical
  rw [← S.wordAverage_finset_sum]
  have hpoint (W : List α) : (∑ L ∈ Finset.Icc 1 T, retainedCapacity S tag A' n a B L W j)=
      if S.listDepth ((W.drop j).take n) ≤ A'*n then
        ∑ ℓ ∈ Finset.Icc a B, capacity (listLaw S tag ((W.drop j).take n)) ℓ else 0 := by
    simp only [retainedCapacity,Retained,S.listDepth_take_add,add_sub_cancel_left]
    by_cases h : S.listDepth ((W.drop j).take n) ≤ A'*n
    · simp only [h,true_and]
      exact sum_target_shift _ a B _ T ha (hcover W).1 (hcover W).2
    · simp only [h,false_and,ite_false,Finset.sum_const_zero]
  simp_rw [hpoint]
  rw [S.wordAverage_segment hH (fun V => if S.listDepth V ≤ A'*n then
    ∑ ℓ ∈ Finset.Icc a B, capacity (listLaw S tag V) ℓ else 0)]
  simp only [System.wordAverage,System.listDepth_ofFn,listLaw_ofFn,pairBudget,mul_ite,mul_zero]

end EntropyRateDimension.Typed

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.GlobalCount ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy FairPairs Windows
open scoped BigOperators ENNReal
variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem total_expected_drop_le (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hc : CompactlyCarried μ)
    {M : ℕ} (hM : 0 < M) (H : ℕ) {q : ℕ} (n K : Fin q → ℕ) (a B : Fin q → ℤ) (A' : ℝ)
    (hsep : ∀ i h : Fin q, h < i → (B h : ℝ)<(a i : ℝ)-A'*n i-1) (L : ℤ) :
    (∑ i, ∑ k ∈ Finset.range (K i), S.wordAverage H (fun W =>
      retainedDrop S tag μ M A' (n i) (a i) (B i) L W (k*n i))) ≤ Real.log ((M*M : ℕ) : ℝ) := by
  classical
  have hs : 0 < (2 : ℝ)^(-L)/(M : ℝ) := div_pos (zpow_pos (by norm_num) _) (by exact_mod_cast hM)
  have hMM : 0 < M*M := Nat.mul_pos hM hM
  simp_rw [← S.wordAverage_finset_sum]
  calc
    _ ≤ S.wordAverage H (fun _ => Real.log ((M*M : ℕ) : ℝ)) := by
      apply S.wordAverage_mono
      intro W _
      have hh := retained_sum_le n K a B A' hsep (fun j => S.listDepth (W.take j))
        (S.listDepth_monotone W) L (suffixWindow S tag μ ((2 : ℝ)^(-L)/(M : ℝ)) (M*M) W)
        (suffixWindow_antitone S tag hr μ hc hs hMM W)
        (fun j => (suffixWindow_bounds S tag μ hc hs hMM W j).1)
      exact hh.trans (suffixWindow_bounds S tag μ hc hs hMM W 0).2
    _ = _ := S.wordAverage_const _ _

theorem count_pair_budget_le (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (hc : CompactlyCarried μ) {δ : ℝ}
    (hδ : ∀ v, 0 < v → δ ≤ deficit μ v) {M : ℕ} (hM : 4 < M)
    (he : 5/(M : ℝ)*Real.log 2 ≤ δ/2)
    {H D q : ℕ} (hD : 1 ≤ D) (hd : ∀ v, S.letterDepth v ≤ D)
    (n K : Fin q → ℕ) (a B : Fin q → ℤ) (A' : ℝ)
    (hkn : ∀ i, K i*n i=H) (ha : ∀ i, 1 ≤ a i) (hB : ∀ i, B i ≤ (H : ℤ))
    (hsep : ∀ i h : Fin q, h < i → (B h : ℝ)<(a i : ℝ)-A'*n i-1) :
    (δ/2)*(∑ i, (K i : ℝ)*pairBudget S tag A' (a i) (B i) (n i)) ≤
      (2*D*H : ℕ)*Real.log ((M*M : ℕ) : ℝ) := by
  classical
  let T : ℤ := (2*D*H : ℕ)
  have hkH (i : Fin q) (k : ℕ) (hk : k ∈ Finset.range (K i)) : k*n i+n i ≤ H := by
    rw [← Nat.succ_mul,← hkn i]
    exact Nat.mul_le_mul_right _ (Finset.mem_range.mp hk)
  have hcover (i : Fin q) (k : ℕ) (hk : k ∈ Finset.range (K i)) (W : List α) :
      0 ≤ ⌈S.listDepth (W.take (k*n i))⌉ ∧ B i+⌈S.listDepth (W.take (k*n i))⌉ ≤ T := by
    refine ⟨Int.ceil_nonneg (S.listDepth_nonneg _),?_⟩
    have hh : S.listDepth (W.take (k*n i)) ≤ ((D*H : ℕ) : ℝ) := by
      have h1 := S.listDepth_take_le (Nat.cast_nonneg D) hd W (k*n i)
      have h2 : k*n i ≤ H := (Nat.le_add_right _ _).trans (hkH i k hk)
      have h2R : ((k*n i : ℕ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast h2
      exact h1.trans (by simpa only [Nat.cast_mul] using
        mul_le_mul_of_nonneg_left h2R (Nat.cast_nonneg D))
    have hh' : ⌈S.listDepth (W.take (k*n i))⌉ ≤ ((D*H : ℕ) : ℤ) := by
      apply Int.ceil_le.mpr
      exact_mod_cast hh
    have hDH : H ≤ D*H := by simpa only [one_mul] using Nat.mul_le_mul_right H hD
    dsimp only [T]
    have hDH' : (H : ℤ) ≤ ((D*H : ℕ) : ℤ) := by exact_mod_cast hDH
    have hmul : ((2*D*H : ℕ) : ℤ)=2*((D*H : ℕ) : ℤ) := by push_cast; ring
    rw [hmul]
    linarith [hB i]
  have hlocal (i : Fin q) (k : ℕ) (hk : k ∈ Finset.range (K i)) :
      (δ/2)*pairBudget S tag A' (a i) (B i) (n i) ≤
      ∑ L ∈ Finset.Icc 1 T, S.wordAverage H (fun W => retainedDrop S tag μ M A' (n i) (a i) (B i) L W (k*n i)) := by
    rw [← expected_capacity_targets S tag (hkH i k hk) A' (a i) (B i) T (ha i) (hcover i k hk),Finset.mul_sum]
    exact Finset.sum_le_sum (fun L _ => expected_retained_gain S tag hr μ hμ hc hδ hM he
      (hkH i k hk) A' (a i) (B i) L)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.range (K i)) (fun k hk => hlocal i k hk))
  have hup : (∑ i, ∑ k ∈ Finset.range (K i), ∑ L ∈ Finset.Icc 1 T,
      S.wordAverage H (fun W => retainedDrop S tag μ M A' (n i) (a i) (B i) L W (k*n i))) ≤
      (2*D*H : ℕ)*Real.log ((M*M : ℕ) : ℝ) := by
    calc
      _ = ∑ L ∈ Finset.Icc 1 T, ∑ i, ∑ k ∈ Finset.range (K i),
          S.wordAverage H (fun W => retainedDrop S tag μ M A' (n i) (a i) (B i) L W (k*n i)) := by
        simp_rw [Finset.sum_comm (s := Finset.range _) (t := Finset.Icc 1 T)]
        exact Finset.sum_comm
      _ ≤ ∑ L ∈ Finset.Icc 1 T, Real.log ((M*M : ℕ) : ℝ) := Finset.sum_le_sum (fun L _ =>
        total_expected_drop_le S tag hr μ hc (by omega) H n K a B A' hsep L)
      _ = _ := by
        have hcard : (Finset.Icc (1 : ℤ) T).card=2*D*H := by
          simp only [Int.card_Icc,add_sub_cancel_right,T,Int.toNat_natCast]
        rw [Finset.sum_const,hcard,nsmul_eq_mul]
  apply le_trans _ hup
  convert hsum using 1
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end EntropyRateDimension.Typed

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.BandSelection ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open scoped BigOperators

theorem exists_large_band_start {A A' : ℝ} (hA : 0 < A) (hAA : A' < A) (N : ℕ) (C : ℝ) :
    ∃ n : ℕ, 0 < n ∧ N ≤ n ∧ 1 ≤ bandStart A n ∧
      C < (bandStart A n : ℝ)-A'*n-1 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max (N : ℝ) (max (2/A) ((C+2)/(A-A'))))
  have hnN : N ≤ n := by exact_mod_cast ((le_max_left _ _).trans_lt hn).le
  have h2 : 2/A < (n : ℝ) := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hn
  have hC : (C+2)/(A-A') < (n : ℝ) := (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hn
  have h2' := (div_lt_iff₀ hA).mp h2
  have hC' := (div_lt_iff₀ (sub_pos.mpr hAA)).mp hC
  have hceil := Int.le_ceil (A*(n : ℝ))
  have hn0 : 0 < n := by
    have : (0 : ℝ)<n := (div_pos (by norm_num) hA).trans h2
    exact_mod_cast this
  refine ⟨n,hn0,hnN,?_,?_⟩
  · dsimp only [bandStart]
    have hc : (2 : ℝ) ≤ (⌈A*(n : ℝ)⌉ : ℝ) := by nlinarith
    have : (2 : ℤ) ≤ ⌈A*(n : ℝ)⌉ := by exact_mod_cast hc
    omega
  · dsimp only [bandStart]
    push_cast
    nlinarith

variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem select_separated_bands (S : System α) (tag : α → β)
    {A A' c : ℝ} (hA : 0 < A) (hAA : A' < A) {N : ℕ}
    (hb : ∀ n, N ≤ n → ∃ B : ℤ, bandStart A n ≤ B ∧
      c*n ≤ pairBudget S tag A' (bandStart A n) B n) (q : ℕ) :
    ∃ n : Fin q → ℕ, ∃ B : Fin q → ℤ,
      (∀ i, 0 < n i) ∧ (∀ i, 1 ≤ bandStart A (n i)) ∧
      (∀ i, c*n i ≤ pairBudget S tag A' (bandStart A (n i)) (B i) (n i)) ∧
      (∀ i h : Fin q, h < i → (B h : ℝ)<(bandStart A (n i) : ℝ)-A'*n i-1) := by
  classical
  induction q with
  | zero =>
    refine ⟨Fin.elim0,Fin.elim0,?_,?_,?_,?_⟩ <;> intro i <;> exact i.elim0
  | succ q ih =>
    obtain ⟨n,B,hn,ha,hb',hsep⟩ := ih
    let C : ℝ := ∑ i, |(B i : ℝ)|
    have hC (i : Fin q) : (B i : ℝ) ≤ C :=
      (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (B j : ℝ)) (Finset.mem_univ i))
    obtain ⟨n',hn',hN,ha',hg⟩ := exists_large_band_start hA hAA N C
    obtain ⟨B',_,hb''⟩ := hb n' hN
    refine ⟨Fin.snoc n n',Fin.snoc B B',?_,?_,?_,?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa only [Fin.snoc_last] using hn'
      · simpa only [Fin.snoc_castSucc] using hn i
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa only [Fin.snoc_last] using ha'
      · simpa only [Fin.snoc_castSucc] using ha i
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa only [Fin.snoc_last] using hb''
      · simpa only [Fin.snoc_castSucc] using hb' i
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro h
        refine Fin.lastCases ?_ (fun h => ?_) h
        · exact fun h => (lt_irrefl _ h).elim
        · intro _
          simpa only [Fin.snoc_last,Fin.snoc_castSucc] using (hC h).trans_lt hg
      · intro h
        refine Fin.lastCases ?_ (fun h => ?_) h
        · intro hh
          exact (not_lt_of_ge (Fin.le_last _) hh).elim
        · intro hh
          simpa only [Fin.snoc_castSucc] using hsep i h (by exact_mod_cast hh)

theorem exists_common_horizon {q : ℕ} (n : Fin q → ℕ) (hn : ∀ i, 0 < n i) (B : Fin q → ℤ) :
    ∃ H : ℕ, 0 < H ∧ (∀ i, n i ∣ H) ∧ (∀ i, B i ≤ (H : ℤ)) := by
  classical
  let P := ∏ i, n i
  let R := 1+∑ i, (B i).toNat
  have hP : 0 < P := Finset.prod_pos (fun i _ => hn i)
  have hR : 0 < R := by dsimp [R]; omega
  refine ⟨R*P,Nat.mul_pos hR hP,?_,?_⟩
  · intro i
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem n (Finset.mem_univ i)) R
  · intro i
    have hBi : (B i).toNat ≤ ∑ i, (B i).toNat := Finset.single_le_sum (fun j _ => Nat.zero_le ((B j).toNat)) (Finset.mem_univ i)
    have hle : (B i).toNat ≤ R*P := by
      have hP1 : 1 ≤ P := hP
      have hRP : R ≤ R*P := by simpa only [mul_one] using Nat.mul_le_mul_left R hP1
      apply le_trans _ hRP
      dsimp only [R]
      omega
    have hh : ((B i).toNat : ℤ) ≤ ((R*P : ℕ) : ℤ) := by exact_mod_cast hle
    omega

end EntropyRateDimension.Typed

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.EntropyGap ----
namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy
open scoped BigOperators
variable {α : Type uα} {β : Type uβ} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]

theorem no_strict_entropy_gap (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    {d C A A' : ℝ} (hd : 0 ≤ d) (hd1 : d < 1) (hA : 0 < A)
    (hA' : S.lyapunov < A') (hAA : A' < A)
    (hb : ∀ s, 0 < s → s < 1 → averaged μ s ≤ d*Real.log (1/s)+C)
    (hgap : d*A*Real.log 2 < S.entropyRate*Real.log 2-Real.log (Fintype.card β)) : False := by
  classical
  obtain ⟨δ,hδ,hdef⟩ := S.uniform_nonsaturation_of_entropy_bound μ hμ hd1 hb
  obtain ⟨M,hM'⟩ := exists_nat_gt (max 4 (10*Real.log 2/δ))
  have hM : 4 < M := by exact_mod_cast (le_max_left _ _).trans_lt hM'
  have hMr : (0 : ℝ)<M := by exact_mod_cast (show 0 < M by omega)
  have he : 5/(M : ℝ)*Real.log 2 ≤ δ/2 := by
    have hh := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hM')
    apply (le_div_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
    apply (mul_le_mul_iff_right₀ hMr).mp
    have heq : (5/(M : ℝ)*Real.log 2*2)*(M : ℝ)=10*Real.log 2 := by field_simp; ring
    nlinarith [heq]
  obtain ⟨ε,hε,N,_,hloss⟩ := retained_loss_linear S tag hr μ hμ hd hA hA' hb hgap
  obtain ⟨c,hc,hbands⟩ := pair_bands_of_retained_loss S tag hr A A' hε hloss
  obtain ⟨dmax,_,hdmax⟩ := S.exists_depth_bound
  obtain ⟨D,hD'⟩ := exists_nat_gt (max 1 dmax)
  have hD : 1 ≤ D := by exact_mod_cast ((le_max_left _ _).trans_lt hD').le
  have hdD : ∀ v, S.letterDepth v ≤ (D : ℝ) := fun v => (hdmax v).trans ((le_max_right _ _).trans_lt hD').le
  have hcoef : 0 < δ/2*c := mul_pos (div_pos hδ (by norm_num)) hc
  obtain ⟨q,hq⟩ := exists_nat_gt ((2*(D : ℝ)*Real.log ((M*M : ℕ) : ℝ))/(δ/2*c))
  obtain ⟨n,B,hn,ha,hbudget,hsep⟩ := select_separated_bands S tag hA hAA hbands q
  obtain ⟨H,hH,hdvd,hBH⟩ := exists_common_horizon n hn B
  let K : Fin q → ℕ := fun i => H/n i
  have hkn (i : Fin q) : K i*n i=H := Nat.div_mul_cancel (hdvd i)
  obtain ⟨R,hR,hcompact⟩ := S.selfSimilar_compact μ hμ
  have hcomp : CompactlyCarried μ := ⟨R,hR.le,hcompact⟩
  have hcount := count_pair_budget_le S tag hr μ hμ hcomp hdef hM he hD hdD n K
    (fun i => bandStart A (n i)) B A' hkn ha hBH hsep
  have hsum : (q : ℝ)*(c*H) ≤ ∑ i, (K i : ℝ)*pairBudget S tag A' (bandStart A (n i)) (B i) (n i) := by
    calc
      _ = ∑ _i : Fin q, c*(H : ℝ) := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        have hi := mul_le_mul_of_nonneg_left (hbudget i) (Nat.cast_nonneg (K i))
        have hnH : (K i : ℝ)*(n i : ℝ)=(H : ℝ) := by exact_mod_cast hkn i
        nlinarith
  have hlim : (δ/2*c)*(q : ℝ) ≤ 2*(D : ℝ)*Real.log ((M*M : ℕ) : ℝ) := by
    apply (mul_le_mul_iff_right₀ (by exact_mod_cast hH : (0 : ℝ)<H)).mp
    calc
      _ = δ/2*((q : ℝ)*(c*H)) := by ring
      _ ≤ δ/2*(∑ i, (K i : ℝ)*pairBudget S tag A' (bandStart A (n i)) (B i) (n i)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ _ := by simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_assoc,mul_comm,mul_left_comm] using hcount
  have hq' := (div_lt_iff₀ hcoef).mp hq
  nlinarith

end EntropyRateDimension.Typed

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.Main ----
namespace OAI

universe uι

namespace EntropyRateDimension
open MeasureTheory MeasureEntropy
open scoped BigOperators ENNReal

theorem exists_slightly_larger_depth {d χ h : ℝ} (hd : 0 ≤ d) (hgap : d*χ < h) :
    ∃ a : ℝ, χ < a ∧ d*a < h := by
  let t := (h-d*χ)/(2*(d+1))
  have hp : 0 < 2*(d+1) := by linarith
  have ht : 0 < t := div_pos (sub_pos.mpr hgap) hp
  have he : t*(2*(d+1))=h-d*χ := div_mul_cancel₀ _ hp.ne'
  refine ⟨χ+t,by linarith,?_⟩
  nlinarith

namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]
attribute [local instance] OAI.EntropyRateDimension.System.instMeasurableSpace_2
attribute [local instance] OAI.EntropyRateDimension.System.instMeasurableSingletonClass_2
end System

end EntropyRateDimension

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.HomogeneousDimension ----
namespace OAI

universe uι

open MeasureTheory

namespace EntropyRateDimension.Extensions

/-- Constant ratios need only one type in the entropy-gap contradiction. -/
theorem homogeneous_exponent_lower_direct {ι : Type uι} [Fintype ι] [Nonempty ι]
    (S : System ι) {lam : ℝ} (hr : ∀ i, S.ratio i = lam)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ) :
    min 1 (S.entropyRate / S.lyapunov) ≤ Coding.exponent S := by
  classical
  by_contra! hstrict
  obtain ⟨d, hed, hdm⟩ := exists_between hstrict
  have hd : 0 ≤ d := (Coding.exponent_nonneg S).trans hed.le
  have hd1 : d < 1 := hdm.trans_le (min_le_left _ _)
  have hdr : d < S.entropyRate / S.lyapunov := hdm.trans_le (min_le_right _ _)
  have hdh : d * S.lyapunov < S.entropyRate := (lt_div_iff₀ S.lyapunov_pos).mp hdr
  obtain ⟨a, hχa, hda⟩ := exists_slightly_larger_depth hd hdh
  have hap : 0 < a := S.lyapunov_pos.trans hχa
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨C, hC⟩ := S.selfSimilar_entropy_bound μ hμ hed
  apply Typed.no_strict_entropy_gap S (fun _ : ι => ())
    (fun i j _ => (hr i).trans (hr j).symm) μ hμ hd hd1 hap
    (A' := (S.lyapunov + a) / 2) (by linarith) (by linarith) hC
  simpa using mul_lt_mul_of_pos_right hda hl

end EntropyRateDimension.Extensions

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Extensions
open MeasureTheory


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.Extensions.homogeneous_exponent_lower_direct.{uι} := @_root_.OAI.EntropyRateDimension.Extensions.homogeneous_exponent_lower_direct.{uι}
