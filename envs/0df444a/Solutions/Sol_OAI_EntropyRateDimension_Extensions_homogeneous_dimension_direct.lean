-- Prove2me | solution 1 for OAI.EntropyRateDimension.Extensions.homogeneous_dimension_direct
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:07:25.172976+00:00
-- url     : https://prove2.me/submissions/90f4cedc-b8f1-4c99-a5db-dcc2e305e6de

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/HomogeneousDimension.lean:L33-L59
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.EntropyRateDimension.Extensions.homogeneous_dimension_direct.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_EntropyRateDimension_Extensions_homogeneous_dimension_direct) verbatim and is proved by it.
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
import Theorems.Thm_OAI_EntropyRateDimension_Coding_exponent_symbol_entropy_bound
import Theorems.Thm_OAI_EntropyRateDimension_Extensions_homogeneous_exponent_lower_direct
import Theorems.Thm_OAI_EntropyRateDimension_Extensions_word_entropy

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

theorem lyapunov_pos [Nonempty ι] (S : System ι) : 0 < S.lyapunov := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [lyapunov, neg_pos]
  apply Finset.sum_neg
  · intro i _
    exact mul_neg_of_pos_of_neg (S.weight_pos i)
      (div_neg_of_neg_of_pos (Real.log_neg (S.ratio_pos i) (S.ratio_lt_one i)) hlog)
  · exact Finset.univ_nonempty

end System

theorem lowerHausdorffDimension_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    lowerHausdorffDimension μ ≤ 1 := by
  calc
    lowerHausdorffDimension μ ≤ dimH (Set.univ : Set ℝ) :=
      iInf_le_of_le Set.univ (iInf_le_of_le MeasurableSet.univ
        (iInf_le_of_le (by simp : 0 < μ Set.univ) le_rfl))
    _ = 1 := Real.dimH_univ

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

end EntropyRateDimension
end

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

theorem observableEntropy_comp_le {α : Type uα} {β : Type uβ} {γ : Type uγ} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (p : α → ℝ) (f : α → β) (g : β → γ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    observableEntropy s p (g ∘ f) ≤ observableEntropy s p f := by
  rw [observableEntropy_comp]
  exact observableEntropy_le _ _ _ (fun b _ => mass_nonneg s p f hp b)

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

end FiniteEntropy
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

-- ---- from OAI.MeasureTheory.SelfSimilar.LocalEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension

namespace FiniteEntropy

end FiniteEntropy

namespace MeasureEntropy

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

theorem restrict_le_hausdorff (μ : Measure ℝ) (E : Set ℝ) {a R : ℝ}
    (_ha : 0 ≤ a) (hR : 0 < R)
    (hball : ∀ x ∈ E, ∀ r : ℝ, 0 < r → r < R →
      μ (closedBall x r) ≤ (ENNReal.ofReal r)^a) :
    μ.restrict E ≤ Measure.hausdorffMeasure a := by
  apply Measure.le_hausdorffMeasure a (μ.restrict E) (ENNReal.ofReal (R/2))
    (ENNReal.ofReal_pos.mpr (by positivity))
  intro A hA
  have hAtop : ediam A ≠ ⊤ := ne_top_of_le_ne_top (by simp) hA
  have hdiam : diam A < R := by
    have hh := ENNReal.toReal_mono (by simp : ENNReal.ofReal (R/2) ≠ ⊤) hA
    rw [ENNReal.toReal_ofReal (by positivity)] at hh
    exact lt_of_le_of_lt hh (by linarith)
  have hcltop : ediam (closure A) ≠ ⊤ := by rwa [ediam_closure]
  by_cases hE : (closure A ∩ E).Nonempty
  · obtain ⟨x,hxA,hxE⟩ := hE
    have hh : ∀ r : ℝ, diam A < r → r < R →
        (μ.restrict E) A ≤ (ENNReal.ofReal r)^a := by
      intro r hdr hrR
      have hr : 0 < r := lt_of_le_of_lt (diam_nonneg) hdr
      calc
        (μ.restrict E) A ≤ (μ.restrict E) (closure A) := measure_mono subset_closure
        _ = μ (closure A ∩ E) := Measure.restrict_apply isClosed_closure.measurableSet
        _ ≤ μ (closedBall x r) := measure_mono (fun y hy => by
          apply mem_closedBall.mpr
          have hd := dist_le_diam_of_mem' hcltop hy.1 hxA
          rw [diam_closure] at hd
          exact hd.trans hdr.le)
        _ ≤ _ := hball x hxE r hr hrR
    have ht : Tendsto (fun r : ℝ => (ENNReal.ofReal r)^a) (𝓝[>] (diam A))
        (𝓝 ((ediam A)^a)) := by
      have he : ENNReal.ofReal (diam A)=ediam A := ENNReal.ofReal_toReal hAtop
      rw [← he]
      exact ((ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal).tendsto _).mono_left
        nhdsWithin_le_nhds
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
      (isOpen_Iio.mem_nhds hdiam)] with r hdr hrR
    exact hh r hdr hrR
  · have he : closure A ∩ E=∅ := Set.not_nonempty_iff_eq_empty.mp hE
    calc
      (μ.restrict E) A ≤ (μ.restrict E) (closure A) := measure_mono subset_closure
      _ = 0 := by rw [Measure.restrict_apply isClosed_closure.measurableSet,he,measure_empty]
      _ ≤ _ := bot_le

theorem positive_set_dim_ge (μ : Measure ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hlocal : ∀ᵐ x ∂μ, ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      μ (closedBall x r) ≤ (ENNReal.ofReal r)^a)
    {B : Set ℝ} (hB : MeasurableSet B) (hpos : 0 < μ B) :
    ENNReal.ofReal a ≤ dimH B := by
  let E : ℕ → Set ℝ := fun n => {x | ∀ r : ℝ, 0 < r → r < 1/((n : ℝ)+1) →
      μ (closedBall x r) ≤ (ENNReal.ofReal r)^a}
  have hae : ∀ᵐ x ∂μ, x ∈ ⋃ n, E n := by
    filter_upwards [hlocal] with x hx
    obtain ⟨R,hR,hRx⟩ := hx
    obtain ⟨n,hn⟩ := (tendsto_one_div_add_atTop_nhds_zero_nat.eventually
      (gt_mem_nhds hR)).exists
    exact mem_iUnion.mpr ⟨n,fun r hr hrn => hRx r hr (hrn.trans hn)⟩
  have hex : ∃ n, 0 < μ (B ∩ E n) := by
    by_contra! hn
    have hzero : μ (⋃ n, B ∩ E n)=0 := measure_iUnion_null (fun n => by simpa using hn n)
    have hsub : B ≤ᵐ[μ] ⋃ n, B ∩ E n := by
      filter_upwards [hae] with x hx hxB
      obtain ⟨n,hn⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨n,hxB,hn⟩
    have := measure_mono_ae hsub
    rw [hzero] at this
    exact (not_lt_of_ge this) hpos
  obtain ⟨n,hn⟩ := hex
  have hdom := restrict_le_hausdorff μ (E n) ha (by positivity : 0 < 1/((n : ℝ)+1))
    (fun x hx r hr hrR => hx r hr hrR)
  have hmass : 0 < Measure.hausdorffMeasure a B := by
    have hh := hdom B
    rw [Measure.restrict_apply hB] at hh
    exact hn.trans_le hh
  have hh := le_dimH_of_hausdorffMeasure_ne_zero (d := ⟨a,ha⟩) hmass.ne'
  convert hh using 1
  exact (ENNReal.coe_nnreal_eq ⟨a,ha⟩).symm

theorem eventual_upper_of_limit (μ : Measure ℝ) [IsFiniteMeasure μ] {x a d : ℝ}
    (hx : x ∈ μ.support) (had : a < d)
    (hlim : Tendsto (fun r => -Real.log (μ.real (closedBall x r)) / -Real.log r)
      (𝓝[>] 0) (𝓝 d)) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, 0 < r → r < R →
      μ (closedBall x r) ≤ (ENNReal.ofReal r)^a := by
  have hev := hlim.eventually (lt_mem_nhds had)
  obtain ⟨R,hR,hRx⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine ⟨min R 1,lt_min hR zero_lt_one,?_⟩
  intro r hr hrR
  have hr1 : r < 1 := lt_of_lt_of_le hrR (min_le_right _ _)
  have harr : a < -Real.log (μ.real (closedBall x r)) / -Real.log r :=
    hRx ⟨by simpa [Real.dist_eq,abs_of_pos hr] using lt_of_lt_of_le hrR (min_le_left _ _),hr⟩
  have hlogr : 0 < -Real.log r := neg_pos.mpr (Real.log_neg hr hr1)
  have hh := (lt_div_iff₀ hlogr).mp harr
  have hmass : 0 < μ.real (closedBall x r) :=
    ENNReal.toReal_pos (ne_of_gt ((Measure.mem_support_iff_forall x).mp hx _
      (closedBall_mem_nhds x hr))) (measure_ne_top μ _)
  have hle : μ.real (closedBall x r) ≤ r^a := by
    rw [Real.rpow_def_of_pos hr, ← Real.exp_log hmass]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [ENNReal.ofReal_rpow_of_pos hr,← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  exact ENNReal.ofReal_le_ofReal hle

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

theorem lower_dim_ge_of_limit (μ : Measure ℝ) [IsProbabilityMeasure μ] {d : ℝ}
    (hlim : ∀ᵐ x ∂μ, Tendsto
      (fun r => -Real.log (μ.real (closedBall x r)) / -Real.log r) (𝓝[>] 0) (𝓝 d)) :
    ENNReal.ofReal d ≤ lowerHausdorffDimension μ := by
  unfold lowerHausdorffDimension
  apply le_iInf
  intro B
  apply le_iInf
  intro hB
  apply le_iInf
  intro hpos
  by_cases htop : dimH B=⊤
  · rw [htop]; exact le_top
  rw [ENNReal.ofReal_le_iff_le_toReal htop]
  apply le_of_forall_lt_imp_le_of_dense
  intro a had
  by_cases ha : 0 ≤ a
  · have hh := positive_set_dim_ge μ ha (by
      filter_upwards [hlim,μ.support_mem_ae] with x hx hs
      exact eventual_upper_of_limit μ hs had hx) hB hpos
    exact (ENNReal.ofReal_le_iff_le_toReal htop).mp hh
  · exact (le_of_not_ge ha).trans ENNReal.toReal_nonneg

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

-- ---- from OAI.MeasureTheory.SelfSimilar.MassDimension ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

section
open scoped BigOperators ENNReal
open MeasureTheory
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal
namespace EntropyRateDimension.LocalMass
open MeasureEntropy

theorem dim_le_of_uniform_lower_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (E : Set ℝ) {B e R : ℝ} (he : 0 ≤ e) (hR : 0 < R)
    (hE : E ⊆ Icc (-B) B)
    (hball : ∀ x ∈ E, ∀ r : ℝ, 0 < r → r < R →
      (r/2)^e ≤ μ.real (ball x r)) : dimH E ≤ ENNReal.ofReal e := by
  classical
  let a : ℝ → Finset ℤ := fun s =>
    (Finset.Icc ⌊-B/s⌋ ⌊B/s⌋).filter (fun i => ∃ x ∈ E, label s 0 x=i)
  let cell : ℝ → ℤ → Set ℝ := fun s i => Icc (s*(i : ℝ)) (s*((i : ℝ)+1))
  have hdiam : ∀ s i, ediam (cell s i)=ENNReal.ofReal s := by
    intro s i
    change ediam (Icc (s*(i : ℝ)) (s*((i : ℝ)+1)))=ENNReal.ofReal s
    rw [Real.ediam_Icc]
    congr 1
    ring
  have hcover : ∀ s : ℝ, 0 < s → E ⊆ ⋃ i : a s, cell s i.val := by
    intro s hs x hx
    have hi : label s 0 x ∈ a s := by
      apply Finset.mem_filter.mpr
      refine ⟨?_,x,hx,rfl⟩
      simpa only [add_zero] using label_in_interval (u := 0) hs (hE hx)
    apply mem_iUnion.mpr
    refine ⟨⟨label s 0 x,hi⟩,?_⟩
    change s*(label s 0 x : ℝ) ≤ x ∧ x ≤ s*((label s 0 x : ℝ)+1)
    simp only [label,add_zero]
    constructor
    · have hh := (le_div_iff₀ hs).mp (Int.floor_le (x/s))
      simpa only [mul_comm] using hh
    · have hh := (div_lt_iff₀ hs).mp (Int.lt_floor_add_one (x/s))
      simpa only [mul_comm] using hh.le
  have hcount : ∀ s : ℝ, 0 < s → s < R →
      ((a s).card : ℝ)*s^e ≤ 3*(4 : ℝ)^e := by
    intro s hs hsR
    have has : ∀ i ∈ a s, ∃ x ∈ E, label s 0 x=i :=
      fun i hi => (Finset.mem_filter.mp hi).2
    let x : ℤ → ℝ := fun i => if hi : i ∈ a s then (has i hi).choose else 0
    have hx : ∀ i ∈ a s, x i ∈ E ∧ label s 0 (x i)=i := by
      intro i hi
      simp only [x,dite_eq_left hi]
      exact (has i hi).choose_spec
    have hh := good_labels_card_bound μ hs (a s) x (fun i hi => (hx i hi).2)
      (q := (s/4)^e) (fun i hi => by
        have hh := hball (x i) (hx i hi).1 (s/2) (by positivity) (by linarith)
        simpa only [show s/2/2=s/4 by ring] using hh)
    have h4 : (4 : ℝ)^e ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
    calc
      ((a s).card : ℝ)*s^e = (((a s).card : ℝ)*(s/4)^e)*(4 : ℝ)^e := by
        rw [Real.div_rpow hs.le (by norm_num)]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (by norm_num) _)
  let s : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hs : ∀ n, 0 < s n := fun n => by dsimp [s]; positivity
  have hsz : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hrz : Tendsto (fun n => ENNReal.ofReal (s n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsz
  have hh := Measure.hausdorffMeasure_le_liminf_sum e E
    (fun n => ENNReal.ofReal (s n)) hrz (fun n (i : a (s n)) => cell (s n) i.val)
    (Eventually.of_forall (fun n i => (hdiam _ _).le))
    (Eventually.of_forall (fun n => hcover _ (hs n)))
  have hlim : liminf (fun n => ∑ i : a (s n), ediam (cell (s n) i.val)^e) atTop ≤
      ENNReal.ofReal (3*(4 : ℝ)^e) := by
    refine liminf_le_of_frequently_le ?_ (by isBoundedDefault)
    apply Filter.Eventually.frequently
    filter_upwards [hsz.eventually (gt_mem_nhds hR)] with n hn
    calc
      (∑ i : a (s n), ediam (cell (s n) i.val)^e) =
          ENNReal.ofReal (((a (s n)).card : ℝ)*(s n)^e) := by
        simp only [hdiam,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,
          ENNReal.ofReal_rpow_of_pos (hs n)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hcount _ (hs n) hn)
  have hfin : Measure.hausdorffMeasure e E ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hh.trans hlim)
  have hdim := dimH_le_of_hausdorffMeasure_ne_top (d := ⟨e,he⟩) hfin
  exact hdim.trans_eq (ENNReal.coe_nnreal_eq ⟨e,he⟩)

theorem lower_dim_eq_of_limit (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hc : CompactlyCarried μ) {d : ℝ} (hd : 0 ≤ d)
    (hlim : ∀ᵐ x ∂μ, Tendsto
      (fun r => -Real.log (μ.real (closedBall x r)) / -Real.log r) (𝓝[>] 0) (𝓝 d)) :
    lowerHausdorffDimension μ = ENNReal.ofReal d := by
  apply le_antisymm _ (lower_dim_ge_of_limit μ hlim)
  have hub : ∀ e : ℝ, d < e → lowerHausdorffDimension μ ≤ ENNReal.ofReal e := by
    intro e hde
    have he := hd.trans hde.le
    obtain ⟨E,hE,hEc,R,hR,hball⟩ := large_uniform_mass_set μ he (by norm_num : (0 : ℝ)<1/2) (by
      filter_upwards [hlim,μ.support_mem_ae] with x hx hs
      exact eventual_lower_of_limit μ hs hde hx)
    obtain ⟨B,_,hB⟩ := hc
    let F := E ∩ Icc (-B) B
    have hF : MeasurableSet F := hE.inter measurableSet_Icc
    have hpos : 0 < μ F := by
      by_contra hn
      have hz : μ F=0 := le_antisymm (le_of_not_gt hn) bot_le
      have hEF : E =ᵐ[μ] F := by
        filter_upwards [show ∀ᵐ x ∂μ, x ∈ Icc (-B) B from ae_iff.mpr hB] with x hx
        apply propext
        exact ⟨fun h => ⟨h,hx⟩,fun h => h.1⟩
      have hez : μ E=0 := (measure_congr hEF).trans hz
      have hec : μ.real Eᶜ=1 := by simp [Measure.real,measure_compl hE (measure_ne_top μ E),hez]
      linarith
    calc
      lowerHausdorffDimension μ ≤ dimH F :=
        iInf_le_of_le F (iInf_le_of_le hF (iInf_le_of_le hpos le_rfl))
      _ ≤ ENNReal.ofReal e := dim_le_of_uniform_lower_mass μ F he hR inter_subset_right
        (fun x hx r hr hrR => hball x hx.1 r hr hrR)
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (d+1/((n : ℝ)+1))) atTop
      (𝓝 (ENNReal.ofReal d)) := by
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    simpa only [add_zero] using (tendsto_const_nhds (x := d)).add tendsto_one_div_add_atTop_nhds_zero_nat
  exact ge_of_tendsto ht (Eventually.of_forall (fun n => hub _ (by
    have : 0 < 1/((n : ℝ)+1) := by positivity
    linarith)))

end EntropyRateDimension.LocalMass

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

theorem selfSimilar_dimension (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) :
    lowerHausdorffDimension μ = ENNReal.ofReal (Coding.exponent S) :=
  LocalMass.lower_dim_eq_of_limit μ (by obtain ⟨B,hB,hc⟩ := S.selfSimilar_compact μ hμ; exact ⟨B,hB.le,hc⟩)
    (Coding.exponent_nonneg S) (S.selfSimilar_radial μ hμ)

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
theorem exponent_le_one (S : System ι) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : S.SelfSimilar μ) : Coding.exponent S ≤ 1 := by
  have hh := lowerHausdorffDimension_le_one μ
  rw [S.selfSimilar_dimension μ hμ] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1)).mp
    (by simpa only [ENNReal.ofReal_one] using hh)

end EntropyRateDimension.System

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.NoOverlaps ----
namespace OAI

universe uι uα

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension.Extensions

variable {ι : Type uι} [Fintype ι]

theorem noExactOverlaps_sameLength (S : System ι) (h : NoExactOverlaps S) :
    SameLengthNoExactOverlaps S := by
  intro n u v huv
  have he : List.ofFn u = List.ofFn v := h huv
  exact List.ofFn_injective he

theorem walkEntropy_eq_symbolEntropy [Nonempty ι] (S : System ι)
    (h : SameLengthNoExactOverlaps S) (n : ℕ) :
    S.walkEntropy n = (n : ℝ) * (symbolEntropy S / Real.log 2) := by
  classical
  have he := FiniteEntropy.observableEntropy_of_injective Finset.univ
    (S.wordWeight (n := n)) S.completeMap
    (fun w _ => (S.wordWeight_pos w).le) (h n)
  rw [S.map_entropy_as_observation, word_entropy] at he
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [← mul_div_assoc]
  apply (eq_div_iff h2).mpr
  exact he

theorem entropyRate_eq_symbolEntropy [Nonempty ι] (S : System ι)
    (h : SameLengthNoExactOverlaps S) :
    S.entropyRate = symbolEntropy S / Real.log 2 := by
  have hw (n : ℕ) : S.walkEntropy (n+1) / (n+1 : ℕ) =
      symbolEntropy S / Real.log 2 := by
    rw [walkEntropy_eq_symbolEntropy S h]
    have hn : (n+1 : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [hn]
  unfold System.entropyRate
  simp only [hw, Set.range_const, csInf_singleton]

theorem lyapunov_eq_naturalLyapunov (S : System ι) :
    S.lyapunov = naturalLyapunov S / Real.log 2 := by
  simp only [System.lyapunov, naturalLyapunov, ← mul_div_assoc,
    ← Finset.sum_div, neg_div]

theorem homogeneous_naturalLyapunov (S : System ι) {lam : ℝ} (hlam : 0 < lam)
    (hr : ∀ i, S.ratio i = lam) : naturalLyapunov S = Real.log (1/lam) := by
  simp only [naturalLyapunov, hr, abs_of_pos hlam, ← Finset.sum_mul,
    S.weight_sum, one_mul, one_div, Real.log_inv]

end EntropyRateDimension.Extensions

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.HomogeneousDimension ----
namespace OAI

universe uι

open MeasureTheory

namespace EntropyRateDimension.Extensions

/-- Same hypotheses and conclusion as homogeneous_dimension; independent proof branch. -/
theorem homogeneous_dimension_direct {ι : Type uι} [Fintype ι] [Nonempty ι] (S : System ι)
    {lam : ℝ} (hlam : 0 < lam) (hr : ∀ i, S.ratio i = lam)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (h : NoExactOverlaps S) :
    lowerHausdorffDimension μ =
      ENNReal.ofReal (min 1 (symbolEntropy S / Real.log (1/lam))) := by
  rw [← homogeneous_naturalLyapunov S hlam hr]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn : 0 < naturalLyapunov S := by
    have hp := S.lyapunov_pos
    rw [lyapunov_eq_naturalLyapunov] at hp
    exact (div_pos_iff_of_pos_right hlog).mp hp
  have hu : Coding.exponent S ≤ symbolEntropy S / naturalLyapunov S := by
    apply (le_div_iff₀ hn).mpr
    have hb := Coding.exponent_symbol_entropy_bound S
    change Coding.exponent S * S.lyapunov * Real.log 2 ≤ symbolEntropy S at hb
    rw [lyapunov_eq_naturalLyapunov] at hb
    have hc : Coding.exponent S * (naturalLyapunov S / Real.log 2) * Real.log 2 =
        Coding.exponent S * naturalLyapunov S := by
      field_simp [hlog.ne']
    rwa [hc] at hb
  have hl := homogeneous_exponent_lower_direct S hr μ hμ
  rw [entropyRate_eq_symbolEntropy S (noExactOverlaps_sameLength S h),
    lyapunov_eq_naturalLyapunov, div_div_div_cancel_right₀ hlog.ne'] at hl
  rw [S.selfSimilar_dimension μ hμ]
  exact congrArg ENNReal.ofReal (le_antisymm (le_min (S.exponent_le_one μ hμ) hu) hl)

end EntropyRateDimension.Extensions

end OAI

-- ---- mission target ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Extensions
universe uι
open scoped BigOperators ENNReal
open MeasureTheory
variable {ι : Type uι} [Fintype ι]

namespace OAI
namespace EntropyRateDimension
namespace Extensions
theorem _root_.solution {ι : Type uι} [Fintype ι] [Nonempty ι] (S : System ι)
    {lam : ℝ} (hlam : 0 < lam) (hr : ∀ i, S.ratio i = lam)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    (h : NoExactOverlaps S) :
    lowerHausdorffDimension μ =
      ENNReal.ofReal (min 1 (symbolEntropy S / Real.log (1/lam))) := by
  first
    | exact OAI.EntropyRateDimension.Extensions.homogeneous_dimension_direct S hlam hr μ hμ h
    | exact OAI.EntropyRateDimension.Extensions.homogeneous_dimension_direct
    | (apply OAI.EntropyRateDimension.Extensions.homogeneous_dimension_direct <;> assumption)
    | (intros; apply OAI.EntropyRateDimension.Extensions.homogeneous_dimension_direct <;> assumption)
end Extensions
end EntropyRateDimension
end OAI
