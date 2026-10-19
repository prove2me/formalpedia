-- Prove2me | solution 2 for OAI.EntropyRateDimension.System.depth_bad_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:31:35.929002+00:00
-- url     : https://prove2.me/submissions/ad98f3cd-dbea-41f5-82a1-b91ac0596427

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FiniteVariance.lean:L85-L109
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.System.depth_bad_mass_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteDistribution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_MeasureEntropy
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RandomGrid
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Boundary
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TranslationGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FairPairs
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ProductLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_GridCoupling
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteRefinement
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SumsetBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordTypes
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_DigitSumset
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Bernoulli
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Coding
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_InvariantLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallRatios
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallIntegrability
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_CodingIntegrals
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ErgodicAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TriangularAverages
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BallLimits
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadiusGrowth
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RadialLimit
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_ExactDimension
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_UpperBound
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Conditioning
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairGain
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TypedLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_TailConvolution
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteVariance

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

theorem wordWeight_cons (S : System ι) {n : ℕ} (i : ι) (w : Fin n → ι) :
    S.wordWeight (Fin.cons i w) = S.weight i*S.wordWeight w := by
  simp only [wordWeight,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]

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

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
open scoped BigOperators


theorem solution.{uα} : type_of% @_root_.OAI.EntropyRateDimension.System.depth_bad_mass_bound.{uα} := @_root_.OAI.EntropyRateDimension.System.depth_bad_mass_bound.{uα}
