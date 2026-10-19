-- Prove2me | solution 1 for OAI.EntropyRateDimension.System.blocks_entropyRate_lower
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:41:01.041413+00:00
-- url     : https://prove2.me/submissions/f5552251-d2de-47f4-895c-38752e689eac

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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordAverage
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
universe uι uα uβ uγ
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System in
theorem hn2_wa_append {ι : Type*} [Fintype ι] (S : System ι) (l1 l2 : List ι) :
    S.wordAffine (l1 ++ l2) = ((S.wordAffine l1).1 * (S.wordAffine l2).1,
      (S.wordAffine l1).1 * (S.wordAffine l2).2 + (S.wordAffine l1).2) := by
  induction l1 with
  | nil => simp [System.wordAffine]
  | cons i l ih =>
    simp only [List.cons_append, System.wordAffine, ih]
    ext <;> simp only <;> ring

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System in
theorem hn2_blocks_wa {ι : Type*} [Fintype ι] (S : System ι) {b : ℕ} (hb : 0 < b)
    (L : List (Fin b → ι)) :
    (S.blocks hb).wordAffine L = S.wordAffine (L.map List.ofFn).flatten := by
  induction L with
  | nil => rfl
  | cons u L ih =>
    simp only [System.wordAffine, ih, List.map_cons, List.flatten_cons, hn2_wa_append]
    rfl

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System in
theorem hn2_blocks_cm {ι : Type*} [Fintype ι] (S : System ι) {b : ℕ} (hb : 0 < b) {m : ℕ}
    (w : Fin m → Fin b → ι) :
    (S.blocks hb).completeMap w = S.completeMap (flattenWordEquiv m b w) := by
  unfold System.completeMap
  rw [hn2_blocks_wa, List.ofFn_mul, List.map_ofFn]
  congr 2
  congr 1
  funext i
  simp only [Function.comp]
  congr 1
  funext j
  have : (⟨i * b + j, by
      calc ↑i * b + ↑j < (↑i + 1) * b := by rw [Nat.add_mul, Nat.one_mul]; omega
        _ ≤ m * b := Nat.mul_le_mul_right _ i.2⟩ : Fin (m*b)) = finProdFinEquiv (i, j) := by
    ext; simp [finProdFinEquiv]; ring
  rw [this, flattenWordEquiv_apply]

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System in
theorem hn2_blocks_ww {ι : Type*} [Fintype ι] (S : System ι) {b : ℕ} (hb : 0 < b) {m : ℕ}
    (w : Fin m → Fin b → ι) :
    (S.blocks hb).wordWeight w = S.wordWeight (flattenWordEquiv m b w) := by
  unfold System.wordWeight
  rw [← finProdFinEquiv.prod_comp, Fintype.prod_prod_type]
  simp only [flattenWordEquiv_apply]
  rfl

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System in
theorem hn2_blocks_walk {ι : Type*} [Fintype ι] (S : System ι) {b : ℕ} (hb : 0 < b) (m : ℕ) :
    (S.blocks hb).walkEntropy m = S.walkEntropy (m*b) := by
  classical
  set F := flattenWordEquiv (ι := ι) m b
  have hsupp : (S.blocks hb).mapSupport m = S.mapSupport (m*b) := by
    unfold System.mapSupport
    ext g
    simp only [Finset.mem_image, Finset.mem_univ, true_and, hn2_blocks_cm]
    constructor
    · rintro ⟨w, h⟩; exact ⟨F w, h⟩
    · rintro ⟨v, h⟩; exact ⟨F.symm v, by simp [F, h]⟩
  have hmass : ∀ g, (S.blocks hb).mapMass m g = S.mapMass (m*b) g := by
    intro g
    unfold System.mapMass
    rw [Finset.sum_filter, Finset.sum_filter]
    simp only [hn2_blocks_cm, hn2_blocks_ww]
    exact F.sum_comp (fun v => if S.completeMap v = g then S.wordWeight v else 0)
  unfold System.walkEntropy
  rw [hsupp]
  simp only [hmass]

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System in
theorem hn2_walk_nonneg {ι : Type*} [Fintype ι] (S : System ι) (n : ℕ) : 0 ≤ S.walkEntropy n := by
  unfold System.walkEntropy
  apply div_nonneg _ (Real.log_nonneg (by norm_num))
  apply Finset.sum_nonneg
  intro g hg
  apply Real.negMulLog_nonneg (S.mapMass_pos hg).le
  rw [← S.mapMass_sum n]
  exact Finset.single_le_sum (fun g hg => (S.mapMass_pos hg).le) hg

theorem solution (S : System ι) {b : ℕ} (hb : 0 < b) :
    (b : ℝ)*S.entropyRate ≤ (S.blocks hb).entropyRate := by
  have hbdd : BddBelow (Set.range fun n : ℕ => S.walkEntropy (n + 1) / (n + 1 : ℕ)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact div_nonneg (hn2_walk_nonneg S _) (Nat.cast_nonneg _)
  unfold System.entropyRate
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨m, rfl⟩
  simp only
  rw [hn2_blocks_walk]
  have hn : (m+1)*b - 1 + 1 = (m+1)*b := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))
  have h1 := csInf_le hbdd ⟨(m+1)*b - 1, rfl⟩
  simp only [hn] at h1
  calc (b:ℝ) * sInf (Set.range fun n : ℕ => S.walkEntropy (n + 1) / (n + 1 : ℕ))
      ≤ (b:ℝ) * (S.walkEntropy ((m+1)*b) / (((m+1)*b : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 hb'.le
    _ = S.walkEntropy ((m + 1) * b) / ((m + 1 : ℕ) : ℝ) := by
        push_cast
        field_simp

