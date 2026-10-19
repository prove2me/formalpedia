-- Prove2me | solution 1 for OAI.EntropyRateDimension.System.selfSimilar_words
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:07:28.393595+00:00
-- url     : https://prove2.me/submissions/d4dd1c32-4181-45fc-ad9c-88c70f5bbaf0

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

open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
universe uι uM
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]
theorem h41n_map_fsum {κ : Type*} (s : Finset κ) (m : κ → Measure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) : (∑ i ∈ s, m i).map f = ∑ i ∈ s, (m i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.map_add _ _ hf, ih]

theorem h41n_wordAffine_append {ι : Type*} [Fintype ι] (S : System ι) (l1 l2 : List ι) (x : ℝ) :
    (S.wordAffine (l1 ++ l2)).1 * x + (S.wordAffine (l1 ++ l2)).2 =
      (S.wordAffine l1).1 * ((S.wordAffine l2).1 * x + (S.wordAffine l2).2) + (S.wordAffine l1).2 := by
  induction l1 with
  | nil => simp [System.wordAffine]
  | cons i l ih =>
    simp only [List.cons_append, System.wordAffine]
    linear_combination S.ratio i * ih

theorem h41n_wordMap_append {ι : Type*} [Fintype ι] (S : System ι) {m n : ℕ}
    (v1 : Fin m → ι) (v2 : Fin n → ι) :
    S.wordMap (Fin.append v1 v2) = S.wordMap v1 ∘ S.wordMap v2 := by
  funext x
  simp only [System.wordMap, System.completeMap, Function.comp, List.ofFn_fin_append]
  exact h41n_wordAffine_append S _ _ x

theorem h41n_wordMap_one {ι : Type*} [Fintype ι] (S : System ι) (i : ι) :
    S.wordMap (fun _ : Fin 1 => i) = S.affine i := by
  funext x
  simp [System.wordMap, System.completeMap, System.wordAffine, System.affine]

theorem h41n_wordWeight_append {ι : Type*} [Fintype ι] (S : System ι) {m n : ℕ}
    (v1 : Fin m → ι) (v2 : Fin n → ι) :
    S.wordWeight (Fin.append v1 v2) = S.wordWeight v1 * S.wordWeight v2 := by
  simp only [System.wordWeight]
  rw [Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem solution (S : System ι) (μ : Measure ℝ) (hμ : S.SelfSimilar μ) (n : ℕ) :
    μ = ∑ w : Fin n → ι, ENNReal.ofReal (S.wordWeight w) • μ.map (S.wordMap w) := by
  have haff : ∀ i, Measurable (S.affine i) := fun i => by unfold System.affine; fun_prop
  induction n with
  | zero =>
    rw [Fintype.sum_unique]
    have h1 : S.wordWeight (default : Fin 0 → ι) = 1 := by simp [System.wordWeight]
    have h2 : S.wordMap (default : Fin 0 → ι) = id := by
      funext x; simp [System.wordMap, System.completeMap, System.wordAffine]
    rw [h1, h2, Measure.map_id]
    simp
  | succ n ih =>
    have hsplit : ∀ w : Fin n → ι, μ.map (S.wordMap w) =
        ∑ i, ENNReal.ofReal (S.weight i) • μ.map (S.wordMap w ∘ S.affine i) := by
      intro w
      conv_lhs => rw [hμ]
      rw [h41n_map_fsum _ _ (S.wordMap_measurable w)]
      apply Finset.sum_congr rfl
      intro i _
      rw [Measure.map_smul, Measure.map_map (S.wordMap_measurable w) (haff i)]
    conv_lhs => rw [ih]
    rw [← (Fin.appendEquiv n 1).sum_comp, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro w _
    rw [hsplit, Finset.smul_sum, ← (Equiv.funUnique (Fin 1) ι).symm.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    have e1 : (Equiv.funUnique (Fin 1) ι).symm i = fun _ => i := rfl
    rw [smul_smul, ← ENNReal.ofReal_mul (S.wordWeight_pos w).le]
    simp only [e1]
    rw [show (Fin.appendEquiv n 1) (w, fun _ => i) = Fin.append w (fun _ => i) from rfl]
    rw [h41n_wordWeight_append, h41n_wordMap_append, h41n_wordMap_one]
    congr 2
    simp [System.wordWeight]

