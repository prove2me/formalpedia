-- Prove2me | solution 1 for OAI.EntropyRateDimension.Extensions.noExactOverlaps_iff_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T15:35:31.8163+00:00
-- url     : https://prove2.me/submissions/302e5ea2-d61b-46af-ba34-d7d7390fb583

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/NoOverlaps.lean:L123-L138
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Extensions.noExactOverlaps_iff_nonempty. The node keeps its source
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

end System
end EntropyRateDimension

end OAI

-- ---- from OAI.MeasureTheory.SelfSimilar.NoOverlaps ----
namespace OAI

universe uι uα

open scoped BigOperators ENNReal
open MeasureTheory

namespace EntropyRateDimension.Extensions

variable {ι : Type uι} [Fintype ι]

theorem wordAffine_slope_pos (S : System ι) (u : List ι) :
    0 < |(S.wordAffine u).1| := by
  induction u with
  | nil => simp [System.wordAffine]
  | cons i u ih =>
    simpa only [System.wordAffine, abs_mul] using mul_pos (S.ratio_pos i) ih

theorem wordAffine_slope_le_one (S : System ι) (u : List ι) :
    |(S.wordAffine u).1| ≤ 1 := by
  induction u with
  | nil => simp [System.wordAffine]
  | cons i u ih =>
    simpa only [System.wordAffine, abs_mul, mul_one] using
      mul_le_mul (S.ratio_lt_one i).le ih (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)

theorem wordAffine_slope_lt_one (S : System ι) {u : List ι} (hu : u ≠ []) :
    |(S.wordAffine u).1| < 1 := by
  cases u with
  | nil => exact (hu rfl).elim
  | cons i u =>
    change |S.ratio i * (S.wordAffine u).1| < 1
    rw [abs_mul]
    calc
      _ ≤ |S.ratio i| * 1 :=
        mul_le_mul_of_nonneg_left (wordAffine_slope_le_one S u) (abs_nonneg _)
      _ < 1 := by simpa using S.ratio_lt_one i

/-- An equal prefix map cannot have a nonempty residual contraction. -/
theorem equal_map_prefix (S : System ι) (u w : List ι)
    (he : S.wordAffine u = S.wordAffine (u ++ w)) : w = [] := by
  have hs := congrArg Prod.fst he
  rw [S.wordAffine_append] at hs
  have hn : (S.wordAffine u).1 ≠ 0 := abs_pos.mp (wordAffine_slope_pos S u)
  have hw : (S.wordAffine w).1 = 1 := by
    apply mul_left_cancel₀ hn
    simpa using hs.symm
  by_contra hne
  have hc := wordAffine_slope_lt_one S hne
  rw [hw, abs_one] at hc
  exact (lt_irrefl 1) hc

/-- Adding the empty word does not strengthen the usual overlap assumption. -/
theorem noExactOverlaps_iff_nonempty (S : System ι) :
    NoExactOverlaps S ↔ ∀ u v : List ι, u ≠ [] → v ≠ [] →
      S.wordAffine u = S.wordAffine v → u = v := by
  constructor
  · intro h u v _ _ he
    exact h he
  · intro h u v he
    by_cases hu : u = []
    · subst u
      have hv := equal_map_prefix S [] v (by simpa using he)
      exact hv.symm
    by_cases hv : v = []
    · subst v
      exact equal_map_prefix S [] u (by simpa using he.symm)
    exact h u v hu hv he

end EntropyRateDimension.Extensions

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Extensions
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.Extensions.noExactOverlaps_iff_nonempty.{uι} := @_root_.OAI.EntropyRateDimension.Extensions.noExactOverlaps_iff_nonempty.{uι}
