-- Prove2me | solution 2 for OAI.EntropyRateDimension.System.blocks_entropyRate_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:40:03.441879+00:00
-- url     : https://prove2.me/submissions/b711d454-2701-4c0e-9339-be05ec1cea32

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/BlockWords.lean:L99-L112
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.System.blocks_entropyRate_lower. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_SuffixLaw
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WordAverage
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_BlockWords

-- ---- from OAI.MeasureTheory.SelfSimilar.Basic ----
namespace OAI

universe uι

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace System
variable {ι : Type uι} [Fintype ι]

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

end System

namespace System
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

end System

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

-- ---- from OAI.MeasureTheory.SelfSimilar.BlockWords ----
namespace OAI

universe uι uα uβ uγ

namespace EntropyRateDimension.FiniteEntropy
open scoped BigOperators

theorem observableEntropy_reindex {α : Type uα} {β : Type uβ} {γ : Type uγ} [Fintype α] [Fintype β] [DecidableEq γ]
    (e : α ≃ β) (p : β → ℝ) (f : β → γ) :
    observableEntropy Finset.univ (fun a => p (e a)) (fun a => f (e a))=
      observableEntropy Finset.univ p f := by
  classical
  have hi : Finset.univ.image (fun a => f (e a))=Finset.univ.image f := by
    ext c
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    exact ⟨fun ⟨a,ha⟩ => ⟨e a,ha⟩,fun ⟨b,hb⟩ => ⟨e.symm b,by simpa using hb⟩⟩
  have hm (c : γ) : mass Finset.univ (fun a => p (e a)) (fun a => f (e a)) c=
      mass Finset.univ p f c := by
    simp only [mass,Finset.sum_filter]
    exact e.sum_comp (fun b => if f b=c then p b else 0)
  simp only [observableEntropy,entropy,hi,hm]

end EntropyRateDimension.FiniteEntropy

namespace EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal
variable {ι : Type uι} [Fintype ι]

theorem wordAffine_blocks (S : System ι) {b : ℕ} (hb : 0 < b) (W : List (Fin b → ι)) :
    (S.blocks hb).wordAffine W=S.wordAffine (W.flatMap List.ofFn) := by
  induction W with
  | nil => rfl
  | cons w W ih =>
    rw [wordAffine,ih,List.flatMap_cons,S.wordAffine_append]
    rfl

theorem completeMap_flatten (S : System ι) {b : ℕ} (hb : 0 < b) {n : ℕ}
    (w : Fin n → Fin b → ι) :
    (S.blocks hb).completeMap w=S.completeMap (flattenWordEquiv n b w) := by
  rw [completeMap,S.wordAffine_blocks,completeMap,List.ofFn_mul]
  congr 1
  rw [List.flatMap,List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  apply congrArg List.ofFn
  funext j
  convert (flattenWordEquiv_apply n b w i j).symm using 1
  apply congrArg (flattenWordEquiv n b w)
  apply Fin.ext
  simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

theorem wordWeight_flatten (S : System ι) {b : ℕ} (hb : 0 < b) {n : ℕ}
    (w : Fin n → Fin b → ι) :
    (S.blocks hb).wordWeight w=S.wordWeight (flattenWordEquiv n b w) := by
  simp only [wordWeight,blocks]
  rw [← finProdFinEquiv.prod_comp (fun j => S.weight (flattenWordEquiv n b w j)),
    Fintype.prod_prod_type]
  simp only [flattenWordEquiv_apply]

theorem blocks_walkEntropy (S : System ι) {b : ℕ} (hb : 0 < b) (n : ℕ) :
    (S.blocks hb).walkEntropy n=S.walkEntropy (n*b) := by
  have he := FiniteEntropy.observableEntropy_reindex (flattenWordEquiv n b)
    S.wordWeight S.completeMap
  simp only [← S.wordWeight_flatten hb,← S.completeMap_flatten hb] at he
  rw [(S.blocks hb).map_entropy_as_observation,S.map_entropy_as_observation] at he
  exact mul_right_cancel₀ (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne' he

theorem blocks_entropyRate_lower (S : System ι) {b : ℕ} (hb : 0 < b) :
    (b : ℝ)*S.entropyRate ≤ (S.blocks hb).entropyRate := by
  apply le_csInf ⟨_,Set.mem_range_self 0⟩
  intro x hx
  obtain ⟨n,rfl⟩ := hx
  dsimp only
  rw [S.blocks_walkEntropy]
  have hpos : 0 < (n+1)*b := Nat.mul_pos (Nat.succ_pos n) hb
  have hh := S.entropyRate_le ((n+1)*b-1)
  rw [Nat.sub_add_cancel hpos] at hh
  have hh' := (le_div_iff₀ (by exact_mod_cast hpos : (0 : ℝ)<((n+1)*b : ℕ))).mp hh
  apply (le_div_iff₀ (by positivity : (0 : ℝ)<(n+1 : ℕ))).mpr
  push_cast at hh' ⊢
  nlinarith

end EntropyRateDimension.System

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.System
open MeasureTheory
open scoped BigOperators ENNReal


theorem solution.{uι} : type_of% @_root_.OAI.EntropyRateDimension.System.blocks_entropyRate_lower.{uι} := @_root_.OAI.EntropyRateDimension.System.blocks_entropyRate_lower.{uι}
