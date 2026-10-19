-- Prove2me | solution 2 for OAI.EntropyRateDimension.Typed.select_separated_bands
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:10:05.09453+00:00
-- url     : https://prove2.me/submissions/2b8fb5b3-b4ad-42af-a933-e9b18ad288e7

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/BandSelection.lean:L34-L78
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Typed.select_separated_bands. The node keeps its source
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
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_EntropyBudget
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_RetainedLoss
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_PairBands
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowCount
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_WindowGain

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

end EntropyRateDimension.Typed

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Typed
open scoped BigOperators


theorem solution.{uα,uβ} : type_of% @_root_.OAI.EntropyRateDimension.Typed.select_separated_bands.{uα,uβ} := @_root_.OAI.EntropyRateDimension.Typed.select_separated_bands.{uα,uβ}
