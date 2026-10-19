-- Prove2me | solution 2 for OAI.EntropyRateDimension.Windows.retained_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T11:52:46.241217+00:00
-- url     : https://prove2.me/submissions/ed86f743-6433-46e6-bed2-b5ac663a5993

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/WindowCount.lean:L11-L50
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.Windows.retained_sum_le. The node keeps its source
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
import Theorems.Thm_OAI_EntropyRateDimension_Windows_multiples_disjoint
import Theorems.Thm_OAI_EntropyRateDimension_Windows_sum_disjoint_drops_le

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

end Windows

end EntropyRateDimension

end

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

end EntropyRateDimension.Windows

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.Windows
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.Windows.retained_sum_le := @_root_.OAI.EntropyRateDimension.Windows.retained_sum_le
