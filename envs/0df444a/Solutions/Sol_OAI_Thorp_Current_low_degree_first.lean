-- Prove2me | solution 1 for OAI.Thorp.Current.low_degree_first
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:35:45.764249+00:00
-- url     : https://prove2.me/submissions/4eb130b6-3418-4848-b2b7-5e33c2f0ea19

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/FirstFourier.lean:L15-L41
-- (upload_full_project.md Phase 4): solution for node OAI.Thorp.Current.low_degree_first. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
import Definitions.Def_OAI_Probability_ThorpShuffle_Classification
import Definitions.Def_OAI_Probability_ThorpShuffle_LinearExtensions
import Definitions.Def_OAI_Probability_ThorpShuffle_ExtensionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_PartitionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_DegreeBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_FirstMoment
import Definitions.Def_OAI_Probability_ThorpShuffle_Reynolds
import Definitions.Def_OAI_Probability_ThorpShuffle_FourierFamilies
import Definitions.Def_OAI_Probability_ThorpShuffle_JointProjectors
import Definitions.Def_OAI_Probability_ThorpShuffle_ProductProjectors
import Definitions.Def_OAI_Probability_ThorpShuffle_SymmetricFamilies
import Definitions.Def_OAI_Probability_ThorpShuffle_BlockEmbedding

-- ---- from OAI.Probability.ThorpShuffle.FirstFourier ----
namespace OAI

universe uE

noncomputable section

namespace Thorp.Current
open scoped BigOperators Classical ComplexConjugate InnerProductSpace
open Thorp.Fourier

/-- The first inverse-degree moment yields a `D^(3/8)` orbit bound.
The filter is precisely `degree ≤ D^(1/8)`, written without a root. -/
lemma low_degree_first {H : Type} [Group H] [Fintype H]
    (F : Fourier.Family H) (D : ℕ) :
    (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ 8 ≤ D), (F.degree b : ℝ)^2) ≤
      (D : ℝ) ^ (3 / 8 : ℝ) * ∑ b, (F.degree b : ℝ)⁻¹ := by
  let s := Finset.univ.filter (fun b => F.degree b ^ 8 ≤ D)
  have hp (b : F.Index) : (0 : ℝ) < F.degree b := by exact_mod_cast F.positive b
  have hsmall : ∑ b ∈ s, (F.degree b : ℝ)⁻¹ ≤ ∑ b, (F.degree b : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun b _ _ => inv_nonneg.mpr (hp b).le)
  calc
    _ ≤ ∑ b ∈ s, (D : ℝ) ^ (3 / 8 : ℝ) * (F.degree b : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro b hb
      have hbD : (F.degree b : ℝ)^8 ≤ D := by
        exact_mod_cast (Finset.mem_filter.mp hb).2
      apply (le_mul_inv_iff₀ (hp b)).mpr
      calc
        (F.degree b : ℝ)^2 * F.degree b = (F.degree b : ℝ)^3 := by ring
        _ = ((F.degree b : ℝ)^8) ^ (3 / 8 : ℝ) := by
          rw [← Real.rpow_natCast_mul (hp b).le]
          norm_num
        _ ≤ _ := Real.rpow_le_rpow (by positivity) hbD (by norm_num)
    _ = (D : ℝ) ^ (3 / 8 : ℝ) * ∑ b ∈ s, (F.degree b : ℝ)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (Real.rpow_nonneg (Nat.cast_nonneg D) _)

end Thorp.Current

end

end OAI

-- ---- platform node ----
open OAI OAI.Thorp OAI.Thorp.Current
open scoped BigOperators Classical ComplexConjugate InnerProductSpace
open Thorp.Fourier


theorem solution : type_of% @_root_.OAI.Thorp.Current.low_degree_first := @_root_.OAI.Thorp.Current.low_degree_first
