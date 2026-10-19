-- Prove2me | solution 1 for OAI.Problem313.graphVariance_bound_of_spectral_inputs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:42:36.936989+00:00
-- url     : https://prove2.me/submissions/8b3dfade-a04c-4f10-a51f-049428992bfd

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/GraphVarianceBound.lean:L14-L50
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.graphVariance_bound_of_spectral_inputs. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype
import Definitions.Def_OAI_Combinatorics_SharpThreshold_ProjectionIdentities
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierProjection
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOptionExpectation
import Theorems.Thm_OAI_Problem313_sqrt_block_size_bounds
import Theorems.Thm_OAI_Problem313_variance_bound_of_fourier_inputs

-- ---- from OAI.Combinatorics.SharpThreshold.BlockSize ----
namespace OAI

noncomputable section

namespace Problem313

/-- The square-root block retains at least one third of the original logarithm. -/
theorem log_sqrt_block_lower (n : ℕ) (hn : 2 ≤ n)
    (ht : 16 ≤ Real.log (n : ℝ)) :
    Real.log (n : ℝ) / 3 ≤ Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hsqrtpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hhalf := (sqrt_block_size_bounds n hn ht).2.2
  have hlog := Real.log_le_log (by positivity : 0 < Real.sqrt (n : ℝ) / 2) hhalf
  rw [Real.log_div (ne_of_gt hsqrtpos) (by norm_num),
    Real.log_sqrt (le_of_lt hnpos)] at hlog
  have htwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  linarith

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.Probability ----
namespace OAI

noncomputable section
namespace Problem313

theorem graphWeight_nonneg {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (x : GraphConfig n) : 0 ≤ graphWeight p x := by
  classical
  apply Finset.prod_nonneg
  intro e he
  split_ifs <;> linarith

theorem edgeInfluence_nonneg {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : GraphConfig n → Bool) (e : GraphEdge n) : 0 ≤ edgeInfluence p f e := by
  classical
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · exact graphWeight_nonneg hp hp1 x
  · exact le_rfl

theorem totalInfluence_nonneg {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (f : GraphConfig n → Bool) : 0 ≤ totalInfluence p f := by
  classical
  apply Finset.sum_nonneg
  intro e he
  exact edgeInfluence_nonneg hp hp1 f e

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.GraphVarianceBound ----
namespace OAI

noncomputable section

namespace Problem313

/-- The graph-level variance reduction, with the two spectral identities and
large-scale block capture supplied explicitly. No symmetry is needed after
these inputs have been obtained. -/
theorem graphVariance_bound_of_spectral_inputs {n : ℕ}
    (f : GraphConfig n → Bool) (p : ℝ) (hn : 2 ≤ n) (hp : 0 < p) (hp1 : p < 1)
    (hvariance : graphVariance p f =
      ∑ S : Finset (GraphEdge n) with S.Nonempty,
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2)
    (hdirichlet : (∑ S : Finset (GraphEdge n), (S.card : ℝ) *
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2) =
      p * (1 - p) * totalInfluence p f)
    (hcapture : 16 ≤ Real.log (n : ℝ) →
      (∑ S : Finset (GraphEdge n) with S.Nonempty ∧
          (S.card : ℝ) ≤ (Real.sqrt (p * (1 - p)) *
            Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2,
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2) ≤
      (4 * (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ)) * totalInfluence p f) :
    graphVariance p f ≤
      ((2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2) * totalInfluence p f := by
  classical
  have hbias : 0 < p * (1 - p) := mul_pos hp (sub_pos.mpr hp1)
  have hsigma : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.2 hbias
  have hsigma_sq : Real.sqrt (p * (1 - p)) ^ 2 ≤ 1 / 4 := by
    rw [Real.sq_sqrt hbias.le]
    nlinarith [sq_nonneg (p - 1 / 2)]
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  apply variance_bound_of_fourier_inputs
    (BiasedFourier.coeff p (fun x => boolReal (f x)))
    (graphVariance p f) (Real.sqrt (p * (1 - p)))
    (totalInfluence p f) (Real.log (n : ℝ))
    hsigma hsigma_sq (totalInfluence_nonneg hp.le hp1.le f) hlog hvariance
  · simpa only [Real.sq_sqrt hbias.le] using hdirichlet
  · intro ht
    refine ⟨(⌊Real.sqrt (n : ℝ)⌋₊ : ℝ), ?_, log_sqrt_block_lower n hn ht, hcapture ht⟩
    have hm := (sqrt_block_size_bounds n hn ht).1
    exact_mod_cast (by omega : 0 < ⌊Real.sqrt (n : ℝ)⌋₊)

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution : type_of% @_root_.OAI.Problem313.graphVariance_bound_of_spectral_inputs := @_root_.OAI.Problem313.graphVariance_bound_of_spectral_inputs
