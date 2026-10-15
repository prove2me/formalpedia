-- Prove2me | solution 1 for OAI.IndependentProducts.representative_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T04:37:37.868675+00:00
-- url     : https://prove2.me/submissions/b0ed5be8-2d4b-4c6b-819f-8118d0c811bf

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ProductSpaces/TailCoefficients.lean:L20-L35
-- (upload_full_project.md Phase 4): solution for node OAI.IndependentProducts.representative_sum. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_IndependentProducts
import Definitions.Def_OAI_Analysis_ProductSpaces_TreeObstruction
import Definitions.Def_OAI_Analysis_ProductSpaces_PathMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_WeakNullity
import Definitions.Def_OAI_Analysis_ProductSpaces_ScalarBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianMoments
import Definitions.Def_OAI_Analysis_ProductSpaces_GaussianExcess
import Definitions.Def_OAI_Analysis_ProductSpaces_RandomSigns
import Definitions.Def_OAI_Analysis_ProductSpaces_MidpointModulus
import Definitions.Def_OAI_Analysis_ProductSpaces_ConditionalBounds
import Definitions.Def_OAI_Analysis_ProductSpaces_FiniteHeads
import Definitions.Def_OAI_Analysis_ProductSpaces_Resampling
import Definitions.Def_OAI_Analysis_ProductSpaces_ClosedTails
import Definitions.Def_OAI_Analysis_ProductSpaces_TailCoefficients

-- ---- from OAI.Analysis.ProductSpaces.TailCoefficients ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

universe uι uκ

namespace IndependentProducts
section FiniteRepresentatives
variable (μ : Measure ℝ) [hμprob : IsProbabilityMeasure μ]
  (h₂ : MemLp (fun w : ℝ => w) 2 μ)

omit hμprob in
lemma representative_sum [IsProbabilityMeasure μ] {ι : Type uι} [Fintype ι]
    (x : ι → productSpan μ)
    (f : ι → Sample → ℝ) (hf : ∀ i, (x i).val =ᵐ[productMeasure μ] f i) (a : ι → ℝ) :
    ((∑ i, a i • x i).val : Sample → ℝ) =ᵐ[productMeasure μ] fun ω => ∑ i, a i * f i ω := by
  have hs : (∑ i, a i • x i).val = ∑ i, a i • (x i).val := by simp
  rw [hs]
  have ha : ∀ i, (a i • (x i).val : Lp ℝ 1 (productMeasure μ)) =ᵐ[productMeasure μ]
      fun ω => a i * f i ω := by
    intro i
    filter_upwards [Lp.coeFn_smul (a i) (x i).val, hf i] with ω hω hi
    simpa only [Pi.smul_apply, smul_eq_mul, hi] using hω
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => a i • (x i).val),
    ae_all_iff.mpr ha] with ω hsum hall
  rw [hsum]
  exact Finset.sum_congr rfl (fun i _ => hall i)

namespace FiniteHead
variable (T : FiniteHead)

end FiniteHead
end FiniteRepresentatives

namespace FiniteHead
section FiniteTailData
variable {ι : Type uι} {κ : Type uκ} [hιfinite : Fintype ι] [Fintype κ] [DecidableEq ι]
variable (T : FiniteHead) (e : ι → T.Boundary) (v : κ → Vertex) (j : κ → ι) (a : κ → ℝ)

end FiniteTailData
end FiniteHead
end IndependentProducts

end

end OAI

-- ---- platform node ----
open OAI OAI.IndependentProducts
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
universe uι uκ
variable (μ : Measure ℝ) [hμprob : IsProbabilityMeasure μ]
  (h₂ : MemLp (fun w : ℝ => w) 2 μ)

omit hμprob in
theorem solution [IsProbabilityMeasure μ] {ι : Type uι} [Fintype ι]
    (x : ι → productSpan μ)
    (f : ι → Sample → ℝ) (hf : ∀ i, (x i).val =ᵐ[productMeasure μ] f i) (a : ι → ℝ) :
    ((∑ i, a i • x i).val : Sample → ℝ) =ᵐ[productMeasure μ] fun ω => ∑ i, a i * f i ω := by
  first
    | exact OAI.IndependentProducts.representative_sum x f hf a
    | exact OAI.IndependentProducts.representative_sum μ h₂ x f hf a
    | exact OAI.IndependentProducts.representative_sum
    | (apply OAI.IndependentProducts.representative_sum <;> assumption)
    | (intros; apply OAI.IndependentProducts.representative_sum <;> assumption)
