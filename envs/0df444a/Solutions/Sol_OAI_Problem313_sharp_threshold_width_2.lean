-- Prove2me | solution 2 for OAI.Problem313.sharp_threshold_width
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:50:26.766979+00:00
-- url     : https://prove2.me/submissions/1a743a4d-5306-4618-8dd7-bc07b4b9f55b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/Main.lean:L28-L30
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.Problem313.sharp_threshold_width.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_Problem313_sharp_threshold_width) verbatim and is proved by it.
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
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Quantile
import Theorems.Thm_OAI_Problem313_BiasedFourier_low_degree_estimate_of_noise
import Theorems.Thm_OAI_Problem313_BiasedFourier_parseval
import Theorems.Thm_OAI_Problem313_BiasedFourier_restriction_mass_subtype
import Theorems.Thm_OAI_Problem313_BiasedFourier_synthesis_fourth_bound
import Theorems.Thm_OAI_Problem313_block_conditional_low_degree_bound_of_estimate
import Theorems.Thm_OAI_Problem313_graphQuantile_width_of_variance_bound
import Theorems.Thm_OAI_Problem313_graphVariance_bound_of_spectral_inputs
import Theorems.Thm_OAI_Problem313_graphVariance_eq_mean_mul
import Theorems.Thm_OAI_Problem313_graph_fourier_captured_mass_of_block_bound
import Theorems.Thm_OAI_Problem313_graph_fourier_dirichlet
import Theorems.Thm_OAI_Problem313_sqrt_block_size_bounds

-- ---- from OAI.Combinatorics.SharpThreshold.FourierVariance ----
namespace OAI

universe u v

noncomputable section

open scoped BigOperators Classical

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι]

end Problem313.BiasedFourier

namespace Problem313

open BiasedFourier

theorem graph_second_moment_eq_mean {n : ℕ} (p : ℝ) (f : GraphConfig n → Bool) :
    (∑ x, BiasedFourier.weight p x * boolReal (f x) ^ 2) = graphMean p f := by
  apply Finset.sum_congr rfl
  intro x hx
  simp only [fourier_weight_eq_graphWeight]
  congr 1
  cases f x <;> norm_num [boolReal]

/-- The graph variance bridge needs only Parseval on the real-valued Boolean encoding. -/
theorem graphVariance_eq_fourier_nonempty_of_parseval {n : ℕ} (p : ℝ)
    (f : GraphConfig n → Bool)
    (hparseval : (∑ x, BiasedFourier.weight p x * boolReal (f x) ^ 2) =
      ∑ S : Finset (GraphEdge n), coeff p (fun x => boolReal (f x)) S ^ 2) :
    graphVariance p f =
      ∑ S ∈ (Finset.univ : Finset (Finset (GraphEdge n))).erase ∅,
        coeff p (fun x => boolReal (f x)) S ^ 2 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ ∅), ← hparseval,
    graph_second_moment_eq_mean, fourier_coeff_empty_eq_graphMean,
    graphVariance_eq_mean_mul]
  ring

theorem graphVariance_eq_fourier_nonempty {n : ℕ} {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : GraphConfig n → Bool) :
    graphVariance p f =
      ∑ S ∈ (Finset.univ : Finset (Finset (GraphEdge n))).erase ∅,
        coeff p (fun x => boolReal (f x)) S ^ 2 := by
  exact graphVariance_eq_fourier_nonempty_of_parseval p f
    (parseval hp hp1 (fun x : GraphConfig n => boolReal (f x))).symm

theorem graphVariance_eq_fourier_nonempty_filter {n : ℕ} {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : GraphConfig n → Bool) :
    graphVariance p f =
      ∑ S ∈ (Finset.univ : Finset (Finset (GraphEdge n))).filter (fun S => S ≠ ∅),
        coeff p (fun x => boolReal (f x)) S ^ 2 := by
  rw [Finset.filter_ne']
  exact graphVariance_eq_fourier_nonempty hp hp1 f

/-- The variance identity as a sum over nonempty Fourier supports. -/
theorem graphVariance_eq_fourier_sum_nonempty {n : ℕ} {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : GraphConfig n → Bool) :
    graphVariance p f =
      ∑ S : Finset (GraphEdge n) with S.Nonempty,
        coeff p (fun x => boolReal (f x)) S ^ 2 := by
  simpa only [Finset.nonempty_iff_ne_empty] using
    graphVariance_eq_fourier_nonempty_filter hp hp1 f

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.RestrictionMassSubtype ----
namespace OAI

universe u

noncomputable section

open scoped BigOperators

namespace Problem313

variable {ι : Type u} [Fintype ι] (P : ι → Prop) [DecidablePred P]

namespace BiasedFourier

/-- Exact restricted Fourier mass at any selection of free-coordinate degrees. -/
theorem restriction_mass_subtype_filter [DecidableEq ι] {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : (ι → Bool) → ℝ)
    (Q : ℕ → Prop) [DecidablePred Q] :
    (∑ y : {i // ¬P i} → Bool, weight p y *
      ∑ A ∈ Finset.univ.filter (fun A : Finset {i // P i} => Q A.card),
        coeff p (restrictCube P f y) A ^ 2) =
      ∑ S ∈ Finset.univ.filter (fun S : Finset ι => Q (S.filter P).card),
        coeff p f S ^ 2 := by
  classical
  simpa only [Finset.sum_filter, Finset.card_subtype, ite_mul, one_mul, zero_mul] using
    restriction_mass_subtype P hp hp1 f (fun A => if Q A.card then 1 else 0)

/-- The low-degree restriction identity in conditional-sum format. -/
theorem restriction_low_degree_mass_subtype [DecidableEq ι] {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (f : (ι → Bool) → ℝ) (k : ℝ) :
    (∑ S : Finset ι, if (S.filter P).Nonempty ∧ ((S.filter P).card : ℝ) ≤ k
      then coeff p f S ^ 2 else 0) =
      ∑ y : {i // ¬P i} → Bool, weight p y *
        ∑ A : Finset {i // P i}, if A.Nonempty ∧ (A.card : ℝ) ≤ k
          then coeff p (restrictCube P f y) A ^ 2 else 0 := by
  classical
  simpa only [Finset.sum_filter, Finset.card_pos] using
    (restriction_mass_subtype_filter P hp hp1 f (fun d => 0 < d ∧ (d : ℝ) ≤ k)).symm

end BiasedFourier
end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.LowDegree ----
namespace OAI

universe u

noncomputable section

namespace Problem313.BiasedFourier

open scoped BigOperators Classical

variable {ι : Type u} [Fintype ι]

/-- The biased Boolean low-degree estimate.  No monotonicity or symmetry
is required beyond the displayed bound on each coordinate influence. -/
theorem low_degree_estimate {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (m : ℝ) (hm : 1 ≤ m)
    (horbit : ∀ i, Reindex.influence p f i ≤ (∑ j, Reindex.influence p f j) / m) :
    (∑ S : Finset ι,
      if S.Nonempty ∧ (S.card : ℝ) ≤ Real.sqrt (p * (1 - p)) * Real.log m / 64
      then coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
        m ^ (-1 / 4 : ℝ) * ∑ i, Reindex.influence p f i := by
  exact low_degree_estimate_of_noise hp hp1 f m hm horbit
    (synthesis_fourth_bound hp hp1)

end Problem313.BiasedFourier

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.BlockLowDegree ----
namespace OAI

universe u

noncomputable section
open scoped BigOperators

namespace Problem313

/-- Fixed-block Fourier estimate: all exterior Fourier degrees are retained.
The only analytic input is the ordinary low-degree estimate on the free cube. -/
theorem block_low_degree_bound_of_estimate
    {n : ℕ} (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)]
    (hB : 3 ≤ B.card) (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    (p k C : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hestimate : ∀ g : ({e : GraphEdge n // EdgeTouches B e} → Bool) → Bool,
      (∀ e, Reindex.influence p g e ≤
        (∑ d, Reindex.influence p g d) / (B.card : ℝ)) →
      (∑ A : Finset {e : GraphEdge n // EdgeTouches B e},
        if A.Nonempty ∧ (A.card : ℝ) ≤ k then
          BiasedFourier.coeff p (fun x => boolReal (g x)) A ^ 2 else 0) ≤
      C * ∑ e, Reindex.influence p g e) :
    (∑ S : Finset (GraphEdge n),
      if (S.filter (EdgeTouches B)).Nonempty ∧
          ((S.filter (EdgeTouches B)).card : ℝ) ≤ k then
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      C * ∑ e : {e : GraphEdge n // EdgeTouches B e}, edgeInfluence p f e.val := by
  rw [BiasedFourier.restriction_low_degree_mass_subtype (EdgeTouches B) hp hp1]
  exact block_conditional_low_degree_bound_of_estimate B hB f hf p k C
    hp.le hp1.le hestimate

/-- The fixed-block low-degree Fourier bound for invariant graph properties.
All symmetry, restriction and analytic premises are discharged. -/
theorem block_low_degree_bound
    {n : ℕ} (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)]
    (hB : 3 ≤ B.card) (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (∑ S : Finset (GraphEdge n),
      if (S.filter (EdgeTouches B)).Nonempty ∧
          ((S.filter (EdgeTouches B)).card : ℝ) ≤
            Real.sqrt (p * (1 - p)) * Real.log (B.card : ℝ) / 64 then
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      (B.card : ℝ) ^ (-1 / 4 : ℝ) *
        ∑ e : {e : GraphEdge n // EdgeTouches B e}, edgeInfluence p f e.val := by
  have hm : (1 : ℝ) ≤ B.card := by exact_mod_cast (by omega : 1 ≤ B.card)
  exact block_low_degree_bound_of_estimate B hB f hf p
    (Real.sqrt (p * (1 - p)) * Real.log (B.card : ℝ) / 64)
    ((B.card : ℝ) ^ (-1 / 4 : ℝ)) hp hp1
    (fun g hg => BiasedFourier.low_degree_estimate hp hp1 g (B.card : ℝ) hm hg)

/-- Filtered finite-sum version of the fixed-block low-degree bound. -/
theorem block_low_degree_bound_filter
    {n : ℕ} (B : Finset (Fin n)) [DecidablePred (EdgeTouches B)]
    (hB : 3 ≤ B.card) (f : GraphConfig n → Bool) (hf : VertexInvariant f)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (∑ S ∈ Finset.univ.filter (fun S : Finset (GraphEdge n) =>
      1 ≤ (S.filter (EdgeTouches B)).card ∧
        ((S.filter (EdgeTouches B)).card : ℝ) ≤
          Real.sqrt (p * (1 - p)) * Real.log (B.card : ℝ) / 64),
      BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2) ≤
      (B.card : ℝ) ^ (-1 / 4 : ℝ) *
        ∑ e ∈ Finset.univ.filter (EdgeTouches B), edgeInfluence p f e := by
  have h := block_low_degree_bound B hB f hf hp hp1
  have hs : (∑ e : {e : GraphEdge n // EdgeTouches B e}, edgeInfluence p f e.val) =
      ∑ e ∈ Finset.univ.filter (EdgeTouches B), edgeInfluence p f e :=
    (Finset.sum_subtype (Finset.univ.filter (EdgeTouches B))
      (by intro e; simp) (edgeInfluence p f)).symm
  rw [hs] at h
  simpa only [Finset.sum_filter, Finset.one_le_card] using h

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.GraphBlockAverage ----
namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace Problem313

/-- The complete captured Fourier-mass bound for a vertex-invariant graph
property. The bias is unrestricted within `(0,1)` and no monotonicity is used. -/
theorem graph_fourier_captured_mass
    {n : ℕ} (f : GraphConfig n → Bool) {p : ℝ}
    (hn : 2 ≤ n) (ht : 16 ≤ Real.log (n : ℝ)) (hf : VertexInvariant f)
    (hp : 0 < p) (hp1 : p < 1) :
    (∑ S : Finset (GraphEdge n),
      if S.Nonempty ∧ (S.card : ℝ) ≤
          (Real.sqrt (p * (1 - p)) * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2
      then BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      4 * (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ) * totalInfluence p f := by
  apply graph_fourier_captured_mass_of_block_bound f hn ht hp hp1
  intro B hB
  have hBm : 3 ≤ B.card := by
    rw [hB]
    exact (sqrt_block_size_bounds n hn ht).1
  simpa only [hB, Finset.sum_filter] using
    block_low_degree_bound_filter B hBm f hf hp hp1

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.GraphVarianceBound ----
namespace OAI

noncomputable section

namespace Problem313

/-- Parseval discharges the variance identity, leaving the Dirichlet and captured-mass inputs. -/
theorem graphVariance_bound_of_dirichlet_capture {n : ℕ}
    (f : GraphConfig n → Bool) (p : ℝ) (hn : 2 ≤ n) (hp : 0 < p) (hp1 : p < 1)
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
  exact graphVariance_bound_of_spectral_inputs f p hn hp hp1
    (graphVariance_eq_fourier_sum_nonempty hp hp1 f) hdirichlet hcapture

/-- All spectral and numerical ingredients are discharged; only the graph-specific
large-scale captured-mass estimate remains. -/
theorem graphVariance_bound_of_capture {n : ℕ}
    (f : GraphConfig n → Bool) (p : ℝ) (hn : 2 ≤ n) (hp : 0 < p) (hp1 : p < 1)
    (hcapture : 16 ≤ Real.log (n : ℝ) →
      (∑ S : Finset (GraphEdge n) with S.Nonempty ∧
          (S.card : ℝ) ≤ (Real.sqrt (p * (1 - p)) *
            Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2,
        BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2) ≤
      (4 * (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ)) * totalInfluence p f) :
    graphVariance p f ≤
      ((2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2) * totalInfluence p f := by
  exact graphVariance_bound_of_dirichlet_capture f p hn hp hp1
    (graph_fourier_dirichlet hp hp1 f) hcapture

/-- The graph variance bound, with all spectral, analytic, counting, and
numerical inputs discharged. -/
theorem variance_influence_bound_core
    (n : ℕ) (f : GraphConfig n → Bool) (p : ℝ)
    (hn : 2 ≤ n) (hf : VertexInvariant f) (hp : 0 < p) (hp1 : p < 1) :
    graphVariance p f ≤
      ((2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2) * totalInfluence p f := by
  classical
  apply graphVariance_bound_of_capture f p hn hp hp1
  intro ht
  simpa only [Finset.sum_filter] using
    graph_fourier_captured_mass f hn ht hf hp hp1

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.SharpThreshold ----
namespace OAI

noncomputable section
namespace Problem313

/-- The logarithmic-square threshold-width bound follows from the variance bound. -/
theorem sharp_threshold_width_of_variance_bound
    (hvariance : ∀ (n : ℕ) (f : GraphConfig n → Bool) (p : ℝ),
      2 ≤ n → VertexInvariant f → 0 < p → p < 1 →
      graphVariance p f ≤ ((2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2) *
        totalInfluence p f) :
    ∀ (n : ℕ) (f : GraphConfig n → Bool) (ε : ℝ),
      2 ≤ n → VertexInvariant f → IncreasingGraphProperty f →
      NontrivialGraphProperty f → 0 < ε → ε < (1 / 2 : ℝ) →
      graphQuantile (1 - ε) f - graphQuantile ε f ≤
        ((2 : ℝ) ^ 19 / (Real.log (n : ℝ)) ^ 2) *
          Real.log (1 / (2 * ε)) := by
  intro n f ε hn hinvariant hmono hnt hε hεhalf
  have h := graphQuantile_width_of_variance_bound
    (C := (2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2)
    (by positivity) hmono hnt hε hεhalf
    (fun p hp => hvariance n f p hn hinvariant hp.1 hp.2)
  convert h using 1; ring

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.Main ----
namespace OAI

noncomputable section

namespace Problem313

theorem variance_influence_bound :
    ∀ (n : ℕ) (f : GraphConfig n → Bool) (p : ℝ), 2 ≤ n → VertexInvariant f → 0 < p → p < 1 → graphVariance p f ≤ ((2 : ℝ) ^ 17 / (Real.log (n : ℝ)) ^ 2) * totalInfluence p f := by
  exact variance_influence_bound_core

theorem sharp_threshold_width :
    ∀ (n : ℕ) (f : GraphConfig n → Bool) (ε : ℝ), 2 ≤ n → VertexInvariant f → IncreasingGraphProperty f → NontrivialGraphProperty f → 0 < ε → ε < (1 / 2 : ℝ) → graphQuantile (1 - ε) f - graphQuantile ε f ≤ ((2 : ℝ) ^ 19 / (Real.log (n : ℝ)) ^ 2) * Real.log (1 / (2 * ε)) := by
  exact sharp_threshold_width_of_variance_bound variance_influence_bound

end Problem313

end

end OAI

-- ---- mission target ----
open OAI OAI.Problem313

namespace OAI
namespace Problem313
theorem _root_.solution :
    ∀ (n : ℕ) (f : GraphConfig n → Bool) (ε : ℝ),
      2 ≤ n → VertexInvariant f → IncreasingGraphProperty f →
      NontrivialGraphProperty f → 0 < ε → ε < (1 / 2 : ℝ) →
      graphQuantile (1 - ε) f - graphQuantile ε f ≤
        ((2 : ℝ) ^ 19 / (Real.log (n : ℝ)) ^ 2) * Real.log (1 / (2 * ε)) := by
  first
    | exact OAI.Problem313.sharp_threshold_width
    | (apply OAI.Problem313.sharp_threshold_width <;> assumption)
    | (intros; apply OAI.Problem313.sharp_threshold_width <;> assumption)
end Problem313
end OAI
