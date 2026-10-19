-- Prove2me | solution 1 for OAI.Problem313.graph_fourier_captured_mass_of_block_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:41:00.644979+00:00
-- url     : https://prove2.me/submissions/348d05d8-4ede-441b-954b-9fdb728b44d6

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/GraphBlockAverage.lean:L92-L128
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.graph_fourier_captured_mass_of_block_bound. The node keeps its source
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
import Theorems.Thm_OAI_Problem313_graph_fourier_capture_of_block_bounds
import Theorems.Thm_OAI_Problem313_sqrt_block_detection_probability
import Theorems.Thm_OAI_Problem313_sqrt_block_size_bounds

-- ---- from OAI.Combinatorics.SharpThreshold.BlockCounting ----
namespace OAI

universe u

noncomputable section

namespace Problem313

open Finset

variable {α : Type u} [DecidableEq α]

omit [DecidableEq α] in
theorem blockProbability_mono (U : Finset α) (m : ℕ)
    {P Q : Finset α → Prop}
    (hPQ : ∀ B ∈ U.powersetCard m, P B → Q B) :
    blockProbability U m P ≤ blockProbability U m Q := by
  classical
  unfold blockProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show (U.powersetCard m).filter P ⊆
      (U.powersetCard m).filter Q from by
    intro B hB
    obtain ⟨hB, hP⟩ := Finset.mem_filter.mp hB
    exact Finset.mem_filter.mpr ⟨hB, hPQ B hB hP⟩)

omit [DecidableEq α] in
theorem blockProbability_congr (U : Finset α) (m : ℕ)
    {P Q : Finset α → Prop}
    (hPQ : ∀ B ∈ U.powersetCard m, P B ↔ Q B) :
    blockProbability U m P = blockProbability U m Q := by
  apply le_antisymm
  · exact blockProbability_mono U m (fun B hB => (hPQ B hB).mp)
  · exact blockProbability_mono U m (fun B hB => (hPQ B hB).mpr)

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.BlockRestrictionSymmetry ----
namespace OAI

noncomputable section
namespace Problem313

lemma edgeTouches_iff_not_disjoint {n : ℕ} (B : Finset (Fin n))
    (e : GraphEdge n) : EdgeTouches B e ↔ ¬ Disjoint e.val B := by
  classical
  simp [EdgeTouches, Finset.disjoint_left]

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.GraphBlockAverage ----
namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace Problem313

/-- At the square-root block size all counting and numerical capture premises
are discharged. Only the fixed-block analytic estimate remains as input. -/
theorem graph_fourier_captured_mass_of_block_bound
    {n : ℕ} (f : GraphConfig n → Bool) {p : ℝ}
    (hn : 2 ≤ n) (ht : 16 ≤ Real.log (n : ℝ))
    (hp : 0 < p) (hp1 : p < 1)
    (hblock : ∀ B : Finset (Fin n), B.card = ⌊Real.sqrt (n : ℝ)⌋₊ →
      (∑ S : Finset (GraphEdge n),
        if 1 ≤ (S.filter (EdgeTouches B)).card ∧
            ((S.filter (EdgeTouches B)).card : ℝ) ≤
              Real.sqrt (p * (1 - p)) * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64
        then BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ) *
        ∑ e : GraphEdge n, if EdgeTouches B e then edgeInfluence p f e else 0) :
    (∑ S : Finset (GraphEdge n),
      if S.Nonempty ∧ (S.card : ℝ) ≤
          (Real.sqrt (p * (1 - p)) * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64) ^ 2 / 2
      then BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      4 * (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ) * totalInfluence p f := by
  have hm := sqrt_block_size_bounds n hn ht
  apply graph_fourier_capture_of_block_bounds f hp.le hp1.le
    (show 1 ≤ ⌊Real.sqrt (n : ℝ)⌋₊ by omega) hm.2.1
    (Real.sqrt (p * (1 - p)) * Real.log (⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) / 64)
    ((⌊Real.sqrt (n : ℝ)⌋₊ : ℝ) ^ (-1 / 4 : ℝ)) (by positivity)
  · intro S hS hcard
    have hsigma1 : Real.sqrt (p * (1 - p)) ≤ (1 / 2 : ℝ) := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · norm_num
      · nlinarith [sq_nonneg (p - 1 / 2)]
    have hdet := sqrt_block_detection_probability n (Real.sqrt (p * (1 - p)))
      hn ht (Real.sqrt_nonneg _) hsigma1 S hS hcard
    refine hdet.trans_eq ?_
    apply blockProbability_congr
    intro B hB
    simp only [BlockDetects, edgeTouches_iff_not_disjoint]
  · exact hblock

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313
open scoped BigOperators Classical


theorem solution : type_of% @_root_.OAI.Problem313.graph_fourier_captured_mass_of_block_bound := @_root_.OAI.Problem313.graph_fourier_captured_mass_of_block_bound
