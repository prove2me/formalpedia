-- Prove2me | solution 1 for OAI.Problem313.graph_fourier_capture_of_block_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:39:03.277133+00:00
-- url     : https://prove2.me/submissions/6709aad4-2c12-4267-84c4-3f7cb443f95c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/GraphBlockAverage.lean:L17-L90
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.graph_fourier_capture_of_block_bounds. The node keeps its source
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
import Theorems.Thm_OAI_Problem313_BlockAverage_captured_mass_le_four_uniform
import Theorems.Thm_OAI_Problem313_blockProbability_inter_nonempty_le

-- ---- from OAI.Combinatorics.SharpThreshold.BlockCounting ----
namespace OAI

universe u

noncomputable section

namespace Problem313

open Finset

variable {α : Type u} [DecidableEq α]

omit [DecidableEq α] in
theorem blockProbability_eq (U : Finset α) (m : ℕ) (P : Finset α → Prop)
    [DecidablePred P] : blockProbability U m P =
      (((U.powersetCard m).filter P).card : ℝ) / (U.powersetCard m).card := by
  unfold blockProbability
  congr

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

/-- The graph-edge touch bound used when averaging the block restriction. -/
theorem blockProbability_edge_touch_le (U E : Finset α) {m : ℕ}
    (hEU : E ⊆ U) (hE : E.card = 2) (hm : 1 ≤ m) (hmn : m ≤ U.card) :
    blockProbability U m (fun B => (B ∩ E).Nonempty) ≤ (2 : ℝ) * m / U.card := by
  simpa [hE] using blockProbability_inter_nonempty_le U E hEU hm hmn

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

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.GraphBlockAverage ----
namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace Problem313

/-- The fixed-block Fourier estimate and the pointwise support-capture estimate
combine into the global captured-mass bound. All graph sampling probabilities
are the canonical `blockProbability`; the edge-touch bound is discharged here.
The two hypotheses are precisely the analytic and combinatorial inputs, with
no requirement that a single block capture every support simultaneously. -/
theorem graph_fourier_capture_of_block_bounds
    {n m : ℕ} (f : GraphConfig n → Bool) {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (hm : 1 ≤ m) (hmn : m ≤ n)
    (k a : ℝ) (ha : 0 ≤ a)
    (hcapture : ∀ S : Finset (GraphEdge n), S.Nonempty →
      (S.card : ℝ) ≤ k ^ 2 / 2 →
      (m : ℝ) / (2 * n) ≤
        blockProbability (Finset.univ : Finset (Fin n)) m (fun B =>
          1 ≤ (S.filter (EdgeTouches B)).card ∧
            ((S.filter (EdgeTouches B)).card : ℝ) ≤ k))
    (hblock : ∀ B : Finset (Fin n), B.card = m →
      (∑ S : Finset (GraphEdge n),
        if 1 ≤ (S.filter (EdgeTouches B)).card ∧
            ((S.filter (EdgeTouches B)).card : ℝ) ≤ k
        then BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      a * ∑ e : GraphEdge n, if EdgeTouches B e then edgeInfluence p f e else 0) :
    (∑ S : Finset (GraphEdge n),
      if S.Nonempty ∧ (S.card : ℝ) ≤ k ^ 2 / 2
      then BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
      4 * a * totalInfluence p f := by
  classical
  let Ω := (Finset.univ : Finset (Fin n)).powersetCard m
  let low := (Finset.univ : Finset (Finset (GraphEdge n))).filter
    (fun S => S.Nonempty ∧ (S.card : ℝ) ≤ k ^ 2 / 2)
  let mass := fun S : Finset (GraphEdge n) =>
    BiasedFourier.coeff p (fun x => boolReal (f x)) S ^ 2
  let detect := fun (B : Finset (Fin n)) (S : Finset (GraphEdge n)) =>
    1 ≤ (S.filter (EdgeTouches B)).card ∧
      ((S.filter (EdgeTouches B)).card : ℝ) ≤ k
  have hn : 0 < n := lt_of_lt_of_le (Nat.zero_lt_of_lt hm) hmn
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hc : 0 < (m : ℝ) / (2 * n) := by positivity
  have hcap : ∀ S ∈ low,
      (m : ℝ) / (2 * n) ≤
        ((Ω.filter (fun B => detect B S)).card : ℝ) / Ω.card := by
    intro S hS
    obtain ⟨_, hSne, hScard⟩ := Finset.mem_filter.mp hS
    simpa only [blockProbability_eq] using hcapture S hSne hScard
  have hb : ∀ B ∈ Ω,
      (∑ S, if detect B S then mass S else 0) ≤
        a * ∑ e : GraphEdge n, if EdgeTouches B e then edgeInfluence p f e else 0 := by
    intro B hB
    exact hblock B (Finset.mem_powersetCard.mp hB).2
  have hi : ∀ e : GraphEdge n,
      ((Ω.filter (fun B => EdgeTouches B e)).card : ℝ) / Ω.card ≤
        4 * ((m : ℝ) / (2 * n)) := by
    intro e
    have htouch := blockProbability_edge_touch_le
      (Finset.univ : Finset (Fin n)) e.val (Finset.subset_univ _) e.property hm
      (by simpa using hmn)
    have hevent : blockProbability (Finset.univ : Finset (Fin n)) m
        (fun B => EdgeTouches B e) =
        blockProbability (Finset.univ : Finset (Fin n)) m
          (fun B => (B ∩ e.val).Nonempty) := by
      apply blockProbability_congr
      intro B hB
      simp only [EdgeTouches, Finset.Nonempty, Finset.mem_inter]
      exact exists_congr (fun _ => and_comm)
    change blockProbability (Finset.univ : Finset (Fin n)) m
      (fun B => EdgeTouches B e) ≤ _
    rw [hevent]
    calc
      _ ≤ (2 : ℝ) * m / (Finset.univ : Finset (Fin n)).card := htouch
      _ = 4 * ((m : ℝ) / (2 * n)) := by simp; ring
  have h := BlockAverage.captured_mass_le_four_uniform Ω mass
    (edgeInfluence p f) detect EdgeTouches low a ((m : ℝ) / (2 * n))
    (fun S => sq_nonneg _) (edgeInfluence_nonneg hp hp1 f) ha hc hcap hb hi
  simpa only [low, mass, Finset.sum_filter, totalInfluence] using h

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313
open scoped BigOperators Classical


theorem solution : type_of% @_root_.OAI.Problem313.graph_fourier_capture_of_block_bounds := @_root_.OAI.Problem313.graph_fourier_capture_of_block_bounds
