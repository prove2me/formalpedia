-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.weights_small
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:49:23.338745+00:00
-- url     : https://prove2.me/submissions/31e0d282-c35f-45c6-8e71-8191c20bb48c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/WeightedCover.lean:L21-L90
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.weights_small. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_TalagrandDiscreteConvexity
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Model
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Basic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_DyadicBins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteFibers
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringBasic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringSampledFamilies
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteProbability
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bernoulli
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringResidualTuples
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringNumericalBounds
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_Covering_elementary_covering
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_binExponent_spec
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_finite_bin_geometric_bound
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_largeWeightFamily_cost_le
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_subset_power_sum_le_bins
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_weightBin_cost_bound

-- ---- from OAI.Combinatorics.DiscreteConvexity.Basic ----
namespace OAI

namespace TalagrandDiscreteConvexity

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable section

omit [Fintype α] [DecidableEq α] in
theorem cost_nonneg {p : ℝ} (hp : 0 ≤ p) (G : Family α) : 0 ≤ cost p G :=
  Finset.sum_nonneg (fun generator _ => pow_nonneg hp generator.card)

omit [Fintype α] in
theorem cost_union_le {p : ℝ} (hp : 0 ≤ p) (G H : Family α) :
    cost p (G ∪ H) ≤ cost p G + cost p H := by
  calc
    cost p (G ∪ H) ≤ cost p (G ∪ H) + cost p (G ∩ H) :=
      le_add_of_nonneg_right (cost_nonneg hp _)
    _ = cost p G + cost p H := by
      exact Finset.sum_union_inter

omit [Fintype α] in
theorem cost_biUnion_le {ι : Type*} [DecidableEq ι] {p : ℝ} (hp : 0 ≤ p)
    (T : Finset ι) (G : ι → Family α) :
    cost p (T.biUnion G) ≤ ∑ i ∈ T, cost p (G i) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      exact (cost_union_le hp _ _).trans (add_le_add le_rfl ih)

end
end TalagrandDiscreteConvexity

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.DyadicBins ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Dyadic bins for positive weights

The exponent of a weight is determined by the first power of `1 / 2`
strictly below it.  In particular, a weight equal to a dyadic endpoint
belongs to the bin whose upper endpoint it equals.
-/

namespace TalagrandDiscreteConvexity

theorem binExponent_lower {w : ℝ} (hwpos : 0 < w) (hwle : w ≤ 1) :
    (1 / 2 : ℝ) ^ (binExponent w + 1) < w :=
  (binExponent_spec hwpos hwle).1

/-- A dyadic upper bound on a weight gives a lower bound on its bin index. -/
theorem le_binExponent_of_le_pow {w : ℝ} {n : ℕ} (hwpos : 0 < w)
    (hwn : w ≤ (1 / 2 : ℝ) ^ n) : n ≤ binExponent w := by
  have hwle : w ≤ 1 :=
    hwn.trans (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  have hpow : (1 / 2 : ℝ) ^ (binExponent w + 1) < (1 / 2 : ℝ) ^ n :=
    (binExponent_lower hwpos hwle).trans_le hwn
  have hn : n < binExponent w + 1 :=
    (pow_lt_pow_iff_right_of_lt_one₀
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)).mp hpow
  exact Nat.lt_succ_iff.mp hn

theorem le_binExponent_of_lt_pow {w : ℝ} {n : ℕ} (hwpos : 0 < w)
    (hwn : w < (1 / 2 : ℝ) ^ n) : n ≤ binExponent w :=
  le_binExponent_of_le_pow hwpos hwn.le

end TalagrandDiscreteConvexity

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.BinNumerics ----
namespace OAI

namespace TalagrandDiscreteConvexity

open scoped BigOperators

/-- The total bin-cover cost is strictly below one quarter. -/
theorem finite_bin_cost_lt_quarter (B : Finset (ℕ × ℕ))
    (hB : ∀ b ∈ B, 1 ≤ b.1 ∧ 64 * b.1 ≤ b.2) :
    (∑ b ∈ B, 3 * (1 / 2 : ℝ) ^ b.2) < 1 / 4 := by
  rw [← Finset.mul_sum]
  have h := finite_bin_geometric_bound B hB (a := (1 / 2 : ℝ))
    (by norm_num) (by norm_num)
  have hn : (3 : ℝ) * (4 * (1 / 2 : ℝ) ^ 64) < 1 / 4 := by norm_num
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h (by norm_num)) hn

/-- The total contribution of uncovered bins is below the exceptional threshold. -/
theorem finite_bin_power_lt_threshold (B : Finset (ℕ × ℕ))
    (hB : ∀ b ∈ B, 1 ≤ b.1 ∧ 64 * b.1 ≤ b.2) :
    (∑ b ∈ B, (1 / 2 : ℝ) ^ (4 * b.2)) < (1 / 2 : ℝ) ^ 32 := by
  have h := finite_bin_geometric_bound B hB (a := (1 / 2 : ℝ) ^ 4)
    (by norm_num) (by norm_num)
  have heq : (∑ b ∈ B, (1 / 2 : ℝ) ^ (4 * b.2)) =
      ∑ b ∈ B, ((1 / 2 : ℝ) ^ 4) ^ b.2 := by
    simp only [pow_mul]
  rw [heq]
  exact lt_of_le_of_lt h (by norm_num)

/-- Fewer than `2^(12h)` weights at most `2⁻ʰ` have small sixteenth-power sum. -/
theorem bin_power_bound {m h : ℕ} (hm : m ≤ 2 ^ (12 * h)) :
    (m : ℝ) * ((1 / 2 : ℝ) ^ h) ^ 16 ≤ (1 / 2 : ℝ) ^ (4 * h) := by
  have hm' : (m : ℝ) ≤ (2 : ℝ) ^ (12 * h) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr hm
  calc
    (m : ℝ) * ((1 / 2 : ℝ) ^ h) ^ 16 ≤
        (2 : ℝ) ^ (12 * h) * ((1 / 2 : ℝ) ^ h) ^ 16 :=
      mul_le_mul_of_nonneg_right hm' (by positivity)
    _ = (1 / 2 : ℝ) ^ (4 * h) := by
      rw [← pow_mul, show h * 16 = 12 * h + 4 * h by omega,
        pow_add, ← mul_assoc, ← mul_pow]
      norm_num

end TalagrandDiscreteConvexity

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.Bins ----
namespace OAI

open scoped BigOperators

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem mem_weightBin {W : Finset α → ℝ} {U : Finset α} {b : ℕ × ℕ} :
    U ∈ weightBin W b ↔ U ∈ smallWeightFamily W ∧ weightBinKey W U = b := by
  classical
  simp [weightBin, FiniteFibers.fiber]

theorem weightBin_card {W : Finset α → ℝ} {U : Finset α} {b : ℕ × ℕ}
    (hU : U ∈ weightBin W b) : U.card = b.1 := by
  exact congrArg Prod.fst (mem_weightBin.mp hU).2

theorem weightBin_bounds {W : Finset α → ℝ} {U : Finset α} {b : ℕ × ℕ}
    (hU : U ∈ weightBin W b) :
    (1 / 2 : ℝ) ^ (b.2 + 1) < W U ∧ W U ≤ (1 / 2 : ℝ) ^ b.2 := by
  have hmem := mem_weightBin.mp hU
  have hw := mem_smallWeightFamily.mp hmem.1
  have hle : W U ≤ 1 := hw.2.2.le.trans (pow_le_one₀ (by norm_num) (by norm_num))
  have hbin := binExponent_spec hw.2.1 hle
  have he : binExponent (W U) = b.2 := congrArg Prod.snd hmem.2
  simpa only [he] using hbin

theorem occupiedWeightBins_bounds {W : Finset α → ℝ} {b : ℕ × ℕ}
    (hb : b ∈ occupiedWeightBins W) : 1 ≤ b.1 ∧ 64 * b.1 ≤ b.2 := by
  classical
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hb
  have hw := mem_smallWeightFamily.mp hU
  exact ⟨Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hw.1),
    le_binExponent_of_lt_pow hw.2.1 hw.2.2⟩

/-- In an uncovered bin, the sixteenth powers have the required geometric bound. -/
theorem weightBin_power_sum_le {W : Finset α → ℝ} (hW : ∀ U, 0 ≤ W U)
    (S : Finset α) (b : ℕ × ℕ)
    (hcount : ((weightBin W b).filter (fun U => U ⊆ S)).card ≤ 2 ^ (12 * b.2)) :
    (∑ U ∈ (weightBin W b).filter (fun U => U ⊆ S), (W U) ^ 16) ≤
      (1 / 2 : ℝ) ^ (4 * b.2) := by
  calc
    _ ≤ ∑ U ∈ (weightBin W b).filter (fun U => U ⊆ S),
        ((1 / 2 : ℝ) ^ b.2) ^ 16 := by
      apply Finset.sum_le_sum
      intro U hU
      exact pow_le_pow_left₀ (hW U) (weightBin_bounds (Finset.mem_filter.mp hU).1).2 _
    _ = (((weightBin W b).filter (fun U => U ⊆ S)).card : ℝ) *
        ((1 / 2 : ℝ) ^ b.2) ^ 16 := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (1 / 2 : ℝ) ^ (4 * b.2) := bin_power_bound hcount

end TalagrandDiscreteConvexity

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.WeightedCover ----
namespace OAI

/-!
# From actual dyadic weights to a containment cover

The only inputs are the two weight inequalities.  All bins, their finite
index set, their covers, and the final union are constructed in the proof.
-/

open scoped BigOperators

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem weights_small {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (A : Family α) (W : Finset α → ℝ) (hW : ∀ U, 0 ≤ W U)
    (hglobal : (∑ U : Finset α, q ^ U.card * W U) ≤ 1)
    (hlower : ∀ S ∈ A,
      (1 / 2 : ℝ) ^ 32 ≤ ∑ U ∈ S.powerset.erase ∅, (W U) ^ 16) :
    Small (q / (2 : ℝ) ^ 70) A := by
  classical
  let ρ : ℝ := q / (2 : ℝ) ^ 70
  let B := occupiedWeightBins W
  have hρ0 : 0 < ρ := div_pos hq0 (pow_pos (by norm_num) _)
  have hρq : ρ ≤ q := div_le_self hq0.le (one_le_pow₀ (by norm_num))
  have hρ1 : ρ < 1 := hρq.trans_lt hq1
  have hB : ∀ b ∈ B, 1 ≤ b.1 ∧ 64 * b.1 ≤ b.2 :=
    fun _ hb => occupiedWeightBins_bounds hb
  have each : ∀ b : ℕ × ℕ, ∃ G : Family α, b ∈ B →
      Covers G (Covering.denseFamily (weightBin W b) (2 ^ (12 * b.2))) ∧
      cost ρ G ≤ 3 * (1 / 2 : ℝ) ^ b.2 := by
    intro b
    by_cases hb : b ∈ B
    · have hbnd := hB b hb
      obtain ⟨G, hcover, hcost⟩ := Covering.elementary_covering
        (weightBin W b) ρ b.1 b.2 hρ0 hρ1
        (fun U hU => weightBin_card hU) hbnd.1
        (by omega) (by omega) (weightBin_cost_bound hq0 hW hglobal b)
      refine ⟨G, fun _ => ⟨hcover, ?_⟩⟩
      simpa only [one_div, inv_pow] using hcost
    · exact ⟨∅, fun h => False.elim (hb h)⟩
  let G : (ℕ × ℕ) → Family α := fun b => Classical.choose (each b)
  have hG : ∀ b ∈ B,
      Covers (G b) (Covering.denseFamily (weightBin W b) (2 ^ (12 * b.2))) ∧
      cost ρ (G b) ≤ 3 * (1 / 2 : ℝ) ^ b.2 :=
    fun b hb => Classical.choose_spec (each b) hb
  let C : Family α := largeWeightFamily W ∪ B.biUnion G
  have hcost : cost ρ C ≤ 1 / 2 := by
    have hsum : (∑ b ∈ B, cost ρ (G b)) < 1 / 4 :=
      (Finset.sum_le_sum (fun b hb => (hG b hb).2)).trans_lt
        (finite_bin_cost_lt_quarter B hB)
    have hlarge : cost ρ (largeWeightFamily W) ≤ 1 / 64 :=
      largeWeightFamily_cost_le hq0.le hW hglobal
    have htotal := (cost_union_le hρ0.le (largeWeightFamily W) (B.biUnion G)).trans
      (add_le_add le_rfl (cost_biUnion_le hρ0.le B G))
    change cost ρ (largeWeightFamily W ∪ B.biUnion G) ≤ 1 / 2
    linarith
  refine ⟨C, ?_, hcost⟩
  intro S hS
  by_contra hcovered
  have hnone : ∀ I ∈ C, ¬ I ⊆ S := by
    intro I hI hIS
    exact hcovered ⟨I, hI, hIS⟩
  have hlarge : ∀ U ∈ largeWeightFamily W, ¬ U ⊆ S := by
    intro U hU
    exact hnone U (Finset.mem_union_left _ hU)
  have hcount : ∀ b ∈ B,
      ((weightBin W b).filter (fun U => U ⊆ S)).card ≤ 2 ^ (12 * b.2) := by
    intro b hb
    have hnot : ¬ S ∈ Covering.denseFamily (weightBin W b) (2 ^ (12 * b.2)) := by
      intro hdense
      obtain ⟨I, hI, hIS⟩ := (hG b hb).1 S hdense
      exact hnone I (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, hb, hI⟩)) hIS
    have hlt : ((weightBin W b).filter (fun U => U ⊆ S)).card < 2 ^ (12 * b.2) :=
      lt_of_not_ge (fun h => hnot (Covering.mem_denseFamily.mpr h))
    exact hlt.le
  have hupper : (∑ U ∈ S.powerset.erase ∅, (W U) ^ 16) < (1 / 2 : ℝ) ^ 32 := by
    calc
      _ ≤ ∑ b ∈ B, ∑ U ∈ (weightBin W b).filter (fun U => U ⊆ S), (W U) ^ 16 :=
        subset_power_sum_le_bins hW S hlarge
      _ ≤ ∑ b ∈ B, (1 / 2 : ℝ) ^ (4 * b.2) :=
        Finset.sum_le_sum (fun b hb => weightBin_power_sum_le hW S b (hcount b hb))
      _ < (1 / 2 : ℝ) ^ 32 := finite_bin_power_lt_threshold B hB
  exact (not_lt_of_ge (hlower S hS)) hupper

end TalagrandDiscreteConvexity

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.weights_small := @_root_.OAI.TalagrandDiscreteConvexity.weights_small
