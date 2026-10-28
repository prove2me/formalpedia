-- Prove2me | solution 1 for OAI.SharpRamseyFive.AmbientEnumeration.ambient_untruncated_moment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:14:30.944992+00:00
-- url     : https://prove2.me/submissions/cb37ea3a-9835-425a-ae14-bff7e8a2f4e0

import Mathlib
import Definitions.Def_OAIQ060R002
import Definitions.Def_OAIQ060R003
import Theorems.Thm_OAI_SharpRamseyFive_AmbientEnumeration_ambient_refined_truncated_moment

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_LargeCard
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.AmbientEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open Classical
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.AmbientDesignations SharpRamseyFive.ComponentPartition
open SharpRamseyFive.ComponentEnumeration SharpRamseyFive.ResidualElimination
open SharpRamseyFive.SingletonEnumeration SharpRamseyFive.SelectionBridge
open SharpRamseyFive.WeightedPrograms
variable {D H : Type} [Fintype D] [DecidableEq D] [Fintype H] [DecidableEq H]

omit [DecidableEq D] in

lemma allTrunc_eq_one {R J : ℕ} (h : R < J) (ω : Fin R × D → ℕ) :
    HighMoment.allTrunc R J ω = 1 := by
  apply Finset.prod_eq_one
  intro d _
  unfold lineTrunc
  apply ite_eq_left
  exact (show (Finset.univ.filter (fun r => ω (r,d) ≠ 0)).card ≤ R by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.filter_subset (fun r : Fin R => ω (r,d) ≠ 0) Finset.univ)).trans_lt h

theorem ambient_untruncated_moment_oai (weight : D → ℝ≥0) (lines : H → Finset D)
    {p : ℕ} (hp : 0 < p) (R : ℕ) (own : H → Fin R → Bool)
    (L : ℝ≥0) (denom rootB mass C D₀ base B : ℝ)
    (hL : 10000 ≤ (L : ℝ)) (hbase : (23 / 25 : ℝ) ≤ base)
    (hlower : ∀ k, (3 / 4 : ℝ) ≤ PoissonScore.mass weight (lines k))
    (hdelta : ∀ k, |PoissonScore.mass weight (lines k) - base| ≤ (17 / 100 : ℝ))
    (hd : 0 < denom) (hb : 1 ≤ rootB) (hm : 0 ≤ mass) (hC : 0 ≤ C)
    (hD : 0 ≤ D₀) (hB : 0 ≤ B)
    (hmass : ∀ u, ∑ d ∈ lines u, ((L * weight d : ℝ≥0) : ℝ) ≤ mass)
    (K h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hKR : K ≤ R / 2) (hh : 0 < h)
    (hsize : h ≤ (R / 2) / (2 * K))
    (herr : (p : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun u => d ∈ lines u)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun u => d ∈ lines u ∧ e ∈ lines u)).card ≤ N₂)
    (hBC : denom * (1 + branchingBound (V := Fin p) (B := Fin R)
      (fun z : H × Fin p => lines z.1) (fun d => L * weight d) denom rootB mass K
      (N₁ * p) (N₂ * p) true) ≤ C)
    (hrow : ∀ y, (∑ x : H, shiftKernel weight lines p K x y) ≤ C)
    (hpair : (∑ x : H, ∑ y : H, shiftKernel weight lines p K x y) ≤ C ^ 2)
    (hDsum : (∑ x : H, |PoissonScore.mass weight (lines x) - base| ^ (R / 2)) ≤ D₀)
    (hcost : D₀ + 2 * ((p + 1 : ℝ) * C) ≤ B * Real.exp (((L : ℝ) * R) / 5))
    (hp2 : (p : ℝ) ^ 2 ≤ Real.exp (((L : ℝ) * R) / 10))
    (Δ : ℕ) (hΔ : ∀ k, Fintype.card {k' : H // overlapRelation weight lines (1 / (100 * p)) k k'} ≤ Δ)
    (hdeg : (Δ : ℝ) ≤ B * Real.exp (-((L : ℝ) * R)))
    (hRelPairs : (Fintype.card (RelatedPair (overlapRelation weight lines (1 / (100 * p)))) : ℝ) ≤
      B ^ 2 * Real.exp (((L : ℝ) * R) / 10)) :
    (∫ ω, (∑ k : H, scoreTerm (lines k) (Real.exp (-(L : ℝ) * base)) (own k)
        (fun r d => ω (r,d))) ^ p
      ∂batchMeasure (fun i : Fin R × D => L * weight i.2)) ≤
        B ^ p * Real.exp (-(1 / 10 : ℝ) * (p * ((L : ℝ) * R))) := by
  have hs := ambient_refined_truncated_moment weight lines hp R own L denom rootB mass C D₀ base B
    hL hbase hlower hdelta hd hb hm hC hD hB hmass K (R+1) h N₁ N₂ hK hKR hh true
    (by simpa using hsize) herr hN₁ hN₂ hBC hrow hpair
    (by simpa only [independentWeight, Nat.lt_succ_self, ite_true, add_zero] using hDsum)
    hcost hp2 Δ hΔ hdeg hRelPairs
  simpa only [allTrunc_eq_one (Nat.lt_succ_self R), one_mul] using hs

end SharpRamseyFive.AmbientEnumeration

end

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.AmbientEnumeration.ambient_untruncated_moment_oai := @OAI.SharpRamseyFive.AmbientEnumeration.ambient_untruncated_moment_oai
