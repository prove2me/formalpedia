-- Prove2me | solution 1 for OAI.ThorpCompatibility.clump_exp_moment_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:49:20.387979+00:00
-- url     : https://prove2.me/submissions/52d1f6b7-5215-4151-b35f-7ccb81a93110

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/ClumpMoments.lean:L74-L111
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.clump_exp_moment_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Model
import Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridExposure
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpCost
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability
import Definitions.Def_OAI_Probability_ThorpCompatibility_ListIncidence
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpMoments
import Theorems.Thm_OAI_ThorpCompatibility_meetsLists_probability_le

-- ---- from OAI.Probability.ThorpCompatibility.PermutationProbability ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset
lemma uniformProbability_def {α : Type*} [Fintype α] (P : α → Prop)
    [DecidablePred P] :
    uniformProbability P = ((Finset.univ.filter P).card : ℝ) / Fintype.card α := by
  unfold uniformProbability
  congr

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.UniformAverages ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset

lemma uniformMean_mono {α : Type*} [Fintype α] {f g : α → ℝ} (h : ∀ x, f x ≤ g x) :
    uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (by positivity)

lemma uniformMean_sum {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    uniformMean (fun x => ∑ y, f x y) = ∑ y, uniformMean (fun x => f x y) := by
  simp only [uniformMean]
  rw [Finset.sum_comm, Finset.sum_div]

lemma uniformMean_const_mul {α : Type*} [Fintype α] (a : ℝ) (f : α → ℝ) :
    uniformMean (fun x => a * f x) = a * uniformMean f := by
  simp only [uniformMean, ← Finset.mul_sum, mul_div_assoc]

lemma uniformMean_indicator {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] :
    uniformMean (fun x => if P x then 1 else 0) = uniformProbability P := by
  rw [uniformProbability_def]
  simp [uniformMean]

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.ClumpMoments ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
open Finset
lemma clumpWeight_nonneg {α : Type*} (H z : ℝ) (s : Finset α) :
    0 ≤ clumpWeight H z s := by
  unfold clumpWeight
  split_ifs <;> positivity

lemma cell_clump_exp_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (H z : ℝ) (hH : 0 ≤ H) (r : α → Equiv.Perm β) (b : β × β) :
    Real.exp (z * (if H < (cellRows r b).card then ((cellRows r b).card : ℝ) else 0)) ≤
      ∑ s : Finset α, clumpWeight H z s *
        (if ∀ i ∈ s, r i b.1 = b.2 then 1 else 0) := by
  let W : Finset α → ℝ := fun s => clumpWeight H z s *
    (if ∀ i ∈ s, r i b.1 = b.2 then 1 else 0)
  change Real.exp _ ≤ ∑ s, W s
  have hW (s : Finset α) : 0 ≤ W s :=
    mul_nonneg (clumpWeight_nonneg _ _ _) (by split_ifs <;> norm_num)
  by_cases h : H < (cellRows r b).card
  · have hs : cellRows r b ≠ ∅ := by
      intro he
      simp [he] at h
      linarith
    have hp : ∀ i ∈ cellRows r b, r i b.1 = b.2 := by
      intro i hi
      simpa only [cellRows, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    calc
      _ = W (cellRows r b) := by
        dsimp [W]
        rw [ite_eq_left h, ite_eq_left hp]
        simp [clumpWeight, hs, h]
      _ ≤ _ := Finset.single_le_sum (fun s _ => hW s) (Finset.mem_univ _)
  · calc
      _ = W ∅ := by
        dsimp [W]
        simp [clumpWeight, h]
      _ ≤ _ := Finset.single_le_sum (fun s _ => hW s) (Finset.mem_univ _)

lemma clump_expansion {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (H z : ℝ) (r : α → Equiv.Perm β) :
    (∏ b : β × β, ∑ s : Finset α, clumpWeight H z s *
      (if ∀ i ∈ s, r i b.1 = b.2 then 1 else 0)) =
    ∑ S : β × β → Finset α, (∏ b, clumpWeight H z (S b)) *
      (if MeetsLists S r then 1 else 0) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_mul_distrib, Finset.prod_boole]
  have hiff : (∀ b : β × β, ∀ i ∈ S b, r i b.1 = b.2) ↔ MeetsLists S r := by
    simp [MeetsLists, Prod.forall]
  simp only [Finset.mem_univ, forall_const]
  by_cases h : MeetsLists S r
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun hh => h (hiff.mp hh)), ite_eq_right h]

lemma clump_exp_moment_le {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (H z : ℝ) (hH : 0 ≤ H) (hn : 0 < Fintype.card β) :
    uniformMean (fun r : α → Equiv.Perm β => Real.exp (z * clumpCount H r)) ≤
      (∑ s : Finset α, clumpWeight H z s *
        (Real.exp 1 / Fintype.card β) ^ s.card) ^ (Fintype.card β ^ 2) := by
  let ρ : ℝ := Real.exp 1 / Fintype.card β
  calc
    _ ≤ uniformMean (fun r : α → Equiv.Perm β =>
        ∏ b : β × β, ∑ s : Finset α, clumpWeight H z s *
          (if ∀ i ∈ s, r i b.1 = b.2 then 1 else 0)) := by
      apply uniformMean_mono
      intro r
      unfold clumpCount
      rw [Nat.cast_sum, Finset.mul_sum, Real.exp_sum]
      apply Finset.prod_le_prod₀
      · intro b _
        exact (Real.exp_pos _).le
      · intro b _
        simpa only [Nat.cast_ite, Nat.cast_zero] using cell_clump_exp_le H z hH r b
    _ = ∑ S : β × β → Finset α, (∏ b, clumpWeight H z (S b)) *
        uniformProbability (MeetsLists S) := by
      simp_rw [clump_expansion]
      rw [uniformMean_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [uniformMean_const_mul, uniformMean_indicator]
    _ ≤ ∑ S : β × β → Finset α, (∏ b, clumpWeight H z (S b)) *
        ρ ^ (∑ b, (S b).card) := by
      apply Finset.sum_le_sum
      intro S _
      apply mul_le_mul_of_nonneg_left (meetsLists_probability_le hn S)
      exact Finset.prod_nonneg fun b _ => clumpWeight_nonneg _ _ _
    _ = ∏ b : β × β, ∑ s : Finset α, clumpWeight H z s * ρ ^ s.card := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro S _
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    _ = _ := by simp [ρ, Fintype.card_prod, pow_two]

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset
open Finset

theorem solution {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (H z : ℝ) (hH : 0 ≤ H) (hn : 0 < Fintype.card β) :
    uniformMean (fun r : α → Equiv.Perm β => Real.exp (z * clumpCount H r)) ≤
      (∑ s : Finset α, clumpWeight H z s *
        (Real.exp 1 / Fintype.card β) ^ s.card) ^ (Fintype.card β ^ 2) := by
  first
    | exact OAI.ThorpCompatibility.clump_exp_moment_le H z hH hn
    | exact OAI.ThorpCompatibility.clump_exp_moment_le
    | (apply OAI.ThorpCompatibility.clump_exp_moment_le <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.clump_exp_moment_le <;> assumption)
