-- Prove2me | solution 1 for OAI.FixedClauseThreshold.auxiliary_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:43:35.208605+00:00
-- url     : https://prove2.me/submissions/d093b89f-6ce0-48b8-8216-3268791824e0

-- Generated from openai/math@1581d4c lean/OAI/Probability/RandomSAT/Interpolation.lean:L401-L424
-- (upload_full_project.md Phase 4): solution for node OAI.FixedClauseThreshold.auxiliary_interpolation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FixedClauseThreshold
import Definitions.Def_OAI_Probability_RandomSAT_Clauses
import Definitions.Def_OAI_Probability_RandomSAT_Replacement
import Definitions.Def_OAI_Probability_RandomSAT_FiniteMean
import Definitions.Def_OAI_Probability_RandomSAT_ClauseProcess
import Definitions.Def_OAI_Probability_RandomSAT_Binomial
import Definitions.Def_OAI_Probability_RandomSAT_Forcing
import Definitions.Def_OAI_Probability_RandomSAT_Variance
import Definitions.Def_OAI_Probability_RandomSAT_Concentration
import Definitions.Def_OAI_Probability_RandomSAT_CenterBounds
import Definitions.Def_OAI_Probability_RandomSAT_Interpolation
import Theorems.Thm_OAI_FixedClauseThreshold_embeddedAverage_alive
import Theorems.Thm_OAI_FixedClauseThreshold_finiteClauseAverage_commute

-- ---- from OAI.Probability.RandomSAT.FiniteMean ----
namespace OAI

/-!
Uniform finite expectations and variances.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem uniformMean_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]

theorem uniformMean_mul_const {α : Type*} [Fintype α] (f : α → ℝ) (c : ℝ) :
    uniformMean (fun a => f a * c) = uniformMean f * c := by
  simp only [uniformMean, ← Finset.sum_mul]
  ring

theorem uniformMean_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  simp only [uniformMean, ← Finset.mul_sum]
  ring

theorem uniformMean_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ a, f a ≤ g a) : uniformMean f ≤ uniformMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (Nat.cast_nonneg _)

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.ClauseProcess ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Coordinate erasure, independent clause averaging, survival probabilities, and
iterated replacement.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem alive_nonneg {n : ℕ} (S : Finset (Assignment n)) : 0 ≤ alive S := by
  unfold alive
  split <;> norm_num

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.Binomial ----
namespace OAI

/-!
Finite Bernoulli-count expectations and integrated telescoping estimates.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem binomialMean_congr {p : ℝ} {m : ℕ} {f g : ℕ → ℝ}
    (h : ∀ d ≤ m, f d = g d) : binomialMean p m f = binomialMean p m g := by
  induction m generalizing f g with
  | zero => exact h 0 (by omega)
  | succ m ih =>
    simp only [binomialMean]
    rw [ih (fun d hd => h d (by omega)), ih (fun d hd => h (d + 1) (by omega))]

theorem uniformMean_binomialMean {α : Type*} [Fintype α]
    (p : ℝ) (m : ℕ) (f : ℕ → α → ℝ) :
    uniformMean (fun a => binomialMean p m (fun d => f d a)) =
      binomialMean p m (fun d => uniformMean (f d)) := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih =>
    simp only [binomialMean, uniformMean_add, uniformMean_const_mul, ih]

end

end FixedClauseThreshold

end OAI

-- ---- from OAI.Probability.RandomSAT.Interpolation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Auxiliary ordered clauses allow repeated variables. Commuting finite averaging
operators give the fixed-count partition interpolation corresponding to the
marked-Poisson comparison.
-/

namespace FixedClauseThreshold

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

theorem finiteClauseAverage_mono {n : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) {f g : Finset (Assignment n) → ℝ}
    (hfg : ∀ S, f S ≤ g S) : ∀ S, finiteClauseAverage sat f S ≤ finiteClauseAverage sat g S := by
  intro S
  exact uniformMean_mono (fun c => hfg _)

theorem finiteClauseAverage_add {n : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) (f g : Finset (Assignment n) → ℝ) :
    finiteClauseAverage sat (fun S => f S + g S) =
      (fun S => finiteClauseAverage sat f S + finiteClauseAverage sat g S) := by
  funext S
  exact uniformMean_add _ _

theorem finiteClauseAverage_const_mul {n : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) (f : Finset (Assignment n) → ℝ) (c : ℝ) :
    finiteClauseAverage sat (fun S => c * f S) = (fun S => c * finiteClauseAverage sat f S) := by
  funext S
  exact uniformMean_const_mul _ _

theorem finiteClauseAverage_binomialMean {n : ℕ} {C : Type*} [Fintype C]
    (sat : C → Assignment n → Prop) (p : ℝ) (m : ℕ)
    (f : ℕ → Finset (Assignment n) → ℝ) :
    finiteClauseAverage sat (fun S => binomialMean p m (fun j => f j S)) =
      (fun S => binomialMean p m (fun j => finiteClauseAverage sat (f j) S)) := by
  funext S
  exact uniformMean_binomialMean _ _ _

theorem iterate_compare_of_commute {X : Type*}
    (A B : (X → ℝ) → (X → ℝ)) (hA : Monotone A) (hB : Monotone B)
    (hcomm : Function.Commute A B) {f : X → ℝ} (hf : B f ≤ A f) (m : ℕ) :
    B^[m] f ≤ A^[m] f := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc
      B (B^[m] f) ≤ B (A^[m] f) := hB ih
      _ = A^[m] (B f) := (hcomm.symm.iterate_right m f)
      _ ≤ A^[m] (A f) := hA.iterate m hf
      _ = A (A^[m] f) := (Function.iterate_succ_apply A m f).symm.trans
        (Function.iterate_succ_apply' A m f)

theorem mixedAverage_mono {X : Type*} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {A B : (X → ℝ) → (X → ℝ)} (hA : Monotone A) (hB : Monotone B) :
    Monotone (mixedAverage p A B) := by
  intro f g hfg S
  exact add_le_add (mul_le_mul_of_nonneg_left (hB hfg S) (sub_nonneg.mpr hp1))
    (mul_le_mul_of_nonneg_left (hA hfg S) hp0)

theorem finiteClauseAverage_commute_mix {n : ℕ} {C D E : Type*}
    [Fintype C] [Fintype D] [Fintype E] (satC : C → Assignment n → Prop)
    (satD : D → Assignment n → Prop) (satE : E → Assignment n → Prop) (p : ℝ) :
    Function.Commute (finiteClauseAverage satC)
      (mixedAverage p (finiteClauseAverage satD) (finiteClauseAverage satE)) := by
  intro f
  unfold mixedAverage
  rw [finiteClauseAverage_add, finiteClauseAverage_const_mul, finiteClauseAverage_const_mul,
    finiteClauseAverage_commute satC satD f, finiteClauseAverage_commute satC satE f]

theorem auxiliaryAverage_alive {n k : ℕ} (hn : 0 < n) (S : Finset (Assignment n)) :
    auxiliaryAverage k alive S = alive S * (1 - (forcedFraction S / 2)^k) := by
  rw [auxiliaryAverage, embeddedAverage_alive hn, embeddedForced_id]
  congr 2
  unfold forcedFraction
  ring

theorem forced_card_partition {r s : ℕ} (S : Finset (Assignment (r + s))) :
    (forcedVariables S).card = (embeddedForced S (Fin.castAdd s)).card +
      (embeddedForced S (Fin.natAdd r)).card := by
  have h := Fin.sum_univ_add (fun i : Fin (r + s) =>
    if i ∈ forcedVariables S then (1 : ℕ) else 0)
  simpa only [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.filter_mem_eq_inter, Finset.univ_inter, embeddedForced] using h

theorem partition_kill_convex {r s k : ℕ} (hr : 0 < r) (hs : 0 < s)
    (S : Finset (Assignment (r + s))) :
    (forcedFraction S / 2)^k ≤
      ((r : ℝ) / (r + s)) * (((embeddedForced S (Fin.castAdd s)).card : ℝ) / (2 * r))^k +
      ((s : ℝ) / (r + s)) * (((embeddedForced S (Fin.natAdd r)).card : ℝ) / (2 * s))^k := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hsum : (r : ℝ) / (r + s) + (s : ℝ) / (r + s) = 1 := by field_simp
  have h := (convexOn_pow (𝕜 := ℝ) k).2
    (show ((embeddedForced S (Fin.castAdd s)).card : ℝ) / (2 * r) ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; positivity)
    (show ((embeddedForced S (Fin.natAdd r)).card : ℝ) / (2 * s) ∈ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; positivity)
    (show 0 ≤ (r : ℝ) / (r + s) by positivity)
    (show 0 ≤ (s : ℝ) / (r + s) by positivity) hsum
  simp only [smul_eq_mul] at h
  convert h using 1
  congr 1
  unfold forcedFraction
  rw [forced_card_partition, Nat.cast_add, Nat.cast_add]
  field_simp

theorem globalAverage_ge_local {r s k : ℕ} (hr : 0 < r) (hs : 0 < s) :
    mixedAverage ((r : ℝ) / (r + s)) (embeddedAverage (Fin.castAdd s) k)
      (embeddedAverage (Fin.natAdd r) k) alive ≤ auxiliaryAverage k alive := by
  intro S
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hw : 1 - (r : ℝ) / (r + s) = (s : ℝ) / (r + s) := by field_simp; ring
  unfold mixedAverage
  rw [embeddedAverage_alive hr, embeddedAverage_alive hs, auxiliaryAverage_alive (by omega), hw]
  have h := mul_le_mul_of_nonneg_left (partition_kill_convex (k := k) hr hs S) (alive_nonneg S)
  have hsum : (r : ℝ) / (r + s) + (s : ℝ) / (r + s) = 1 := by field_simp
  have hsum_mul := congrArg (fun x : ℝ => alive S * x) hsum
  nlinarith

theorem mixed_finiteAverage_iterate {n : ℕ} {C D : Type*} [Fintype C] [Fintype D]
    (satC : C → Assignment n → Prop) (satD : D → Assignment n → Prop)
    (p : ℝ) (m : ℕ) (f : Finset (Assignment n) → ℝ) :
    (mixedAverage p (finiteClauseAverage satC) (finiteClauseAverage satD))^[m] f =
      (fun S => binomialMean p m (fun j =>
        ((finiteClauseAverage satC)^[j] ((finiteClauseAverage satD)^[m - j] f)) S)) := by
  induction m with
  | zero => simp [binomialMean]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    unfold mixedAverage
    rw [finiteClauseAverage_binomialMean, finiteClauseAverage_binomialMean]
    funext S
    rw [binomialMean]
    congr 1
    · congr 1
      apply binomialMean_congr
      intro j hj
      rw [(finiteClauseAverage_commute satD satC).iterate_right j,
        ← Function.iterate_succ_apply' (finiteClauseAverage satD) (m - j) f]
      rw [show (m - j).succ = m.succ - j by omega]
    · congr 1
      apply binomialMean_congr
      intro j hj
      rw [← Function.iterate_succ_apply' (finiteClauseAverage satC) j]
      simp only [Nat.add_sub_add_right]

theorem blockSet_nonempty {r s : ℕ} (S : Finset (Assignment r)) (T : Finset (Assignment s)) :
    (blockSet S T).Nonempty ↔ S.Nonempty ∧ T.Nonempty := by
  constructor
  · rintro ⟨σ, hσ⟩
    have h := (mem_blockSet S T σ).mp hσ
    exact ⟨⟨_, h.1⟩, ⟨_, h.2⟩⟩
  · rintro ⟨⟨σ, hσ⟩, ⟨τ, hτ⟩⟩
    refine ⟨Fin.addCases σ τ, ?_⟩
    simpa only [mem_blockSet, Fin.addCases_left, Fin.addCases_right] using And.intro hσ hτ

theorem alive_blockSet {r s : ℕ} (S : Finset (Assignment r)) (T : Finset (Assignment s)) :
    alive (blockSet S T) = alive S * alive T := by
  simp only [alive, blockSet_nonempty]
  split_ifs <;> simp_all

theorem filter_blockSet_left {r s k : ℕ} (S : Finset (Assignment r))
    (T : Finset (Assignment s)) (C : AuxiliaryClause r k) :
    (blockSet S T).filter (fun σ => auxiliarySatisfies σ (embedAuxiliaryClause (Fin.castAdd s) C)) =
      blockSet (S.filter (fun σ => auxiliarySatisfies σ C)) T := by
  ext σ
  constructor
  · intro h
    obtain ⟨hσ, hC⟩ := Finset.mem_filter.mp h
    obtain ⟨hS, hT⟩ := (mem_blockSet S T σ).mp hσ
    exact (mem_blockSet _ _ σ).mpr ⟨Finset.mem_filter.mpr ⟨hS, hC⟩, hT⟩
  · intro h
    obtain ⟨hS, hT⟩ := (mem_blockSet _ _ σ).mp h
    obtain ⟨hS, hC⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨(mem_blockSet S T σ).mpr ⟨hS, hT⟩, hC⟩

theorem filter_blockSet_right {r s k : ℕ} (S : Finset (Assignment r))
    (T : Finset (Assignment s)) (C : AuxiliaryClause s k) :
    (blockSet S T).filter (fun σ => auxiliarySatisfies σ (embedAuxiliaryClause (Fin.natAdd r) C)) =
      blockSet S (T.filter (fun σ => auxiliarySatisfies σ C)) := by
  ext σ
  constructor
  · intro h
    obtain ⟨hσ, hC⟩ := Finset.mem_filter.mp h
    obtain ⟨hS, hT⟩ := (mem_blockSet S T σ).mp hσ
    exact (mem_blockSet _ _ σ).mpr ⟨hS, Finset.mem_filter.mpr ⟨hT, hC⟩⟩
  · intro h
    obtain ⟨hS, hT⟩ := (mem_blockSet _ _ σ).mp h
    obtain ⟨hT, hC⟩ := Finset.mem_filter.mp hT
    exact Finset.mem_filter.mpr ⟨(mem_blockSet S T σ).mpr ⟨hS, hT⟩, hC⟩

theorem auxiliarySurvival_succ {n k m : ℕ} (S : Finset (Assignment n)) :
    auxiliarySurvival k (m + 1) S = uniformMean (fun C : AuxiliaryClause n k =>
      auxiliarySurvival k m (S.filter (fun σ => auxiliarySatisfies σ C))) := by
  unfold auxiliarySurvival
  rw [Function.iterate_succ_apply']
  rfl

theorem local_iterates_block {r s k : ℕ} (j l : ℕ) (S : Finset (Assignment r))
    (T : Finset (Assignment s)) :
    ((embeddedAverage (Fin.castAdd s) k)^[j]
      ((embeddedAverage (Fin.natAdd r) k)^[l] alive)) (blockSet S T) =
      auxiliarySurvival k j S * auxiliarySurvival k l T := by
  induction j generalizing S T with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    change _ = alive S * auxiliarySurvival k l T
    induction l generalizing T with
    | zero => exact alive_blockSet S T
    | succ l ih =>
      rw [Function.iterate_succ_apply', auxiliarySurvival_succ, ← uniformMean_const_mul]
      unfold embeddedAverage finiteClauseAverage
      apply uniformMean_congr
      intro C
      rw [filter_blockSet_right]
      exact ih _
  | succ j ih =>
    rw [Function.iterate_succ_apply', auxiliarySurvival_succ, ← uniformMean_mul_const]
    unfold embeddedAverage finiteClauseAverage
    apply uniformMean_congr
    intro C
    rw [filter_blockSet_left]
    exact ih _ _

theorem auxiliary_interpolation {r s k : ℕ} (hr : 0 < r) (hs : 0 < s) (m : ℕ) :
    binomialMean ((r : ℝ) / (r + s)) m (fun j =>
      auxiliaryProbability r k j * auxiliaryProbability s k (m - j)) ≤
      auxiliaryProbability (r + s) k m := by
  have hp0 : 0 ≤ (r : ℝ) / (r + s) := by positivity
  have hp1 : (r : ℝ) / (r + s) ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < r + s)).mpr
    exact le_add_of_nonneg_right (Nat.cast_nonneg s)
  have h := iterate_compare_of_commute (auxiliaryAverage (n := r + s) k)
    (mixedAverage ((r : ℝ) / (r + s)) (embeddedAverage (Fin.castAdd s) k)
      (embeddedAverage (Fin.natAdd r) k))
    (fun _ _ h => finiteClauseAverage_mono _ h) (mixedAverage_mono hp0 hp1
      (fun _ _ h => finiteClauseAverage_mono _ h) (fun _ _ h => finiteClauseAverage_mono _ h))
    (finiteClauseAverage_commute_mix _ _ _ _) (globalAverage_ge_local hr hs) m Finset.univ
  change _ ≤ auxiliaryProbability (r + s) k m at h
  convert h using 1
  unfold embeddedAverage
  rw [mixed_finiteAverage_iterate]
  apply binomialMean_congr
  intro j hj
  change _ = ((embeddedAverage (Fin.castAdd s) k)^[j]
      ((embeddedAverage (Fin.natAdd r) k)^[m - j] alive)) Finset.univ
  rw [← blockSet_univ r s, local_iterates_block]
  rfl

end

end FixedClauseThreshold

end OAI

-- ---- platform node ----
open OAI OAI.FixedClauseThreshold
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.FixedClauseThreshold.auxiliary_interpolation := @_root_.OAI.FixedClauseThreshold.auxiliary_interpolation
