-- Prove2me | solution 1 for OAI.ThorpCompatibility.weightedCompatibility_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:14:03.264282+00:00
-- url     : https://prove2.me/submissions/15fc313b-6210-4372-a247-a4afc5b46682

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/Main.lean:L30-L107
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.weightedCompatibility_bound. The node keeps its source
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
import Definitions.Def_OAI_Probability_ThorpCompatibility_HeavyEntries
import Definitions.Def_OAI_Probability_ThorpCompatibility_ExposureEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_UniformSupport
import Definitions.Def_OAI_Probability_ThorpCompatibility_HeavyColumns
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridDeficits
import Definitions.Def_OAI_Probability_ThorpCompatibility_VariationalBound
import Theorems.Thm_OAI_ThorpCompatibility_Law_condEntropy_eq_mean
import Theorems.Thm_OAI_ThorpCompatibility_Law_entropy_chain
import Theorems.Thm_OAI_ThorpCompatibility_Law_heavy_mass_uniformOn
import Theorems.Thm_OAI_ThorpCompatibility_Law_map_mass_pos_iff
import Theorems.Thm_OAI_ThorpCompatibility_Law_mean_predict
import Theorems.Thm_OAI_ThorpCompatibility_Law_tilt_log_partition
import Theorems.Thm_OAI_ThorpCompatibility_Law_weighted_gibbs_le
import Theorems.Thm_OAI_ThorpCompatibility_clump_deficit_bound
import Theorems.Thm_OAI_ThorpCompatibility_compatibilityWeight_support
import Theorems.Thm_OAI_ThorpCompatibility_entropy_normalization_error
import Theorems.Thm_OAI_ThorpCompatibility_grid_deficit_decomposition
import Theorems.Thm_OAI_ThorpCompatibility_grid_entropy_charge
import Theorems.Thm_OAI_ThorpCompatibility_log_factorial_upper
import Theorems.Thm_OAI_ThorpCompatibility_rowDeficit_le_joint

-- ---- from OAI.Probability.ThorpCompatibility.LogEstimates ----
namespace OAI

open scoped Classical

namespace ThorpCompatibility
open Finset

lemma sum_reverse_succ (n : ℕ) (f : ℕ → ℝ) :
    (∑ t : Fin n, f (n - (t : ℕ))) = ∑ t : Fin n, f ((t : ℕ) + 1) := by
  apply Fintype.sum_equiv Fin.revPerm
  intro t
  congr 1
  change n - (t : ℕ) = n - ((t : ℕ) + 1) + 1
  omega

lemma sum_log_sub (n : ℕ) :
    (∑ t : Fin n, Real.log ((n - (t : ℕ) : ℕ) : ℝ)) = Real.log (n.factorial : ℝ) := by
  rw [sum_reverse_succ n (fun k => Real.log (k : ℝ)),
    Fin.sum_univ_eq_sum_range (fun k => Real.log ((k + 1 : ℕ) : ℝ)),
    Nat.factorial_eq_prod_range_add_one, Nat.cast_prod]
  exact (Real.log_prod (fun i _ => by positivity)).symm

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.FiniteLaw ----
namespace OAI

open scoped Classical

namespace ThorpCompatibility
open Finset

namespace Law
variable {α β : Type*} [Fintype α] [Fintype β]

lemma mean_map (P : Law α) (f : α → β) (g : β → ℝ) :
    (P.map f).mean g = P.mean (g ∘ f) := by
  classical
  simp only [mean, map, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

lemma pointwise_entropy_lower {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hzero : q = 0 → p = 0) : p - q ≤ p * Real.log (p / q) := by
  by_cases hq0 : q = 0
  · simp [hq0, hzero hq0]
  have h := mul_le_mul_of_nonneg_left
    (Real.self_sub_one_le_mul_log (div_nonneg hp hq)) hq
  calc
    p - q = q * (p / q - 1) := by field_simp
    _ ≤ q * (p / q * Real.log (p / q)) := h
    _ = p * Real.log (p / q) := by field_simp

lemma relativeEntropy_nonneg (P Q : Law α)
    (hzero : ∀ a, Q.mass a = 0 → P.mass a = 0) :
    0 ≤ P.relativeEntropy Q := by
  have h := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
    pointwise_entropy_lower (P.nonneg a) (Q.nonneg a) (hzero a)
  simpa [relativeEntropy, Finset.sum_sub_distrib, P.total, Q.total] using h

lemma relativeEntropy_uniform [Nonempty α] (P : Law α) :
    P.relativeEntropy uniform = P.uniformDeficit := by
  classical
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [relativeEntropy, uniform, one_div, div_inv_eq_mul]
  have hterm (a : α) :
      P.mass a * Real.log (P.mass a * Fintype.card α) =
        P.mass a * Real.log (P.mass a) + P.mass a * Real.log (Fintype.card α) := by
    by_cases ha : P.mass a = 0
    · simp [ha]
    · rw [Real.log_mul ha hc, mul_add]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, P.total, one_mul]
  exact add_comm _ _

lemma uniformDeficit_nonneg [Nonempty α] (P : Law α) :
    0 ≤ P.uniformDeficit := by
  rw [← P.relativeEntropy_uniform]
  apply P.relativeEntropy_nonneg
  intro a h
  have hc : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [uniform, hc] at h

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.Entropy ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma mean_const (P : Law α) (c : ℝ) : P.mean (fun _ => c) = c := by
  simp [mean, ← Finset.sum_mul, P.total]

lemma mean_add (P : Law α) (f g : α → ℝ) :
    P.mean (fun a => f a + g a) = P.mean f + P.mean g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

lemma mean_sub (P : Law α) (f g : α → ℝ) :
    P.mean (fun a => f a - g a) = P.mean f - P.mean g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

lemma mean_mul_const (P : Law α) (f : α → ℝ) (c : ℝ) :
    P.mean (fun a => f a * c) = P.mean f * c := by
  simp [mean, ← mul_assoc, Finset.sum_mul]

lemma mean_const_mul (P : Law α) (c : ℝ) (f : α → ℝ) :
    P.mean (fun a => c * f a) = c * P.mean f := by
  simpa [mul_comm] using P.mean_mul_const f c

lemma mean_congr_support (P : Law α) {f g : α → ℝ}
    (h : ∀ a, 0 < P.mass a → f a = g a) : P.mean f = P.mean g := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : P.mass a = 0
  · simp [ha]
  · rw [h a (lt_of_le_of_ne (P.nonneg a) (Ne.symm ha))]

lemma mass_le_map (P : Law α) (f : α → β) (a : α) :
    P.mass a ≤ (P.map f).mass (f a) := by
  classical
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun b => if f b = f a then P.mass b else 0)
    (fun b _ => by split_ifs <;> simp_all [P.nonneg]) (Finset.mem_univ a)
  simpa [map] using h

lemma map_mass_pos (P : Law α) (f : α → β) {a : α} (ha : 0 < P.mass a) :
    0 < (P.map f).mass (f a) := lt_of_lt_of_le ha (P.mass_le_map f a)

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.EntropyBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α : Type*} [Fintype α]

lemma mean_sum {ι : Type*} [Fintype ι] (P : Law α) (f : ι → α → ℝ) :
    P.mean (fun a => ∑ i, f i a) = ∑ i, P.mean (f i) := by
  simp only [mean, Finset.mul_sum]
  exact Finset.sum_comm

lemma mean_nonneg (P : Law α) {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) : 0 ≤ P.mean f :=
  Finset.sum_nonneg fun a _ => mul_nonneg (P.nonneg a) (hf a)

lemma mean_mono_support (P : Law α) {f g : α → ℝ}
    (h : ∀ a, 0 < P.mass a → f a ≤ g a) : P.mean f ≤ P.mean g := by
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : P.mass a = 0
  · simp [ha]
  · exact mul_le_mul_of_nonneg_left (h a (lt_of_le_of_ne (P.nonneg a) (Ne.symm ha)))
      (P.nonneg a)

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.Prediction ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma restrict_mass (P : Law α) (S : α → Prop) (h : 0 < P.prob S) (a : α) :
    (P.restrict S).mass a = (if S a then P.mass a else 0) / P.prob S := by
  simp [restrict, h]

lemma prob_eq_map_mass (P : Law α) (Y : α → γ) (y : γ) :
    P.prob (fun a => Y a = y) = (P.map Y).mass y := by rfl

lemma predict_mass (P : Law α) (X : α → β) (Y : α → γ) (y : γ)
    (hy : 0 < (P.map Y).mass y) (x : β) :
    (P.predict X Y y).mass x =
      (P.map (fun a => (X a, Y a))).mass (x, y) / (P.map Y).mass y := by
  have hp : 0 < P.prob (fun a => Y a = y) := hy
  simp only [predict, map, P.restrict_mass _ hp, prob_eq_map_mass]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hx : X a = x <;> by_cases hy' : Y a = y <;> simp [hx, hy']

lemma predict_mass_self (P : Law α) (X : α → β) (Y : α → γ)
    {a : α} (ha : 0 < P.mass a) :
    (P.predict X Y (Y a)).mass (X a) = P.condMass X Y a := by
  exact P.predict_mass X Y (Y a) (P.map_mass_pos Y ha) (X a)

lemma predict_mass_zero (P : Law α) (X : α → β) (Y : α → γ) {y : γ} {x : β}
    (hy : 0 < (P.map Y).mass y)
    (h : ∀ a, 0 < P.mass a → Y a = y → X a ≠ x) :
    (P.predict X Y y).mass x = 0 := by
  rw [P.predict_mass X Y y hy x]
  suffices hz : (P.map (fun a => (X a, Y a))).mass (x, y) = 0 by simp [hz]
  by_contra hn
  obtain ⟨a, he, ha⟩ := (P.map_mass_pos_iff _ _).mp
    (lt_of_le_of_ne ((P.map _).nonneg _) (Ne.symm hn))
  exact h a ha (congrArg Prod.snd he) (congrArg Prod.fst he)

lemma mean_predict_log (P : Law α) (X : α → β) (Y : α → γ) :
    P.mean (fun a => Real.log ((P.predict X Y (Y a)).mass (X a))) =
      -P.condEntropy X Y := by
  rw [P.condEntropy_eq_mean, neg_neg]
  exact P.mean_congr_support fun a ha => congrArg Real.log (P.predict_mass_self X Y ha)

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.EntropyChain ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma entropy_eq_of_fibers (P : Law α) (X : α → β) (Y : α → γ)
    (hf : ∀ a b, X a = X b ↔ Y a = Y b) : (P.map X).entropy = (P.map Y).entropy := by
  have hm (a : α) : (P.map X).mass (X a) = (P.map Y).mass (Y a) := by
    simp only [map]
    apply Finset.sum_congr rfl
    intro b _
    rw [hf b a]
  unfold entropy
  rw [P.mean_map, P.mean_map]
  simp only [Function.comp_def, hm]

omit [Fintype α] [Fintype β] in
lemma history_eq_iff {n : ℕ} (X : Fin n → α → β) (t : ℕ) (a b : α) :
    history X t a = history X t b ↔ ∀ i : Fin n, (i : ℕ) < t → X i a = X i b := by
  constructor
  · intro h i hi
    have he := congrFun h i
    simpa [history, hi] using he
  · intro h
    funext i
    by_cases hi : (i : ℕ) < t
    · simp [history, hi, h i hi]
    · simp [history, hi]

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.GridEntropy ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

namespace Law
end Law

lemma grid_base_chain {A D : ℕ} (Q : Law (Grid A D)) (k : Fin D) :
    (∑ i : Fin A, Q.condEntropy (fun a => a.2 k i) (colHistory k i)) =
      (Q.map (fun a => a.2 k)).entropy := by
  change (∑ i : Fin A, Q.condEntropy (fun a => a.2 k i)
      (Law.history (fun h : Fin A => fun b : Grid A D => b.2 k h) i)) = _
  rw [Q.entropy_chain]
  apply Q.entropy_eq_of_fibers
  intro a b
  constructor
  · intro h
    exact Equiv.ext (congrFun h)
  · intro h
    simp [h]

end ThorpCompatibility

namespace ThorpCompatibility
open Finset

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.FactorialBounds ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

lemma log_step_bound (n : ℕ) :
    ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) - (n : ℝ) * Real.log n ≤
      Real.log ((n : ℝ) + 1) + 1 := by
  by_cases hn : n = 0
  · simp [hn]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hn1 hn0)) hn0.le
  rw [Real.log_div hn1.ne' hn0.ne'] at h
  have hr : (n : ℝ) * (((n : ℝ) + 1) / (n : ℝ) - 1) = 1 := by
    field_simp
    ring
  rw [hr] at h
  nlinarith

lemma log_descFactorial_integral (n k : ℕ) (hk : k ≤ n) :
    (n : ℝ) * Real.log n - (n - k : ℕ) * Real.log (n - k : ℕ) - k ≤
      Real.log (n.descFactorial k : ℝ) := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = 0 := Nat.eq_zero_of_le_zero hk
    simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hk' : k ≤ n := Nat.le_of_succ_le_succ hk
      have h₁ := ih k hk'
      have h₂ := log_step_bound n
      have hd : (n.descFactorial k : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.descFactorial_pos.mpr hk').ne'
      rw [Nat.succ_descFactorial_succ, Nat.cast_mul,
        Real.log_mul (by positivity) hd]
      simp only [Nat.succ_sub_succ_eq_sub, Nat.cast_succ] at *
      linarith

lemma log_descFactorial_lower (n k : ℕ) (hk : k ≤ n) :
    (k : ℝ) * (Real.log n - 1) ≤ Real.log (n.descFactorial k : ℝ) := by
  have h := log_descFactorial_integral n k hk
  have hnk : (n - k : ℕ) * Real.log (n - k : ℕ) ≤
      (n - k : ℕ) * Real.log n := by
    by_cases hz : n - k = 0
    · simp [hz]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz)
    exact_mod_cast Nat.sub_le n k
  rw [Nat.cast_sub hk] at h hnk
  nlinarith

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.HeavyEntries ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
lemma entryHeavyMass_nonneg {A D : ℕ} (Q : Law (Grid A D)) (H : ℝ)
    (k : Fin D) (i : Fin A) (a : Grid A D) : 0 ≤ entryHeavyMass Q H k i a :=
  Law.prob_nonneg _ _

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.UniformSupport ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α : Type*} [Fintype α]

lemma mean_neg (P : Law α) (f : α → ℝ) : P.mean (fun a => -f a) = -P.mean f := by
  simp [mean, Finset.sum_neg_distrib]

lemma mean_prediction_entropy {β γ : Type*} [Fintype β] [Fintype γ]
    (P : Law α) (X : α → β) (Y : α → γ) :
    P.mean (fun a => (P.predict X Y (Y a)).entropy) = P.condEntropy X Y := by
  have h := P.mean_predict X Y (fun y b => -Real.log ((P.predict X Y y).mass b))
  simp only [mean_neg] at h
  rw [P.mean_predict_log, neg_neg] at h
  simpa only [entropy, mean_neg] using h

end Law
open Finset

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.HeavyColumns ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
lemma card_remainingValues {A : ℕ} (σ : Equiv.Perm (Fin A)) (i : Fin A) :
    (remainingValues σ i).card = A - (i : ℕ) := by simp [remainingValues]

lemma mem_remainingValues {A : ℕ} (σ : Equiv.Perm (Fin A)) (i w : Fin A) :
    w ∈ remainingValues σ i ↔ i ≤ σ.symm w := by
  simp only [remainingValues, Finset.mem_map, Finset.mem_Ici, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨h, hi, hw⟩
    rwa [← hw, σ.symm_apply_apply]
  · intro h
    exact ⟨σ.symm w, h, σ.apply_symm_apply w⟩

lemma remainingValues_nonempty {A : ℕ} (σ : Equiv.Perm (Fin A)) (i : Fin A) :
    (remainingValues σ i).Nonempty := by
  apply Finset.card_pos.mp
  rw [card_remainingValues]
  exact Nat.sub_pos_of_lt i.isLt

lemma columnPrediction_unused {A D : ℕ} (Q : Law (Grid A D)) (k : Fin D) (i : Fin A)
    (a : Grid A D) (hQa : 0 < Q.mass a) (w : Fin A) (hw : w ∉ remainingValues (a.2 k) i) :
    (columnPrediction Q k i (colHistory k i a)).mass w = 0 := by
  apply Q.predict_mass_zero _ _ (Q.map_mass_pos _ hQa)
  intro b _ hprev hvalue
  have hlt : (a.2 k).symm w < i := lt_of_not_ge (by simpa [mem_remainingValues] using hw)
  have he := (Law.history_eq_iff _ _ b a).mp hprev ((a.2 k).symm w) hlt
  change b.2 k ((a.2 k).symm w) = a.2 k ((a.2 k).symm w) at he
  rw [(a.2 k).apply_symm_apply] at he
  have hi : (a.2 k).symm w = i := (b.2 k).injective (he.trans hvalue.symm)
  exact (ne_of_lt hlt) hi

lemma entry_heavy_mass_bound {A D : ℕ} (Q : Law (Grid A D)) (k : Fin D) (i : Fin A)
    (a : Grid A D) (hQa : 0 < Q.mass a) {H : ℝ} (hH : 0 < H) :
    (Real.log H - 1) * entryHeavyMass Q H k i a ≤
      Real.log ((A - (i : ℕ) : ℕ) : ℝ) -
        (columnPrediction Q k i (colHistory k i a)).entropy := by
  have h := (columnPrediction Q k i (colHistory k i a)).heavy_mass_uniformOn
    (remainingValues (a.2 k) i) (remainingValues_nonempty (a.2 k) i)
    (fun w hw => columnPrediction_unused Q k i a hQa w hw) hH
  rw [card_remainingValues] at h
  simpa only [entryHeavyMass, columnLight, not_le] using h

lemma mean_entry_heavy_bound {A D : ℕ} (Q : Law (Grid A D)) (k : Fin D) (i : Fin A)
    {H : ℝ} (hH : 0 < H) :
    (Real.log H - 1) * Q.mean (entryHeavyMass Q H k i) ≤
      Real.log ((A - (i : ℕ) : ℕ) : ℝ) -
        Q.condEntropy (fun a => a.2 k i) (colHistory k i) := by
  have h := Q.mean_mono_support (fun a ha => entry_heavy_mass_bound Q k i a ha hH)
  rw [Law.mean_const_mul, Law.mean_sub, Law.mean_const] at h
  change _ ≤ _ - Q.mean (fun a => (Q.predict (fun b => b.2 k i)
    (colHistory k i) (colHistory k i a)).entropy) at h
  rwa [Q.mean_prediction_entropy] at h

lemma column_heavy_bound {A D : ℕ} (Q : Law (Grid A D)) (k : Fin D)
    {H : ℝ} (hH : 0 < H) :
    (Real.log H - 1) * (∑ i : Fin A, Q.mean (entryHeavyMass Q H k i)) ≤
      (Q.map (fun a => a.2 k)).uniformDeficit := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin A))) =>
    mean_entry_heavy_bound Q k i hH)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_log_sub, grid_base_chain] at h
  simpa only [Law.uniformDeficit, Law.entropy, Law.mean, Fintype.card_perm,
    Fintype.card_fin, sub_neg_eq_add] using h

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.GridDeficits ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

lemma rowDeficit_nonneg {A D : ℕ} (Q : Law (Grid A D)) : 0 ≤ rowDeficit Q :=
  Finset.sum_nonneg fun _ _ => Law.uniformDeficit_nonneg _

lemma colDeficit_nonneg {A D : ℕ} (Q : Law (Grid A D)) : 0 ≤ colDeficit Q :=
  Finset.sum_nonneg fun _ _ => Law.uniformDeficit_nonneg _

lemma heavyTotal_nonneg {A D : ℕ} (Q : Law (Grid A D)) (H : ℝ) :
    0 ≤ heavyTotal Q H := by
  apply Finset.sum_nonneg
  intro k _
  apply Finset.sum_nonneg
  intro i _
  exact Q.mean_nonneg (fun a => entryHeavyMass_nonneg Q H k i a)

lemma heavyTotal_log_bound {A D : ℕ} (Q : Law (Grid A D)) {m : ℝ}
    (hm : 0 < m) (hl : 200 ≤ Real.log m) :
    Real.log m * heavyTotal Q (m^(1/100:ℝ)) ≤ 200 * colDeficit Q := by
  have h := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin D))) =>
    column_heavy_bound Q k (Real.rpow_pos_of_pos hm (1/100:ℝ)))
  rw [← Finset.mul_sum] at h
  change (Real.log (m^(1/100:ℝ)) - 1) * heavyTotal Q (m^(1/100:ℝ)) ≤ colDeficit Q at h
  rw [Real.log_rpow hm] at h
  have hM := heavyTotal_nonneg Q (m^(1/100:ℝ))
  nlinarith

lemma absorb_entropy_losses {ell R r C M T J n E : ℝ}
    (hl : 1000 ≤ ell) (hr : 0 ≤ r) (hR : r ≤ R) (hC : 0 ≤ C)
    (hM : ell * M ≤ 200 * C) (hT : ell * T ≤ 400 * R + 400)
    (hJ : R + C + n - E - 3*M - T ≤ J) :
    n - E - 1 + (1 - 1000/ell) * (r+C) ≤ J := by
  have hl0 : 0 < ell := by linarith
  have hrR : 0 ≤ R := le_trans hr hR
  have hloss : 3*M + T - 1 ≤ 1000*(R+C)/ell := by
    apply (le_div_iff₀ hl0).mpr
    nlinarith
  have ht : 0 ≤ 1 - 1000/ell := sub_nonneg.mpr ((div_le_one hl0).mpr hl)
  have hmarg := mul_le_mul_of_nonneg_left hR ht
  have heq : 1000*(R+C)/ell = (1000/ell)*(R+C) := by ring
  rw [heq] at hloss
  nlinarith

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.EntropyEstimate ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
lemma grid_entropy_estimate {A D : ℕ} (hD : 2 ≤ D) (Q : Law (Grid A D))
    (hQ : ∀ a, 0 < Q.mass a → Compatible a.1 a.2) {m : ℝ}
    (hm : 0 < m) (hl : 1000 ≤ Real.log m)
    (hmgf : uniformMean (fun r : Rows A D =>
      Real.exp ((1/400 * Real.log m) * clumpCount (m^(1/100:ℝ)) r)) ≤ 2) :
    (A : ℝ)*D - totalExposureError A D (m^(1/100:ℝ)) (m^(1/100:ℝ)) - 1 +
      (1 - 1000/Real.log m) * (rowDeficit Q + colDeficit Q) ≤ Q.uniformDeficit := by
  have h := grid_entropy_charge hD Q hQ (Real.rpow_nonneg hm.le (1/100:ℝ))
    (Real.rpow_nonneg hm.le (1/100:ℝ))
  have hj := grid_deficit_decomposition Q
  apply absorb_entropy_losses hl (rowDeficit_nonneg Q) (rowDeficit_le_joint Q)
    (colDeficit_nonneg Q) (heavyTotal_log_bound Q hm (le_trans (by norm_num) hl))
    (clump_deficit_bound Q m hmgf)
  change Q.uniformDeficit = jointRowDeficit Q + colDeficit Q + _ at hj
  change _ - 3 * heavyTotal Q (m^(1/100:ℝ)) - _ ≤ _ at h
  linarith

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.WeightedGibbs ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility

end ThorpCompatibility

namespace ThorpCompatibility
namespace Law
open Finset
variable {α : Type*} [Fintype α]

lemma exists_mass_pos (P : Law α) : ∃ x, 0 < P.mass x := by
  by_contra h
  push Not at h
  have hh := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset α)) => h x)
  simp only [P.total, Finset.sum_const_zero] at hh
  linarith

lemma uniformMean_rpow_pos [Nonempty α] (P : Law α) (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hs : ∀ x, w x = 0 → P.mass x = 0) (p : ℝ) :
    0 < uniformMean (fun x => (w x)^p) := by
  obtain ⟨x,hx⟩ := P.exists_mass_pos
  have hwx : 0 < w x := lt_of_le_of_ne (hw x) (by
    intro he
    exact hx.ne' (hs x he.symm))
  unfold uniformMean
  apply div_pos
  · exact lt_of_lt_of_le (Real.rpow_pos_of_pos hwx p)
      (Finset.single_le_sum (fun y _ => Real.rpow_nonneg (hw y) p) (Finset.mem_univ x))
  · exact_mod_cast Fintype.card_pos

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.VariationalBound ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

lemma marginalFactor_nonneg {α : Type*} [Fintype α] (θ : ℝ) (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) : 0 ≤ marginalFactor θ w := by
  simp only [marginalFactor, Real.rpow_eq_pow]
  apply Real.rpow_nonneg
  exact div_nonneg (Finset.sum_nonneg (fun x _ => Real.rpow_nonneg (hw x) _))
    (Nat.cast_nonneg _)

lemma Law.marginalFactor_pos {α : Type*} [Fintype α] [Nonempty α]
    (P : Law α) (θ : ℝ) (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hs : ∀ x, w x = 0 → P.mass x = 0) :
    0 < marginalFactor θ w := by
  simp only [marginalFactor, Real.rpow_eq_pow]
  exact Real.rpow_pos_of_pos (P.uniformMean_rpow_pos w hw hs _) θ

lemma compatibilityWeight_nonneg {A D : ℕ}
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ)
    (hw : ∀ i σ, 0 ≤ w i σ) (hv : ∀ k σ, 0 ≤ v k σ) (a : Grid A D) :
    0 ≤ compatibilityWeight w v a := by
  unfold compatibilityWeight
  split_ifs
  · exact mul_nonneg (Finset.prod_nonneg (fun i _ => hw i _))
      (Finset.prod_nonneg (fun k _ => hv k _))
  · rfl

lemma Law.map_support_weight {α β : Type*} [Fintype α] [Fintype β]
    (P : Law α) (f : α → β) (w : β → ℝ)
    (hs : ∀ a, 0 < P.mass a → 0 < w (f a)) (x : β) (hx : w x = 0) :
    (P.map f).mass x = 0 := by
  by_contra hn
  obtain ⟨a,he,ha⟩ := (P.map_mass_pos_iff f x).mp
    (lt_of_le_of_ne ((P.map f).nonneg x) (Ne.symm hn))
  have hw := hs a ha
  rw [he,hx] at hw
  exact lt_irrefl _ hw

lemma grid_log_weight_mean {A D : ℕ} (Q : Law (Grid A D))
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ)
    (hw : ∀ i σ, 0 ≤ w i σ) (hv : ∀ k σ, 0 ≤ v k σ)
    (hs : ∀ a, 0 < Q.mass a → 0 < compatibilityWeight w v a) :
    Q.mean (fun a => Real.log (compatibilityWeight w v a)) =
      (∑ i : Fin A, (Q.map (fun a => a.1 i)).mean (fun σ => Real.log (w i σ))) +
      (∑ k : Fin D, (Q.map (fun a => a.2 k)).mean (fun σ => Real.log (v k σ))) := by
  calc
    _ = Q.mean (fun a => (∑ i, Real.log (w i (a.1 i))) +
        (∑ k, Real.log (v k (a.2 k)))) := by
      apply Q.mean_congr_support
      intro a ha
      obtain ⟨hc, hr, hd⟩ := compatibilityWeight_support w v hw hv (hs a ha)
      rw [compatibilityWeight, ite_eq_left hc,
        Real.log_mul (Finset.prod_pos (fun i _ => hr i)).ne'
          (Finset.prod_pos (fun k _ => hd k)).ne',
        Real.log_prod (fun i _ => (hr i).ne'), Real.log_prod (fun k _ => (hd k).ne')]
    _ = _ := by
      rw [Q.mean_add, Law.mean_sum, Law.mean_sum]
      simp only [Law.mean_map, Function.comp_def]

lemma grid_weight_variational {A D : ℕ} (Q : Law (Grid A D)) {θ : ℝ} (hθ : 0 < θ)
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ)
    (hw : ∀ i σ, 0 ≤ w i σ) (hv : ∀ k σ, 0 ≤ v k σ)
    (hs : ∀ a, 0 < Q.mass a → 0 < compatibilityWeight w v a) :
    Q.mean (fun a => Real.log (compatibilityWeight w v a)) - θ*(rowDeficit Q + colDeficit Q) ≤
      (∑ i, Real.log (marginalFactor θ (w i))) + (∑ k, Real.log (marginalFactor θ (v k))) := by
  have hwr (i : Fin A) := (Q.map (fun a => a.1 i)).weighted_gibbs_le hθ (w i) (hw i)
    (Q.map_support_weight (fun a => a.1 i) (w i) (fun a ha =>
      (compatibilityWeight_support w v hw hv (hs a ha)).2.1 i))
  have hvc (k : Fin D) := (Q.map (fun a => a.2 k)).weighted_gibbs_le hθ (v k) (hv k)
    (Q.map_support_weight (fun a => a.2 k) (v k) (fun a ha =>
      (compatibilityWeight_support w v hw hv (hs a ha)).2.2 k))
  have hr := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin A))) => hwr i)
  have hc := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin D))) => hvc k)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hr hc
  rw [grid_log_weight_mean Q w v hw hv hs]
  unfold rowDeficit colDeficit
  linarith

lemma compatibility_log_mean_bound {A D : ℕ} (hD : 2 ≤ D) {m : ℝ}
    (hm : 0 < m) (hl : 1000 ≤ Real.log m) (hθ : 0 < 1 - 1000/Real.log m)
    (hmgf : uniformMean (fun r : Rows A D =>
      Real.exp ((1/400 * Real.log m) * clumpCount (m^(1/100:ℝ)) r)) ≤ 2)
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ)
    (hw : ∀ i σ, 0 ≤ w i σ) (hv : ∀ k σ, 0 ≤ v k σ)
    (hZ : 0 < ∑ a : Grid A D, compatibilityWeight w v a) :
    Real.log (uniformMean (compatibilityWeight w v)) ≤
      -(A:ℝ)*D + totalExposureError A D (m^(1/100:ℝ)) (m^(1/100:ℝ)) + 1 +
      (∑ i, Real.log (marginalFactor (1-1000/Real.log m) (w i))) +
      (∑ k, Real.log (marginalFactor (1-1000/Real.log m) (v k))) := by
  let Q : Law (Grid A D) := Law.tilt (compatibilityWeight w v) (compatibilityWeight_nonneg w v hw hv) hZ
  have hs (a : Grid A D) (ha : 0 < Q.mass a) : 0 < compatibilityWeight w v a := by
    exact (div_pos_iff_of_pos_right hZ).mp ha
  have hQ (a : Grid A D) (ha : 0 < Q.mass a) : Compatible a.1 a.2 :=
    (compatibilityWeight_support w v hw hv (hs a ha)).1
  have hE := grid_entropy_estimate hD Q hQ hm hl hmgf
  have hW := grid_weight_variational Q hθ w v hw hv hs
  have hG := Law.tilt_log_partition (compatibilityWeight w v) (compatibilityWeight_nonneg w v hw hv) hZ
  change Q.mean _ - Q.uniformDeficit = _ at hG
  linarith

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.Main ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

lemma log_normalizingFactor_upper (A D : ℕ) (hA : 0 < A) (hD : 0 < D) :
    Real.log ((Nat.factorial (A*D) : ℝ) /
      ((Nat.factorial D : ℝ)^A * (Nat.factorial A : ℝ)^D)) ≤
      (A:ℝ)*D + 1 + Real.log ((A:ℝ)*D) := by
  have hn := log_factorial_upper (A*D) (Nat.mul_pos hA hD)
  rw [Nat.cast_mul] at hn
  have hfA := log_descFactorial_lower A A le_rfl
  have hfD := log_descFactorial_lower D D le_rfl
  simp only [Nat.descFactorial_self] at hfA hfD
  have h₁ := mul_le_mul_of_nonneg_left hfA (Nat.cast_nonneg D : (0:ℝ) ≤ D)
  have h₂ := mul_le_mul_of_nonneg_left hfD (Nat.cast_nonneg A : (0:ℝ) ≤ A)
  have hAa : (A:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hA
  have hDd : (D:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  rw [Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  rw [Real.log_mul hAa hDd] at hn ⊢
  nlinarith

lemma weightedCompatibility_bound {A D : ℕ} {m : ℝ}
    (hm : 4 ≤ m) (hmdef : m^2 = (A:ℝ)*D)
    (hl : 1000 ≤ Real.log m) (hθ : 0 < 1-1000/Real.log m)
    (hAl : m/2 ≤ A) (hAu : (A:ℝ) ≤ 2*m)
    (hDl : m/2 ≤ D) (hDu : (D:ℝ) ≤ 2*m)
    (hmgf : uniformMean (fun r : Rows A D =>
      Real.exp ((1/400 * Real.log m) * clumpCount (m^(1/100:ℝ)) r)) ≤ 2)
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ)
    (hw : ∀ i σ, 0 ≤ w i σ) (hv : ∀ k σ, 0 ≤ v k σ) :
    weightedCompatibility A D w v ≤
      Real.exp (50000*((A:ℝ)*D)^(54/100:ℝ)) *
        (∏ i, marginalFactor (1-1000/Real.log m) (w i)) *
        (∏ k, marginalFactor (1-1000/Real.log m) (v k)) := by
  have hm0 : 0 < m := by linarith
  have hA0 : 0 < A := by exact_mod_cast (show (0:ℝ) < A by linarith)
  have hD0 : 0 < D := by exact_mod_cast (show (0:ℝ) < D by linarith)
  have hD2 : 2 ≤ D := by exact_mod_cast (show (2:ℝ) ≤ D by linarith)
  let θ : ℝ := 1-1000/Real.log m
  let a : Grid A D → ℝ := compatibilityWeight w v
  have ha : ∀ x, 0 ≤ a x := compatibilityWeight_nonneg w v hw hv
  by_cases hz : (∑ x : Grid A D, a x) = 0
  · have hW : weightedCompatibility A D w v = 0 := by
      change _ * uniformMean a = 0
      rw [uniformMean, hz, zero_div, mul_zero]
    rw [hW]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (Finset.prod_nonneg (fun i _ => marginalFactor_nonneg θ (w i) (hw i))))
      (Finset.prod_nonneg (fun k _ => marginalFactor_nonneg θ (v k) (hv k)))
  have hZ : 0 < ∑ x : Grid A D, a x :=
    lt_of_le_of_ne (Finset.sum_nonneg (fun x _ => ha x)) (Ne.symm hz)
  let Q : Law (Grid A D) := Law.tilt a ha hZ
  have hs (x : Grid A D) (hx : 0 < Q.mass x) : 0 < compatibilityWeight w v x :=
    (div_pos_iff_of_pos_right hZ).mp hx
  have hwr (i : Fin A) : 0 < marginalFactor θ (w i) :=
    (Q.map (fun x => x.1 i)).marginalFactor_pos θ (w i) (hw i)
      (Q.map_support_weight (fun x => x.1 i) (w i) (fun x hx =>
        (compatibilityWeight_support w v hw hv (hs x hx)).2.1 i))
  have hvc (k : Fin D) : 0 < marginalFactor θ (v k) :=
    (Q.map (fun x => x.2 k)).marginalFactor_pos θ (v k) (hv k)
      (Q.map_support_weight (fun x => x.2 k) (v k) (fun x hx =>
        (compatibilityWeight_support w v hw hv (hs x hx)).2.2 k))
  have hWP : 0 < ∏ i, marginalFactor θ (w i) := Finset.prod_pos (fun i _ => hwr i)
  have hVP : 0 < ∏ k, marginalFactor θ (v k) := Finset.prod_pos (fun k _ => hvc k)
  let F : ℝ := (Nat.factorial (A*D) : ℝ) /
      ((Nat.factorial D : ℝ)^A * (Nat.factorial A : ℝ)^D)
  have hF : 0 < F := by dsimp [F]; positivity
  have hU : 0 < uniformMean a := div_pos hZ (by exact_mod_cast Fintype.card_pos)
  have hL : 0 < weightedCompatibility A D w v := mul_pos hF hU
  have hR : 0 < Real.exp (50000*((A:ℝ)*D)^(54/100:ℝ)) *
      (∏ i, marginalFactor θ (w i)) * (∏ k, marginalFactor θ (v k)) :=
    mul_pos (mul_pos (Real.exp_pos _) hWP) hVP
  apply (Real.log_le_log_iff hL hR).mp
  change Real.log (F * uniformMean a) ≤ _
  rw [Real.log_mul hF.ne' hU.ne',
    Real.log_mul (mul_pos (Real.exp_pos _) hWP).ne' hVP.ne',
    Real.log_mul (Real.exp_pos _).ne' hWP.ne', Real.log_exp,
    Real.log_prod (fun i _ => (hwr i).ne'), Real.log_prod (fun k _ => (hvc k).ne')]
  have hnorm := log_normalizingFactor_upper A D hA0 hD0
  change Real.log F ≤ _ at hnorm
  have hcompat := compatibility_log_mean_bound hD2 hm0 hl hθ hmgf w v hw hv hZ
  change Real.log (uniformMean a) ≤ _ at hcompat
  have herr := entropy_normalization_error (by linarith : 1 ≤ m) hA0 hD0 hAu hDu
  have hp : m^(108/100:ℝ) = ((A:ℝ)*D)^(54/100:ℝ) := by
    calc
      _ = m^((2:ℝ)*(54/100:ℝ)) := by norm_num
      _ = (m^(2:ℝ))^(54/100:ℝ) := Real.rpow_mul hm0.le _ _
      _ = _ := by rw [Real.rpow_two, hmdef]
  have hlog : Real.log ((A:ℝ)*D) = 2*Real.log m := by
    rw [← hmdef, Real.log_pow]
    norm_num
  rw [hp] at herr
  rw [hlog] at hnorm
  change 0 < θ at hθ
  change Real.log (uniformMean a) ≤ -(A:ℝ)*D + _ + 1 +
      (∑ i, Real.log (marginalFactor θ (w i))) +
      (∑ k, Real.log (marginalFactor θ (v k))) at hcompat
  linarith

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem solution {A D : ℕ} {m : ℝ}
    (hm : 4 ≤ m) (hmdef : m^2 = (A:ℝ)*D)
    (hl : 1000 ≤ Real.log m) (hθ : 0 < 1-1000/Real.log m)
    (hAl : m/2 ≤ A) (hAu : (A:ℝ) ≤ 2*m)
    (hDl : m/2 ≤ D) (hDu : (D:ℝ) ≤ 2*m)
    (hmgf : uniformMean (fun r : Rows A D =>
      Real.exp ((1/400 * Real.log m) * clumpCount (m^(1/100:ℝ)) r)) ≤ 2)
    (w : Fin A → Equiv.Perm (Fin D) → ℝ)
    (v : Fin D → Equiv.Perm (Fin A) → ℝ)
    (hw : ∀ i σ, 0 ≤ w i σ) (hv : ∀ k σ, 0 ≤ v k σ) :
    weightedCompatibility A D w v ≤
      Real.exp (50000*((A:ℝ)*D)^(54/100:ℝ)) *
        (∏ i, marginalFactor (1-1000/Real.log m) (w i)) *
        (∏ k, marginalFactor (1-1000/Real.log m) (v k)) := by
  first
    | exact OAI.ThorpCompatibility.weightedCompatibility_bound hm hmdef hl hθ hAl hAu hDl hDu hmgf w v hw hv
    | exact OAI.ThorpCompatibility.weightedCompatibility_bound
    | (apply OAI.ThorpCompatibility.weightedCompatibility_bound <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.weightedCompatibility_bound <;> assumption)
