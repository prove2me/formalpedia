-- Prove2me | solution 1 for OAI.ThorpCompatibility.grid_entropy_charge
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:55:39.679376+00:00
-- url     : https://prove2.me/submissions/ef50d773-68ee-417f-86d0-efecca136587

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/ExposureEntropy.lean:L80-L107
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.grid_entropy_charge. The node keeps its source
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
import Theorems.Thm_OAI_ThorpCompatibility_Law_condEntropy_eq_mean
import Theorems.Thm_OAI_ThorpCompatibility_Law_condEntropy_light_comparison
import Theorems.Thm_OAI_ThorpCompatibility_Law_entropy_chain
import Theorems.Thm_OAI_ThorpCompatibility_Law_entropy_chain_history
import Theorems.Thm_OAI_ThorpCompatibility_Law_mean_predict
import Theorems.Thm_OAI_ThorpCompatibility_average_columnCost_good

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

lemma sum_inv_sub (n : ℕ) :
    (∑ t : Fin n, 1 / ((n - (t : ℕ) : ℕ) : ℝ)) = (harmonic n : ℝ) := by
  rw [sum_reverse_succ n (fun k => 1 / (k : ℝ)),
    Fin.sum_univ_eq_sum_range (fun k => 1 / ((k + 1 : ℕ) : ℝ))]
  simp [harmonic, one_div]

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

lemma mean_sub (P : Law α) (f g : α → ℝ) :
    P.mean (fun a => f a - g a) = P.mean f - P.mean g := by
  simp [mean, mul_sub, Finset.sum_sub_distrib]

lemma mean_mul_const (P : Law α) (f : α → ℝ) (c : ℝ) :
    P.mean (fun a => f a * c) = P.mean f * c := by
  simp [mean, ← mul_assoc, Finset.sum_mul]

lemma mean_const_mul (P : Law α) (c : ℝ) (f : α → ℝ) :
    P.mean (fun a => c * f a) = c * P.mean f := by
  simpa [mul_comm] using P.mean_mul_const f c

lemma mean_mono (P : Law α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    P.mean f ≤ P.mean g := by
  exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (P.nonneg a)

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

lemma entropy_map_injective (P : Law α) (f : α → β) (hf : Function.Injective f) :
    (P.map f).entropy = P.entropy := by
  classical
  have hm (a : α) : (P.map f).mass (f a) = P.mass a := by
    simp [map, hf.eq_iff]
  unfold entropy
  rw [P.mean_map]
  simp only [Function.comp_def, hm]

lemma condMass_pos (P : Law α) (X : α → β) (Y : α → γ)
    {a : α} (ha : 0 < P.mass a) : 0 < P.condMass X Y a :=
  div_pos (P.map_mass_pos _ ha) (P.map_mass_pos _ ha)

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.LightRescaling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma prob_mono (P : Law α) {S T : α → Prop} (h : ∀ a, S a → T a) :
    P.prob S ≤ P.prob T := by
  apply Finset.sum_le_sum
  intro a _
  by_cases hs : S a
  · simp [hs, h a hs]
  · simp [hs]
    split_ifs <;> simp_all [P.nonneg]

lemma prob_eq_mean (P : Law α) (S : α → Prop) [DecidablePred S] :
    P.prob S = P.mean (fun a => if S a then 1 else 0) := by
  unfold prob mean
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : S a <;> simp [ha]

lemma light_cost_nonneg (P : Law α) (L S : α → Prop) :
    0 ≤ -Real.log (P.prob (fun b => L b ∧ S b) / P.prob L) := by
  apply neg_nonneg.mpr
  apply Real.log_nonpos (div_nonneg (P.prob_nonneg _) (P.prob_nonneg _))
  by_cases hL : P.prob L = 0
  · simp [hL]
  · exact (div_le_one (lt_of_le_of_ne (P.prob_nonneg _) (Ne.symm hL))).mpr
      (P.prob_mono fun _ h => h.1)

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

lemma predict_pos (P : Law α) (X : α → β) (Y : α → γ)
    {a : α} (ha : 0 < P.mass a) : 0 < (P.predict X Y (Y a)).mass (X a) := by
  rw [P.predict_mass_self X Y ha]
  exact P.condMass_pos X Y ha

lemma mean_predict_log (P : Law α) (X : α → β) (Y : α → γ) :
    P.mean (fun a => Real.log ((P.predict X Y (Y a)).mass (X a))) =
      -P.condEntropy X Y := by
  rw [P.condEntropy_eq_mean, neg_neg]
  exact P.mean_congr_support fun a ha => congrArg Real.log (P.predict_mass_self X Y ha)

lemma mean_predict_prob (P : Law α) (X : α → β) (Y : α → γ) (S : γ → β → Prop) :
    P.mean (fun a => (P.predict X Y (Y a)).prob (S (Y a))) =
      P.prob (fun a => S (Y a) (X a)) := by
  simp_rw [prob_eq_mean]
  exact P.mean_predict X Y (fun y x => if S y x then 1 else 0)

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.RankAverages ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β : Type*} [Fintype α] [Fintype β]

lemma mean_comm (P : Law α) (Q : Law β) (f : α → β → ℝ) :
    P.mean (fun a => Q.mean (f a)) = Q.mean (fun b => P.mean (fun a => f a b)) := by
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

end Law
open Finset

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

lemma priorCols_eq_iff {A D : ℕ} (e : Equiv.Perm (Fin D)) (k : Fin D)
    (a b : Grid A D) :
    priorCols e k a = priorCols e k b ↔ ∀ l, e l < e k → a.2 l = b.2 l := by
  constructor
  · intro h l hl
    have h' := congrFun h l
    simpa [priorCols, hl] using h'
  · intro h
    funext l
    by_cases hl : e l < e k <;> simp [priorCols, hl, h l]

namespace Law
lemma condEntropy_eq_of_fibers {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (P : Law α) (X : α → β) (Y : α → γ) (Z : α → δ)
    (h : ∀ a b, Y a = Y b ↔ Z a = Z b) :
    P.condEntropy X Y = P.condEntropy X Z := by
  unfold condEntropy
  rw [P.entropy_eq_of_fibers Y Z h,
    P.entropy_eq_of_fibers (fun a => (X a, Y a)) (fun a => (X a, Z a))
      (by intro a b; simp only [Prod.mk.injEq, h a b])]

lemma condEntropy_out_eq_of_fibers {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (P : Law α) (X : α → β) (V : α → δ) (Y : α → γ)
    (h : ∀ a b, X a = X b ↔ V a = V b) :
    P.condEntropy X Y = P.condEntropy V Y := by
  unfold condEntropy
  rw [P.entropy_eq_of_fibers (fun a => (X a, Y a)) (fun a => (V a, Y a))
      (by intro a b; simp only [Prod.mk.injEq, h a b])]
end Law

lemma grid_inner_chain {A D : ℕ} (Q : Law (Grid A D))
    (e : Equiv.Perm (Fin D)) (k : Fin D) :
    (∑ i : Fin A, Q.condEntropy (fun a => a.2 k i) (gridPast e k i)) =
      Q.condEntropy (fun a => a.2 k) (fun a => (a.1, priorCols e k a)) := by
  rw [show (∑ i : Fin A, Q.condEntropy (fun a => a.2 k i) (gridPast e k i)) =
      (∑ i : Fin A, Q.condEntropy (fun a => a.2 k i)
        (fun a => ((a.1, priorCols e k a),
          Law.history (fun h : Fin A => fun b : Grid A D => b.2 k h) i a))) from rfl,
    Q.entropy_chain_history]
  apply Q.condEntropy_out_eq_of_fibers
  intro a b
  constructor
  · intro h
    exact Equiv.ext (congrFun h)
  · intro h
    simp [h]

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

lemma priorCols_history_fibers {A D : ℕ} (e : Equiv.Perm (Fin D)) (k : Fin D)
    (a b : Grid A D) : priorCols e k a = priorCols e k b ↔
      Law.history (fun t : Fin D => fun c : Grid A D => c.2 (e.symm t)) (e k) a =
      Law.history (fun t : Fin D => fun c : Grid A D => c.2 (e.symm t)) (e k) b := by
  rw [priorCols_eq_iff, Law.history_eq_iff]
  constructor
  · intro h t ht
    exact h (e.symm t) (by simpa using ht)
  · intro h l hl
    simpa using h (e l) hl

lemma grid_outer_chain {A D : ℕ} (Q : Law (Grid A D)) (e : Equiv.Perm (Fin D)) :
    (∑ k : Fin D, Q.condEntropy (fun a => a.2 k) (fun a => (a.1, priorCols e k a))) =
      Q.entropy - (Q.map Prod.fst).entropy := by
  have h (k : Fin D) :
      Q.condEntropy (fun a => a.2 k) (fun a => (a.1, priorCols e k a)) =
      Q.condEntropy (fun a => a.2 (e.symm (e k))) (fun a => (a.1,
        Law.history (fun t : Fin D => fun c : Grid A D => c.2 (e.symm t)) (e k) a)) := by
    simp only [e.symm_apply_apply]
    apply Q.condEntropy_eq_of_fibers
    intro a b
    simp only [Prod.mk.injEq, priorCols_history_fibers]
  simp_rw [h]
  rw [Fintype.sum_equiv e _
    (fun t => Q.condEntropy (fun a => a.2 (e.symm t)) (fun a => (a.1,
      Law.history (fun s : Fin D => fun c : Grid A D => c.2 (e.symm s)) t a)))
    (fun k => rfl)]
  rw [Q.entropy_chain_history]
  unfold Law.condEntropy
  congr 1
  have hf := Q.entropy_eq_of_fibers
    (fun a : Grid A D => ((fun k => a.2 (e.symm k)), a.1)) id (by
      intro a b
      simp only [Prod.mk.injEq, id_eq]
      constructor
      · rintro ⟨hc, hr⟩
        apply Prod.ext hr
        funext k
        simpa using congrFun hc (e k)
      · intro hab
        simp [hab])
  rw [hf, Q.entropy_map_injective id Function.injective_id]

lemma grid_comparison_sum {A D : ℕ} (Q : Law (Grid A D)) (e : Equiv.Perm (Fin D)) :
    (∑ k : Fin D, ∑ i : Fin A,
      (Q.condEntropy (fun a => a.2 k i) (colHistory k i) -
        Q.condEntropy (fun a => a.2 k i) (gridPast e k i))) =
      (Q.map Prod.fst).entropy + (∑ k : Fin D, (Q.map (fun a => a.2 k)).entropy) -
        Q.entropy := by
  simp_rw [Finset.sum_sub_distrib, grid_inner_chain, grid_base_chain]
  rw [grid_outer_chain]
  ring

end ThorpCompatibility

namespace ThorpCompatibility
open Finset

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.GridExposure ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
lemma gridAllowed_actual {A D : ℕ} (a : Grid A D) (ha : Compatible a.1 a.2)
    (e : Equiv.Perm (Fin D)) (k : Fin D) (i : Fin A) :
    gridAllowed k i (gridPast e k i a) (a.2 k i) := by
  intro h σ hσ heq
  dsimp [gridPast, priorCols] at hσ
  split_ifs at hσ with hlt
  · have hσ' : a.2 (a.1 h ((a.1 i).symm k)) = σ := Option.some.inj hσ
    have heq' : a.2 (a.1 h ((a.1 i).symm k)) h =
        a.2 (a.1 i ((a.1 i).symm k)) i := by simpa [hσ'] using heq
    have hi : h = i := ha _ heq'
    simp [hi] at hlt

lemma columnCost_nonneg {A D : ℕ} (Q : Law (Grid A D)) (H : ℝ)
    (e : Equiv.Perm (Fin D)) (k : Fin D) (i : Fin A) (a : Grid A D) :
    0 ≤ columnCost Q H e k i a := by
  unfold columnCost
  split_ifs
  · exact Law.light_cost_nonneg _ _ _
  · rfl

lemma columnCost_le_comparison {A D : ℕ} (Q : Law (Grid A D))
    (hQ : ∀ a, 0 < Q.mass a → Compatible a.1 a.2) (H : ℝ)
    (e : Equiv.Perm (Fin D)) (k : Fin D) (i : Fin A) :
    Q.mean (columnCost Q H e k i) ≤
      Q.condEntropy (fun a => a.2 k i) (colHistory k i) -
      Q.condEntropy (fun a => a.2 k i) (gridPast e k i) := by
  have h := Q.condEntropy_light_comparison (fun a => a.2 k i) (gridPast e k i)
    (fun y => columnPrediction Q k i y.2)
    (fun y => columnLight Q H k i y.2) (gridAllowed k i)
    (fun a ha => Q.predict_pos _ _ ha)
    (fun a ha => gridAllowed_actual a (hQ a ha) e k i)
  change Q.mean (columnCost Q H e k i) ≤
    -Q.mean (fun a => Real.log ((Q.predict (fun a => a.2 k i)
      (colHistory k i) (colHistory k i a)).mass (a.2 k i))) - _ at h
  rwa [Q.mean_predict_log, neg_neg] at h

end ThorpCompatibility

namespace ThorpCompatibility
open Finset

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.ClumpCost ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
lemma exposureError_nonneg {A D : ℕ} (hD : 1 ≤ D) {H K : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K)
    (i : Fin A) : 0 ≤ exposureError A D H K i := by
  have hlog : 0 ≤ Real.log (D : ℝ) := Real.log_nonneg (by exact_mod_cast hD)
  unfold exposureError
  positivity

end ThorpCompatibility

namespace ThorpCompatibility
open Finset

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.HeavyEntries ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
lemma entryHeavyMass_nonneg {A D : ℕ} (Q : Law (Grid A D)) (H : ℝ)
    (k : Fin D) (i : Fin A) (a : Grid A D) : 0 ≤ entryHeavyMass Q H k i a :=
  Law.prob_nonneg _ _

lemma average_columnCost_lower {A D : ℕ} (hD : 2 ≤ D) (Q : Law (Grid A D))
    (a : Grid A D) (hQa : 0 < Q.mass a) (ha : Compatible a.1 a.2)
    {H K : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K) (k : Fin D) (i : Fin A) :
    1 - exposureError A D H K i - 2 * entryHeavyMass Q H k i a -
      (if ¬columnLight Q H k i (colHistory k i a) (a.2 k i) then 1 else 0) -
      (if K < (entryClumpSize k i a : ℝ) then 1 else 0) ≤
      (Law.uniform : Law (Equiv.Perm (Fin D))).mean (fun e => columnCost Q H e k i a) := by
  have hnonneg := (Law.uniform : Law (Equiv.Perm (Fin D))).mean_nonneg
    (fun e => columnCost_nonneg Q H e k i a)
  have herror := exposureError_nonneg (by omega : 1 ≤ D) hH hK i
  have ht := entryHeavyMass_nonneg Q H k i a
  have hlight : entryHeavyMass Q H k i a = 1 -
      (columnPrediction Q k i (colHistory k i a)).prob (columnLight Q H k i (colHistory k i a)) :=
    Law.prob_not _ _
  by_cases hL : 1/2 ≤ (columnPrediction Q k i (colHistory k i a)).prob
      (columnLight Q H k i (colHistory k i a))
  · by_cases haL : columnLight Q H k i (colHistory k i a) (a.2 k i)
    · by_cases hc : K < (entryClumpSize k i a : ℝ)
      · rw [ite_eq_right (not_not_intro haL), ite_eq_left hc]
        linarith
      · rw [ite_eq_right (not_not_intro haL), ite_eq_right hc]
        have hg := average_columnCost_good hD Q a hQa ha hH k i hL haL (le_of_not_gt hc)
        linarith
    · rw [ite_eq_left haL]
      have : (0 : ℝ) ≤ if K < (entryClumpSize k i a : ℝ) then 1 else 0 := by split_ifs <;> norm_num
      linarith
  · have htlarge : 1 ≤ 2 * entryHeavyMass Q H k i a := by linarith
    have h₁ : (0 : ℝ) ≤ if ¬columnLight Q H k i (colHistory k i a) (a.2 k i) then 1 else 0 := by
      split_ifs <;> norm_num
    have h₂ : (0 : ℝ) ≤ if K < (entryClumpSize k i a : ℝ) then 1 else 0 := by split_ifs <;> norm_num
    linarith

lemma mean_entry_heavy {A D : ℕ} (Q : Law (Grid A D)) (H : ℝ) (k : Fin D) (i : Fin A) :
    Q.mean (entryHeavyMass Q H k i) =
      Q.mean (fun a => if ¬columnLight Q H k i (colHistory k i a) (a.2 k i) then 1 else 0) := by
  have h := Q.mean_predict_prob (fun a => a.2 k i) (colHistory k i)
    (fun v w => ¬columnLight Q H k i v w)
  rw [Q.prob_eq_mean] at h
  exact h

lemma mean_columnCost_lower {A D : ℕ} (hD : 2 ≤ D) (Q : Law (Grid A D))
    (hQ : ∀ a, 0 < Q.mass a → Compatible a.1 a.2)
    {H K : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K) (k : Fin D) (i : Fin A) :
    1 - exposureError A D H K i - 3 * Q.mean (entryHeavyMass Q H k i) -
      Q.mean (fun a => if K < (entryClumpSize k i a : ℝ) then 1 else 0) ≤
      (Law.uniform : Law (Equiv.Perm (Fin D))).mean (fun e => Q.mean (columnCost Q H e k i)) := by
  have h := Q.mean_mono_support (fun a ha =>
    average_columnCost_lower hD Q a ha (hQ a ha) hH hK k i)
  rw [Law.mean_comm] at h
  simp only [Law.mean_sub, Law.mean_const, Law.mean_const_mul] at h
  rw [← mean_entry_heavy] at h
  linarith

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.ExposureEntropy ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset

lemma cellRows_weight_sum {α β : Type*} [Fintype α] [Fintype β]
    (r : α → Equiv.Perm β) (v : β × β → ℝ) :
    (∑ i : α, ∑ j : β, v (j, r i j)) =
      ∑ b : β × β, (cellRows r b).card * v b := by
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = ∑ i : α, ∑ k : β, if r i j = k then v (j,k) else 0 := by simp
    _ = ∑ k : β, ∑ i : α, if r i j = k then v (j,k) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      have he : (∑ i : α, if r i j = k then v (j,k) else 0) =
          ∑ _i ∈ cellRows r (j,k), v (j,k) := by
        rw [cellRows, Finset.sum_filter]
      rw [he]
      simp

lemma clumpCount_eq_entries {A D : ℕ} (K : ℝ) (a : Grid A D) :
    (∑ k : Fin D, ∑ i : Fin A, if K < (entryClumpSize k i a : ℝ) then 1 else 0) =
      (clumpCount K a.1 : ℝ) := by
  rw [Finset.sum_comm]
  have he (i : Fin A) :
      (∑ k : Fin D, if K < (entryClumpSize k i a : ℝ) then (1 : ℝ) else 0) =
      ∑ j : Fin D, if K < ((cellRows a.1 (j, a.1 i j)).card : ℝ) then (1 : ℝ) else 0 := by
    apply Fintype.sum_equiv (a.1 i).symm
    intro k
    simp only [entryClumpSize, Equiv.apply_symm_apply]
    by_cases hk : K < ((cellRows a.1 ((a.1 i).symm k, k)).card : ℝ) <;> simp [hk]
  simp_rw [he]
  rw [cellRows_weight_sum a.1
    (fun b => if K < ((cellRows a.1 b).card : ℝ) then (1 : ℝ) else 0)]
  unfold clumpCount
  push_cast
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp

lemma mean_clumpCount_eq_entries {A D : ℕ} (Q : Law (Grid A D)) (K : ℝ) :
    (∑ k : Fin D, ∑ i : Fin A,
      Q.mean (fun a => if K < (entryClumpSize k i a : ℝ) then 1 else 0)) =
      Q.mean (fun a => (clumpCount K a.1 : ℝ)) := by
  rw [show Q.mean (fun a => (clumpCount K a.1 : ℝ)) =
      Q.mean (fun a => ∑ k : Fin D, ∑ i : Fin A,
        if K < (entryClumpSize k i a : ℝ) then 1 else 0) by
    congr 1
    funext a
    exact (clumpCount_eq_entries K a).symm]
  simp_rw [Law.mean_sum]

lemma sum_exposureError {A D : ℕ} (hD : 0 < D) (H K : ℝ) :
    (∑ _ : Fin D, ∑ i : Fin A, exposureError A D H K i) =
      totalExposureError A D H K := by
  have he (i : Fin A) : exposureError A D H K i =
      (1 + Real.log (D : ℝ)) / D +
      (2 * K * H * (1 + Real.log (D : ℝ))) * (1 / ((A - (i : ℕ) : ℕ) : ℝ)) := by
    unfold exposureError
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_inv_sub]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold totalExposureError
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  field_simp [hD0]

lemma grid_entropy_charge {A D : ℕ} (hD : 2 ≤ D) (Q : Law (Grid A D))
    (hQ : ∀ a, 0 < Q.mass a → Compatible a.1 a.2)
    {H K : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K) :
    (A : ℝ) * D - totalExposureError A D H K -
      3 * (∑ k : Fin D, ∑ i : Fin A, Q.mean (entryHeavyMass Q H k i)) -
      Q.mean (fun a => (clumpCount K a.1 : ℝ)) ≤
      (Q.map Prod.fst).entropy + (∑ k : Fin D, (Q.map (fun a => a.2 k)).entropy) - Q.entropy := by
  let E : Law (Equiv.Perm (Fin D)) := Law.uniform
  have hl := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin D))) =>
    Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin A))) =>
      mean_columnCost_lower hD Q hQ hH hK k i))
  have hu (e : Equiv.Perm (Fin D)) :
      (∑ k : Fin D, ∑ i : Fin A, Q.mean (columnCost Q H e k i)) ≤
      (Q.map Prod.fst).entropy + (∑ k : Fin D, (Q.map (fun a => a.2 k)).entropy) - Q.entropy := by
    rw [← grid_comparison_sum Q e]
    exact Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun i _ =>
      columnCost_le_comparison Q hQ H e k i))
  have havg := E.mean_mono hu
  rw [Law.mean_const] at havg
  simp only [Law.mean_sum] at havg
  have hh := le_trans hl havg
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  rw [mean_clumpCount_eq_entries] at hh
  have herr := sum_exposureError (A := A) (by omega : 0 < D) H K
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at herr
  rw [herr] at hh
  nlinarith

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem solution {A D : ℕ} (hD : 2 ≤ D) (Q : Law (Grid A D))
    (hQ : ∀ a, 0 < Q.mass a → Compatible a.1 a.2)
    {H K : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K) :
    (A : ℝ) * D - totalExposureError A D H K -
      3 * (∑ k : Fin D, ∑ i : Fin A, Q.mean (entryHeavyMass Q H k i)) -
      Q.mean (fun a => (clumpCount K a.1 : ℝ)) ≤
      (Q.map Prod.fst).entropy + (∑ k : Fin D, (Q.map (fun a => a.2 k)).entropy) - Q.entropy := by
  first
    | exact OAI.ThorpCompatibility.grid_entropy_charge hD Q hQ hH hK
    | exact OAI.ThorpCompatibility.grid_entropy_charge
    | (apply OAI.ThorpCompatibility.grid_entropy_charge <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.grid_entropy_charge <;> assumption)
