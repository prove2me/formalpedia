-- Prove2me | solution 1 for OAI.RandomKSAT.insertVar_stop_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T19:53:56.311765+00:00
-- url     : https://prove2.me/submissions/c2ddce8d-e55b-4d4b-bc0c-258b51e4d5df

-- Generated from openai/math@1581d4c lean/OAI/Probability/SATVariance/InsertionVariance.lean:L233-L292
-- (upload_full_project.md Phase 4): solution for node OAI.RandomKSAT.insertVar_stop_lower. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SATVariance
import Definitions.Def_OAI_Probability_SATVariance_ClauseCombinatorics__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FrozenReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_BlockKilling
import Definitions.Def_OAI_Probability_SATVariance_MarkovReplacement__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiniteVariance
import Definitions.Def_OAI_Probability_SATVariance_LifetimePotential
import Definitions.Def_OAI_Probability_SATVariance_RootDisintegration__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_FiberRefresh
import Definitions.Def_OAI_Probability_SATVariance_PairEvolution
import Definitions.Def_OAI_Probability_SATVariance_HiddenTests
import Definitions.Def_OAI_Probability_SATVariance_WeightedRewards
import Definitions.Def_OAI_Probability_SATVariance_CountMoments
import Definitions.Def_OAI_Probability_SATVariance_SupportProbabilities__SATVariance
import Definitions.Def_OAI_Probability_SATVariance_OmissionCompression
import Definitions.Def_OAI_Probability_SATVariance_CapBridge
import Definitions.Def_OAI_Probability_SATVariance_ShuffleAverages
import Definitions.Def_OAI_Probability_SATVariance_BystanderStops
import Definitions.Def_OAI_Probability_SATVariance_InsertionVariance
import Theorems.Thm_OAI_RandomKSAT_harmless_private
import Theorems.Thm_OAI_RandomKSAT_insertion_moments
import Theorems.Thm_OAI_RandomKSAT_listStop_insert

-- ---- from OAI.Probability.SATVariance.MarkovReplacement ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_mono.{u_1} {α : Type u_1} [Fintype α] {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    favg f ≤ favg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a) (by positivity)

lemma favg_const.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (c : ℝ) :
    favg (fun _ : α => c) = c := by
  simp [favg, Fintype.card_ne_zero]

lemma favg_add.{u_1} {α : Type u_1} [Fintype α] (f g : α → ℝ) :
    favg (fun a => f a + g a) = favg f + favg g := by
  simp only [favg, Finset.sum_add_distrib, add_div]

lemma favg_sub.{u_1} {α : Type u_1} [Fintype α] (f g : α → ℝ) :
    favg (fun a => f a - g a) = favg f - favg g := by
  simp only [favg, Finset.sum_sub_distrib, sub_div]

lemma favg_mul.{u_1} {α : Type u_1} [Fintype α] (c : ℝ) (f : α → ℝ) :
    favg (fun a => c*f a) = c*favg f := by
  simp only [favg, ← Finset.mul_sum]
  ring

lemma favg_nonneg.{u_1} {α : Type u_1} [Fintype α] {f : α → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ favg f := by
  exact div_nonneg (Finset.sum_nonneg fun a _ => h a) (by positivity)

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.FiniteVariance ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma favg_sq_sub_const.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) (c : ℝ) :
    favg (fun a => (f a-c)^2) = favg (fun a => (f a)^2) - 2*c*favg f + c^2 := by
  have he : (fun a => (f a-c)^2) = (fun a => (f a)^2 - (2*c)*f a + c^2) := by
    funext a; ring
  rw [he, favg_add, favg_sub, favg_mul, favg_const]

lemma fvariance_centered.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) :
    fvariance f = favg (fun a => (f a-favg f)^2) := by
  rw [favg_sq_sub_const, fvariance]; ring

lemma fvariance_nonneg.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) :
    0 ≤ fvariance f := by
  rw [fvariance_centered]
  exact favg_nonneg fun a => sq_nonneg _

lemma favg_sq_le.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (f : α → ℝ) :
    (favg f)^2 ≤ favg (fun a => (f a)^2) := sub_nonneg.mp (fvariance_nonneg f)

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.BystanderStops ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma listStop_le {n k : ℕ} (l : List (Clause n k)) : listStop l ≤ l.length+1 :=
  Nat.find_min' _ (Or.inl rfl)

end RandomKSAT

end

end OAI

-- ---- from OAI.Probability.SATVariance.InsertionVariance ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

lemma inserts_length.{u_1} {α : Type u_1} {b l r : List α} (h : Inserts b l r) :
    r.length = b.length+l.length := by
  induction h with
  | nil => simp
  | cons c h i hi ih => rw [List.length_insertIdx_of_le_length hi, ih, List.length_cons]; omega

lemma inserts_perm.{u_1} {α : Type u_1} {b l r : List α} (h : Inserts b l r) : r.Perm (b++l) := by
  induction h with
  | nil => simp
  | cons c h i hi ih => exact (List.perm_insertIdx c _ hi).trans (ih.cons c)

lemma insertAvg_congr.{u_1} {α : Type u_1} (b l : List α) {f g : List α → ℝ}
    (h : ∀ r, Inserts b l r → f r = g r) : insertAvg b l f = insertAvg b l g := by
  induction b generalizing f g with
  | nil => exact h l (Inserts.nil l)
  | cons c b ih =>
    apply ih
    intro r hr
    unfold insertKernel
    congr 1
    funext i
    exact h _ (Inserts.cons c hr i (by omega))

lemma insertAvg_mono.{u_1} {α : Type u_1} (b l : List α) {f g : List α → ℝ}
    (h : ∀ r, Inserts b l r → f r ≤ g r) : insertAvg b l f ≤ insertAvg b l g := by
  induction b generalizing f g with
  | nil => exact h l (Inserts.nil l)
  | cons c b ih =>
    apply ih
    intro r hr
    exact favg_mono (fun i => h _ (Inserts.cons c hr i (by omega)))

lemma insertAvg_const.{u_1} {α : Type u_1} (b l : List α) (a : ℝ) :
    insertAvg b l (fun _ => a) = a := by
  induction b with
  | nil => rfl
  | cons c b ih =>
    change insertAvg b l (fun r => favg (fun _ : Fin (r.length+1) => a)) = a
    simp only [favg_const,ih]

lemma insertAvg_sub.{u_1} {α : Type u_1} (b l : List α) (f g : List α → ℝ) :
    insertAvg b l (fun r => f r-g r) = insertAvg b l f-insertAvg b l g := by
  induction b generalizing f g with
  | nil => rfl
  | cons c b ih =>
    change insertAvg b l (fun r => favg (fun i : Fin (r.length+1) =>
      f (r.insertIdx i c)-g (r.insertIdx i c))) = _
    simp only [favg_sub]
    exact ih _ _

lemma insertAvg_mul.{u_1} {α : Type u_1} (b l : List α) (a : ℝ) (f : List α → ℝ) :
    insertAvg b l (fun r => a*f r) = a*insertAvg b l f := by
  induction b generalizing f with
  | nil => rfl
  | cons c b ih =>
    change insertAvg b l (fun r => favg (fun i : Fin (r.length+1) => a*f (r.insertIdx i c))) = _
    simp only [favg_mul]
    exact ih _

lemma insertAvg_sq_le.{u_1} {α : Type u_1} (b l : List α) (f : List α → ℝ) :
    (insertAvg b l f)^2 ≤ insertAvg b l (fun r => (f r)^2) := by
  induction b generalizing f with
  | nil => exact le_refl _
  | cons c b ih =>
    apply (ih (insertKernel c f)).trans
    apply insertAvg_mono
    intro r _
    exact favg_sq_le _

lemma insertVar_nonneg.{u_1} {α : Type u_1} (b l : List α) (f : List α → ℝ) : 0 ≤ insertVar b l f :=
  sub_nonneg.mpr (insertAvg_sq_le b l f)

lemma insertVar_congr.{u_1} {α : Type u_1} (b l : List α) {f g : List α → ℝ}
    (h : ∀ r, Inserts b l r → f r = g r) : insertVar b l f = insertVar b l g := by
  unfold insertVar
  rw [insertAvg_congr b l h,insertAvg_congr b l (fun r hr => congrArg (fun x : ℝ => x^2) (h r hr))]

lemma insertVar_mul.{u_1} {α : Type u_1} (b l : List α) (a : ℝ) (f : List α → ℝ) :
    insertVar b l (fun r => a*f r) = a^2*insertVar b l f := by
  have he : (fun r => (a*f r)^2) = (fun r => a^2*(f r)^2) := by funext r; ring
  simp only [insertVar,he,insertAvg_mul]
  ring

lemma insertVar_cons.{u_1} {α : Type u_1} (b l : List α) (c : α) (f : List α → ℝ) :
    insertVar (c::b) l f = insertVar b l (insertKernel c f) +
      insertAvg b l (fun r => fvariance (fun i : Fin (r.length+1) => f (r.insertIdx i c))) := by
  change insertAvg b l (insertKernel c (fun r => (f r)^2)) -
    (insertAvg b l (insertKernel c f))^2 =
    (insertAvg b l (fun r => (insertKernel c f r)^2) -
      (insertAvg b l (insertKernel c f))^2) +
    insertAvg b l (fun r => insertKernel c (fun r => (f r)^2) r -
      (insertKernel c f r)^2)
  rw [insertAvg_sub]
  ring

lemma private_perm {n k : ℕ} {c : Clause n k} {l r : List (Clause n k)}
    (h : l.Perm r) (hc : Private c l) : Private c r := by
  obtain ⟨v,hv⟩ := hc
  exact ⟨v,fun d hd => hv d (h.mem_iff.mpr hd)⟩

lemma private_harmless {n k : ℕ} {c : Clause n k} {l : List (Clause n k)}
    (hc : Private c l) : Harmless c l := by
  obtain ⟨v,hv⟩ := hc
  exact harmless_private c l v hv

lemma inserts_stop_bounds {n k : ℕ} {b l r : List (Clause n k)} (hb : Bystanders b l)
    (h : Inserts b l r) : listStop l ≤ listStop r ∧ listStop r ≤ listStop l+b.length := by
  induction h with
  | nil => simp
  | @cons c b l r h i hi ih =>
    have hh : Harmless c r := private_harmless (private_perm (inserts_perm h).symm hb.1)
    rw [listStop_insert c r hh i hi]
    have ht := ih hb.2
    simp only [List.length_cons]
    split_ifs <;> omega

lemma insertKernel_stop {n k : ℕ} (c : Clause n k) (r : List (Clause n k))
    (hc : Harmless c r) :
    insertKernel c (fun s => (listStop s:ℝ)) r =
      (1+1/((r.length:ℝ)+1))*(listStop r:ℝ) := by
  unfold insertKernel
  have he (i : Fin (r.length+1)) := listStop_insert c r hc i (by omega)
  simp only [he]
  exact_mod_cast (insertion_moments (Nat.succ_pos _) (listStop_le r)).1

lemma insertion_variance_stop {n k : ℕ} (c : Clause n k) (r : List (Clause n k))
    (hc : Harmless c r) :
    fvariance (fun i : Fin (r.length+1) => (listStop (r.insertIdx i c):ℝ)) =
      (listStop r:ℝ)*((r.length:ℝ)+1-listStop r)/((r.length:ℝ)+1)^2 := by
  have he (i : Fin (r.length+1)) := listStop_insert c r hc i (by omega)
  simp only [he]
  exact_mod_cast (insertion_moments (Nat.succ_pos _) (listStop_le r)).2

lemma insertVar_stop_lower {n k : ℕ} {b l : List (Clause n k)} (hb : Bystanders b l)
    {A C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (hAt : A ≤ (listStop l:ℝ)) (hCt : C ≤ (l.length:ℝ)+1-listStop l)
    (hlen : (b.length:ℝ)+l.length+1 ≤ D) :
    (b.length:ℝ)*(A*C/D^2) ≤ insertVar b l (fun r => (listStop r:ℝ)) := by
  induction b with
  | nil => simp [insertVar,insertAvg]
  | cons c b ih =>
    have hlen' : (b.length:ℝ)+l.length+1 ≤ D := by
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hlen
      linarith
    have hi := ih hb.2 hlen'
    rw [insertVar_cons]
    let a : ℝ := 1+1/((b.length:ℝ)+l.length+1)
    have ha : 1 ≤ a := by
      dsimp [a]
      have : (0:ℝ) ≤ 1/((b.length:ℝ)+l.length+1) := by positivity
      linarith
    have he : insertVar b l (insertKernel c (fun r => (listStop r:ℝ))) =
        a^2*insertVar b l (fun r => (listStop r:ℝ)) := by
      rw [←insertVar_mul]
      apply insertVar_congr
      intro r hr
      rw [insertKernel_stop c r (private_harmless (private_perm (inserts_perm hr).symm hb.1))]
      have hrlen := inserts_length hr
      simp only [hrlen,Nat.cast_add]
      rfl
    rw [he]
    have hstep : A*C/D^2 ≤ insertAvg b l (fun r =>
        fvariance (fun i : Fin (r.length+1) => (listStop (r.insertIdx i c):ℝ))) := by
      rw [←insertAvg_const b l (A*C/D^2)]
      apply insertAvg_mono
      intro r hr
      rw [insertion_variance_stop c r
        (private_harmless (private_perm (inserts_perm hr).symm hb.1))]
      have ht := inserts_stop_bounds hb.2 hr
      have hrlen := inserts_length hr
      have hr0 : 0 < (r.length:ℝ)+1 := by positivity
      have ht0 : 0 ≤ (listStop r:ℝ) := by positivity
      have hs : 0 ≤ (r.length:ℝ)+1-listStop r := by
        have := listStop_le r
        exact sub_nonneg.mpr (by exact_mod_cast this)
      have hAr : A ≤ (listStop r:ℝ) := hAt.trans (by exact_mod_cast ht.1)
      have hCr : C ≤ (r.length:ℝ)+1-listStop r := by
        have ht' : (listStop r:ℝ) ≤ listStop l+b.length := by exact_mod_cast ht.2
        have hrl : (r.length:ℝ) = b.length+l.length := by exact_mod_cast hrlen
        linarith
      have hrD : (r.length:ℝ)+1 ≤ D := by
        rw [hrlen,Nat.cast_add]
        exact hlen'
      calc
        _ ≤ (listStop r:ℝ)*((r.length:ℝ)+1-listStop r)/D^2 :=
          div_le_div_of_nonneg_right (mul_le_mul hAr hCr hC ht0) (sq_nonneg D)
        _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg ht0 hs)
          (sq_pos_of_pos hr0) (by nlinarith)
    have hv := insertVar_nonneg b l (fun r => (listStop r:ℝ))
    have ha2 : 1 ≤ a^2 := by nlinarith
    have hv' := mul_le_mul_of_nonneg_right ha2 hv
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

end RandomKSAT

end

end OAI

-- ---- platform node ----
open OAI OAI.RandomKSAT
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal


theorem solution : type_of% @_root_.OAI.RandomKSAT.insertVar_stop_lower := @_root_.OAI.RandomKSAT.insertVar_stop_lower
