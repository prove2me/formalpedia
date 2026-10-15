-- Prove2me | solution 1 for OAI.ThorpCompatibility.average_columnCost_good
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T00:44:52.395264+00:00
-- url     : https://prove2.me/submissions/876cb8d4-9e4f-4a42-9442-563c1c0a78b0

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpCompatibility/ClumpCost.lean:L61-L112
-- (upload_full_project.md Phase 4): solution for node OAI.ThorpCompatibility.average_columnCost_good. The node keeps its source
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
import Theorems.Thm_OAI_ThorpCompatibility_gridAllowed_iff_rank
import Theorems.Thm_OAI_ThorpCompatibility_random_order_exclusion

-- ---- from OAI.Probability.ThorpCompatibility.Entropy ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

lemma mass_le_map (P : Law α) (f : α → β) (a : α) :
    P.mass a ≤ (P.map f).mass (f a) := by
  classical
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun b => if f b = f a then P.mass b else 0)
    (fun b _ => by split_ifs <;> simp_all [P.nonneg]) (Finset.mem_univ a)
  simpa [map] using h

lemma map_mass_pos (P : Law α) (f : α → β) {a : α} (ha : 0 < P.mass a) :
    0 < (P.map f).mass (f a) := lt_of_lt_of_le ha (P.mass_le_map f a)

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

lemma mass_le_prob (P : Law α) (S : α → Prop) {a : α} (ha : S a) :
    P.mass a ≤ P.prob S := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun b => if S b then P.mass b else 0)
    (fun b _ => by split_ifs <;> simp_all [P.nonneg]) (Finset.mem_univ a)
  simpa [ha, prob] using h

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

end Law
end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.RankLaw ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α : Type*} [Fintype α] [Nonempty α]

omit [Nonempty α] in
lemma restrict_prob (P : Law α) (S T : α → Prop) (hS : 0 < P.prob S) :
    (P.restrict S).prob T = P.prob (fun a => S a ∧ T a) / P.prob S := by
  simp only [prob, P.restrict_mass S hS, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hs : S a <;> by_cases ht : T a <;> simp [hs, ht]

end Law
open Finset

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.GridExposure ----
namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
lemma columnFor_actual {A D : ℕ} (a : Grid A D) (ha : Compatible a.1 a.2)
    (k : Fin D) (i : Fin A) : columnFor a ha ((a.1 i).symm k) (a.2 k i) = k := by
  have hout : outputEquiv a ha ((a.1 i).symm k) i = a.2 k i := by simp
  rw [← hout, columnFor_output]
  simp

end ThorpCompatibility

namespace ThorpCompatibility
open Finset

end ThorpCompatibility

end OAI

-- ---- from OAI.Probability.ThorpCompatibility.ClumpCost ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
lemma protected_mass_le {A D : ℕ} (a : Grid A D) (ha : Compatible a.1 a.2)
    (j k : Fin D) (B : Law (Fin A)) (b : ℝ) (hb : ∀ w, B.mass w ≤ b) :
    B.prob (fun w => columnFor a ha j w = k) ≤ (cellRows a.1 (j,k)).card * b := by
  have he : B.prob (fun w => columnFor a ha j w = k) =
      ∑ h ∈ cellRows a.1 (j,k), B.mass (outputEquiv a ha j h) := by
    unfold Law.prob
    rw [cellRows, Finset.sum_filter]
    symm
    apply Fintype.sum_equiv (outputEquiv a ha j)
    intro h
    simp only [columnFor_output]
    by_cases hh : a.1 h j = k <;> simp [hh]
  rw [he]
  calc
    _ ≤ ∑ _h ∈ cellRows a.1 (j,k), b := Finset.sum_le_sum (fun h _ => hb _)
    _ = _ := by simp

lemma light_restrict_mass_le {α : Type*} [Fintype α] (P : Law α) {b : ℝ}
    (hb : 0 ≤ b) (hL : 1/2 ≤ P.prob (fun w => P.mass w ≤ b)) (w : α) :
    (P.restrict (fun w => P.mass w ≤ b)).mass w ≤ 2 * b := by
  have hp : 0 < P.prob (fun w => P.mass w ≤ b) := by linarith
  rw [P.restrict_mass _ hp]
  split_ifs with hw
  · apply (div_le_iff₀ hp).mpr
    nlinarith
  · simp [mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hb]

lemma average_columnCost_good {A D : ℕ} (hD : 2 ≤ D) (Q : Law (Grid A D))
    (a : Grid A D) (hQa : 0 < Q.mass a) (ha : Compatible a.1 a.2)
    {H K : ℝ} (hH : 0 ≤ H) (k : Fin D) (i : Fin A)
    (hL : 1/2 ≤ (columnPrediction Q k i (colHistory k i a)).prob
      (columnLight Q H k i (colHistory k i a)))
    (haL : columnLight Q H k i (colHistory k i a) (a.2 k i))
    (hK : (entryClumpSize k i a : ℝ) ≤ K) :
    1 - exposureError A D H K i ≤
      (Law.uniform : Law (Equiv.Perm (Fin D))).mean (fun e => columnCost Q H e k i a) := by
  let P := columnPrediction Q k i (colHistory k i a)
  let L := columnLight Q H k i (colHistory k i a)
  let B := P.restrict L
  let j := (a.1 i).symm k
  have hpL : 0 < P.prob L := by dsimp [P, L]; linarith
  have hBpos : 0 < B.mass (a.2 k i) := by
    rw [show B.mass (a.2 k i) = (P.restrict L).mass (a.2 k i) from rfl,
      P.restrict_mass L hpL, ite_eq_left haL]
    exact div_pos (Q.predict_pos _ _ hQa) hpL
  have hα : 0 < B.prob (fun w => columnFor a ha j w = k) :=
    lt_of_lt_of_le hBpos (B.mass_le_prob _ (columnFor_actual a ha k i))
  have hu : (0 : ℝ) < (A - (i : ℕ) : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt i.isLt
  have hbound (w : Fin A) : B.mass w ≤ 2 * (H / ((A - (i : ℕ) : ℕ) : ℝ)) :=
    light_restrict_mass_le P (div_nonneg hH hu.le) hL w
  have hαbound : B.prob (fun w => columnFor a ha j w = k) ≤
      2 * K * H / ((A - (i : ℕ) : ℕ) : ℝ) := by
    have h₁ := protected_mass_le a ha j k B _ hbound
    have h₂ := mul_le_mul_of_nonneg_right hK (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
      (div_nonneg hH hu.le))
    dsimp [entryClumpSize] at h₂
    dsimp [j] at h₁
    calc
      _ ≤ (cellRows a.1 ((a.1 i).symm k, k)).card * (2 * (H / ((A - (i : ℕ) : ℕ) : ℝ))) := h₁
      _ ≤ K * (2 * (H / ((A - (i : ℕ) : ℕ) : ℝ))) := h₂
      _ = _ := by ring
  have hcost (e : Equiv.Perm (Fin D)) : columnCost Q H e k i a =
      -Real.log (B.prob (fun w => e k ≤ e (columnFor a ha j w))) := by
    unfold columnCost
    rw [ite_eq_left haL]
    rw [show B.prob (fun w => e k ≤ e (columnFor a ha j w)) =
      P.prob (fun w => L w ∧ gridAllowed k i (gridPast e k i a) w) / P.prob L by
        rw [show B = P.restrict L from rfl, P.restrict_prob L _ hpL]
        congr 2
        funext w
        rw [gridAllowed_iff_rank]]
  simp_rw [hcost]
  have h := random_order_exclusion hD B (columnFor a ha j) k hα
  have hlog : 0 ≤ 1 + Real.log (D : ℝ) := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ D by exact_mod_cast (by omega : 1 ≤ D))
    linarith
  have hmul := mul_le_mul_of_nonneg_right hαbound hlog
  dsimp [exposureError]
  linarith

end ThorpCompatibility

namespace ThorpCompatibility
open Finset

end ThorpCompatibility

end OAI

-- ---- platform node ----
open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem solution {A D : ℕ} (hD : 2 ≤ D) (Q : Law (Grid A D))
    (a : Grid A D) (hQa : 0 < Q.mass a) (ha : Compatible a.1 a.2)
    {H K : ℝ} (hH : 0 ≤ H) (k : Fin D) (i : Fin A)
    (hL : 1/2 ≤ (columnPrediction Q k i (colHistory k i a)).prob
      (columnLight Q H k i (colHistory k i a)))
    (haL : columnLight Q H k i (colHistory k i a) (a.2 k i))
    (hK : (entryClumpSize k i a : ℝ) ≤ K) :
    1 - exposureError A D H K i ≤
      (Law.uniform : Law (Equiv.Perm (Fin D))).mean (fun e => columnCost Q H e k i a) := by
  first
    | exact OAI.ThorpCompatibility.average_columnCost_good hD Q a hQa ha hH k i hL haL hK
    | exact OAI.ThorpCompatibility.average_columnCost_good
    | (apply OAI.ThorpCompatibility.average_columnCost_good <;> assumption)
    | (intros; apply OAI.ThorpCompatibility.average_columnCost_good <;> assumption)
