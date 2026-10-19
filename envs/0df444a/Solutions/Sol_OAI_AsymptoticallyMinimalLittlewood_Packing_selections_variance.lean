-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.selections_variance
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:18:48.819869+00:00
-- url     : https://prove2.me/submissions/71d5cea9-f00f-409d-8684-e47f686a6d22

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/DependentMoments.lean:L111-L149
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.selections_variance. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_avg_prod_injective
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_moments_from_good

-- ---- from OAI.Analysis.Littlewood.Averages ----
namespace OAI

universe uΩ uI uΛ uK uA uJ uY

namespace AsymptoticallyMinimalLittlewood
namespace Packing
noncomputable section
open scoped BigOperators
open Finset

section Average
variable {Ω : Type uΩ} [Fintype Ω] [Nonempty Ω]

lemma avg_const (c : ℝ) : avg (fun _ : Ω ↦ c) = c := by
  simp [avg, Fintype.card_ne_zero]
omit [Nonempty Ω] in
lemma avg_add (f g : Ω → ℝ) : avg (fun ω ↦ f ω+g ω)=avg f+avg g := by
  simp [avg,Finset.sum_add_distrib,add_div]
omit [Nonempty Ω] in
lemma avg_mono {f g : Ω → ℝ} (h : ∀ ω, f ω≤g ω) : avg f≤avg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ ↦ h ω)) (Nat.cast_nonneg _)
lemma avg_nonneg {f : Ω → ℝ} (h : ∀ ω, 0≤f ω) : 0≤avg f := by
  simpa only [avg_const] using avg_mono h
omit [Nonempty Ω] in
lemma avg_prod_type {Λ : Type uΛ} [Fintype Λ] [Nonempty Λ] (f : Ω × Λ → ℝ) :
    avg f = avg (fun ω ↦ avg (fun x ↦ f (ω,x))) := by
  simp only [avg,Fintype.card_prod,Nat.cast_mul,Fintype.sum_prod_type,← Finset.sum_div]
  ring

end Average
end
end Packing
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- from OAI.Analysis.Littlewood.DependentMoments ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement).
private abbrev Finset.prod_le_one₀ := @Finset.prod_le_one

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uκ uA uJ uY uV uK uΩ uI

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

section ProductMoments
variable {κ : Type uκ} {A : Type uA} {J : Type uJ} {Y : Type uY} [Fintype κ] [DecidableEq κ] [Fintype A] [Nonempty A] [DecidableEq A]
  [Fintype J] [Fintype Y] [Nonempty Y]

omit [Nonempty A] in
lemma avg_singleton (a : A) : avg (fun x : A ↦ if x=a then (1 : ℝ) else 0) =
    1/(Fintype.card A : ℝ) := by
  classical
  simp [avg]

lemma avg_independent_selections (c : J → κ) (hc : Function.Injective c) (a : J → A) :
    avg (fun ω : κ → A ↦ ∏ j, if ω (c j)=a j then (1 : ℝ) else 0) =
      (1/(Fintype.card A : ℝ))^(Fintype.card J) := by
  classical
  rw [avg_prod_injective c hc (fun j x ↦ if x=a j then (1 : ℝ) else 0)]
  simp only [avg_singleton,Finset.prod_const,Finset.card_univ]

lemma avg_double_selections (c d : J → κ) (hc : Function.Injective c)
    (hd : Function.Injective d) (hcd : ∀ j l, c j≠d l) (a b : J → A) :
    avg (fun ω : κ → A ↦
      (∏ j, if ω (c j)=a j then (1 : ℝ) else 0)*
      (∏ j, if ω (d j)=b j then (1 : ℝ) else 0)) =
      ((1/(Fintype.card A : ℝ))^(Fintype.card J))^2 := by
  classical
  let c' : J ⊕ J → κ := Sum.elim c d
  let a' : J ⊕ J → A := Sum.elim a b
  have hc' : Function.Injective c' := by
    intro i j hij
    cases i with
    | inl i => cases j with
      | inl j => exact congrArg Sum.inl (hc hij)
      | inr j => exact (hcd i j hij).elim
    | inr i => cases j with
      | inl j => exact (hcd j i hij.symm).elim
      | inr j => exact congrArg Sum.inr (hd hij)
  have h := avg_independent_selections c' hc' a'
  calc
    _ = avg (fun ω : κ → A ↦ ∏ j : J ⊕ J, if ω (c' j)=a' j then (1 : ℝ) else 0) := by
      congr 1; funext ω
      rw [Fintype.prod_sum_type]
      rfl
    _ = _ := by
      rw [h,Fintype.card_sum,pow_add,pow_two]

lemma avg_fst (F : Y → ℝ) : avg (fun yy : Y × Y ↦ F yy.1)=avg F := by
  calc
    _ = avg (fun y : Y ↦ avg (fun _ : Y ↦ F y)) :=
      avg_prod_type (Ω := Y) (Λ := Y) (fun yy : Y × Y ↦ F yy.1)
    _ = _ := by simp only [avg_const]

lemma avg_snd (F : Y → ℝ) : avg (fun yy : Y × Y ↦ F yy.2)=avg F := by
  calc
    _ = avg (fun _ : Y ↦ avg F) :=
      avg_prod_type (Ω := Y) (Λ := Y) (fun yy : Y × Y ↦ F yy.2)
    _ = _ := avg_const _

omit [Fintype κ] in
lemma bad_pair_avg_bound (c : Y → J → κ) (good : Y → Prop) [DecidablePred good]
    {b d : ℝ}
    (hb : avg (fun y ↦ if good y then (0 : ℝ) else 1)≤b)
    (hd : avg (fun yy : Y × Y ↦ if ∃ j l, c yy.1 j=c yy.2 l then (1 : ℝ) else 0)≤d) :
    avg (fun yy : Y × Y ↦ if good yy.1 ∧ good yy.2 ∧ ∀ j l, c yy.1 j≠c yy.2 l
      then (0 : ℝ) else 1)≤2*b+d := by
  classical
  let good₂ : Y × Y → Prop := fun yy ↦ good yy.1 ∧ good yy.2 ∧ ∀ j l, c yy.1 j≠c yy.2 l
  change avg (fun yy ↦ if good₂ yy then (0 : ℝ) else 1)≤2*b+d
  calc
    _ ≤ avg (fun yy : Y × Y ↦ (if good yy.1 then 0 else 1)+
        (if good yy.2 then 0 else 1)+
        (if ∃ j l, c yy.1 j=c yy.2 l then 1 else 0)) := by
      apply avg_mono
      intro yy
      by_cases h₁ : good yy.1
      · by_cases h₂ : good yy.2
        · by_cases h₃ : ∃ j l, c yy.1 j=c yy.2 l
          · simp only [good₂,h₁,h₂,true_and,ite_true,zero_add]
            split_ifs <;> norm_num
          · have h₄ : ∀ j l, c yy.1 j≠c yy.2 l := by
              intro j l h; exact h₃ ⟨j,l,h⟩
            simp [good₂,h₁,h₂,h₄]
        · simp only [good₂,h₁,h₂,true_and,false_and,ite_false,ite_true,zero_add]
          split_ifs <;> norm_num
      · simp only [good₂,h₁,false_and,ite_false]
        split_ifs <;> norm_num
    _ = 2*avg (fun y ↦ if good y then 0 else 1)+
        avg (fun yy : Y × Y ↦ if ∃ j l, c yy.1 j=c yy.2 l then 1 else 0) := by
      rw [avg_add,avg_add]
      rw [avg_fst (fun y : Y ↦ if good y then (0 : ℝ) else 1),
        avg_snd (fun y : Y ↦ if good y then (0 : ℝ) else 1)]
      ring
    _ ≤ _ := by linarith

/-- A finite dependent-row moment estimate.  Dependence is charged only to
same-chunk collisions; rows on distinct chunks use independent coordinates. -/
lemma selections_variance (f : J → Y → (κ → A) → ℝ)
    (c : Y → J → κ) (a : Y → J → A) (good : Y → Prop)
    [DecidablePred good] {b d : ℝ}
    (hf : ∀ j y ω, 0≤f j y ω ∧ f j y ω≤1)
    (hc : ∀ y, good y → Function.Injective (c y))
    (ha : ∀ y, good y → ∀ j ω,
      f j y ω=(if ω (c y j)=a y j then 1 else 0))
    (hb : avg (fun y ↦ if good y then 0 else 1)≤b)
    (hd : avg (fun yy : Y × Y ↦
      if ∃ j l, c yy.1 j=c yy.2 l then 1 else 0)≤d) :
    avg (fun ω : κ → A ↦
      (avg (fun y ↦ ∏ j, f j y ω)-(1/(Fintype.card A : ℝ))^(Fintype.card J))^2)
        ≤ 3*(2*b+d) := by
  classical
  let p : ℝ := (1/(Fintype.card A : ℝ))^(Fintype.card J)
  let good₂ : Y × Y → Prop := fun yy ↦ good yy.1 ∧ good yy.2 ∧
    ∀ j l, c yy.1 j≠c yy.2 l
  have hb0 : 0≤b := (avg_nonneg (by intro y; split_ifs <;> norm_num)).trans hb
  have hd0 : 0≤d := (avg_nonneg (by intro yy; split_ifs <;> norm_num)).trans hd
  have hp : 0≤p := by dsimp [p]; positivity
  have hp1 : p≤1 := by
    apply pow_le_one₀ (by positivity)
    apply (div_le_one (by exact_mod_cast Fintype.card_pos)).mpr
    exact_mod_cast Fintype.card_pos (α := A)
  have hfirst (y : Y) (hy : good y) : avg (fun ω ↦ ∏ j, f j y ω)=p := by
    simp_rw [ha y hy]
    exact avg_independent_selections (c y) (hc y hy) (a y)
  have hsecond (yy : Y × Y) (hy : good₂ yy) :
      avg (fun ω ↦ (∏ j, f j yy.1 ω)*(∏ j, f j yy.2 ω))=p^2 := by
    simp_rw [ha yy.1 hy.1,ha yy.2 hy.2.1]
    exact avg_double_selections _ _ (hc _ hy.1) (hc _ hy.2.1) hy.2.2 _ _
  have hbad₂ : avg (fun yy ↦ if good₂ yy then 0 else 1)≤2*b+d :=
    bad_pair_avg_bound c good hb hd
  exact moments_from_good (fun y ω ↦ ∏ j, f j y ω) good good₂ hp hp1
    (fun y ω ↦ ⟨Finset.prod_nonneg (fun j _ ↦ (hf j y ω).1),
      Finset.prod_le_one₀ (fun j _ ↦ (hf j y ω).1) (fun j _ ↦ (hf j y ω).2)⟩)
    hfirst hsecond (by linarith) hbad₂

end ProductMoments
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

section ConditionalAverage
variable {K : Type uK} {V : Type uV} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]

end ConditionalAverage
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

section GoodRows
variable {K : Type uK} {V : Type uV} {J : Type uJ} {κ : Type uκ} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J]

attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Packing.rowsGoodDecidable
end GoodRows
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

section AveragedVariance
variable {K : Type uK} {V : Type uV} {J : Type uJ} {κ : Type uκ} {A : Type uA} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [Fintype V] [DecidableEq V]
  [Fintype J] [DecidableEq J] [Fintype κ] [DecidableEq κ]
  [Fintype A] [Nonempty A] [DecidableEq A]

end AveragedVariance
end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
open scoped BigOperators
open Finset


theorem solution.{uκ,uA,uJ,uY} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.selections_variance.{uκ,uA,uJ,uY} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.selections_variance.{uκ,uA,uJ,uY}
