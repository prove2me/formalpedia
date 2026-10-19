-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.moments_from_good
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:01:35.573359+00:00
-- url     : https://prove2.me/submissions/75ffabdb-861b-4e5a-a691-07f599e6dba1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Averages.lean:L156-L180
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.moments_from_good. The node keeps its source
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
lemma avg_sub (f g : Ω → ℝ) : avg (fun ω ↦ f ω-g ω)=avg f-avg g := by
  simp [avg,Finset.sum_sub_distrib,sub_div]
omit [Nonempty Ω] in
lemma avg_mul_const (f : Ω → ℝ) (c : ℝ) : avg (fun ω ↦ f ω*c)=avg f*c := by
  simp [avg,← Finset.sum_mul]; ring
omit [Nonempty Ω] in
lemma avg_const_mul (c : ℝ) (f : Ω → ℝ) : avg (fun ω ↦ c*f ω)=c*avg f := by
  simpa only [mul_comm c] using avg_mul_const f c
omit [Nonempty Ω] in
lemma avg_mono {f g : Ω → ℝ} (h : ∀ ω, f ω≤g ω) : avg f≤avg g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ ↦ h ω)) (Nat.cast_nonneg _)
lemma avg_nonneg {f : Ω → ℝ} (h : ∀ ω, 0≤f ω) : 0≤avg f := by
  simpa only [avg_const] using avg_mono h
omit [Nonempty Ω] in
lemma avg_abs {f : Ω → ℝ} : |avg f|≤avg (fun ω ↦ |f ω|) := by
  have hc : |(Fintype.card Ω : ℝ)|=(Fintype.card Ω : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
  rw [avg,abs_div,hc]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)
omit [Nonempty Ω] in
lemma avg_comm {Λ : Type uΛ} [Fintype Λ] [Nonempty Λ] (f : Ω → Λ → ℝ) :
    avg (fun ω ↦ avg (f ω))=avg (fun x ↦ avg (fun ω ↦ f ω x)) := by
  dsimp [avg]
  simp only [← Finset.sum_div]
  rw [Finset.sum_comm]
  ring

omit [Nonempty Ω] in
lemma avg_prod_type {Λ : Type uΛ} [Fintype Λ] [Nonempty Λ] (f : Ω × Λ → ℝ) :
    avg f = avg (fun ω ↦ avg (fun x ↦ f (ω,x))) := by
  simp only [avg,Fintype.card_prod,Nat.cast_mul,Fintype.sum_prod_type,← Finset.sum_div]
  ring

/-- Good configurations contribute exactly c; all bad configurations carry
only a bounded contribution. This is the uniform first/second moment input. -/
lemma avg_error_on_bad (f : Ω → ℝ) (good : Ω → Prop) [DecidablePred good]
    {c : ℝ} (hc : 0≤c) (hc1 : c≤1) (hf : ∀ ω, 0≤f ω ∧ f ω≤1)
    (he : ∀ ω, good ω → f ω=c) :
    |avg f-c| ≤ avg (fun ω ↦ if good ω then 0 else 1) := by
  rw [← avg_const (Ω := Ω) c,← avg_sub]
  exact avg_abs.trans (avg_mono (fun ω ↦ by
    by_cases h : good ω
    · simp [h,he ω h]
    · simp only [h,ite_false]
      rw [abs_le]
      constructor <;> linarith [(hf ω).1,(hf ω).2]))

lemma avg_square_error {Z : Ω → ℝ} {p a : ℝ} (hp : 0≤p) (hp1 : p≤1)
    (hmean : |avg Z-p|≤a) (hsecond : |avg (fun ω ↦ Z ω^2)-p^2|≤a) :
    avg (fun ω ↦ (Z ω-p)^2) ≤ 3*a := by
  have he : avg (fun ω ↦ (Z ω-p)^2) =
      avg (fun ω ↦ Z ω^2)-2*p*avg Z+p^2 := by
    calc
      _ = avg (fun ω ↦ Z ω^2-(2*p)*Z ω+p^2) := by congr 1; funext ω; ring
      _ = _ := by rw [avg_add,avg_sub,avg_const_mul,avg_const]
  rw [he]
  have ha : 0≤a := (abs_nonneg _).trans hmean
  have hm := (abs_le.mp hmean).1
  have hs := (abs_le.mp hsecond).2
  nlinarith

omit [Nonempty Ω] in
lemma avg_mul_avg {Λ : Type uΛ} [Fintype Λ] [Nonempty Λ]
    (f : Ω → ℝ) (g : Λ → ℝ) :
    avg f*avg g = avg (fun x : Ω × Λ ↦ f x.1*g x.2) := by
  rw [avg_prod_type]
  simp_rw [avg_const_mul,avg_mul_const]

omit [Nonempty Ω] in
lemma avg_square {Y : Type uY} [Fintype Y] [Nonempty Y] (f : Y → Ω → ℝ) :
    avg (fun ω ↦ (avg (fun y ↦ f y ω))^2) =
      avg (fun yy : Y × Y ↦ avg (fun ω ↦ f yy.1 ω*f yy.2 ω)) := by
  simp_rw [pow_two,avg_mul_avg]
  exact avg_comm _

/-- Unconditional moments suffice: pruning all atypical candidate centers
only enlarges the deleted set, so no conditional-probability axiom is used. -/
lemma moments_from_good {Y : Type uY} [Fintype Y] [Nonempty Y]
    (f : Y → Ω → ℝ) (good : Y → Prop) (good₂ : Y × Y → Prop)
    [DecidablePred good] [DecidablePred good₂] {p a : ℝ}
    (hp : 0≤p) (hp1 : p≤1) (hf : ∀ y ω, 0≤f y ω ∧ f y ω≤1)
    (hfirst : ∀ y, good y → avg (f y)=p)
    (hsecond : ∀ yy, good₂ yy → avg (fun ω ↦ f yy.1 ω*f yy.2 ω)=p^2)
    (hbad : avg (fun y ↦ if good y then 0 else 1)≤a)
    (hbad₂ : avg (fun yy ↦ if good₂ yy then 0 else 1)≤a) :
    avg (fun ω ↦ (avg (fun y ↦ f y ω)-p)^2) ≤ 3*a := by
  have hb (y) : 0≤avg (f y) ∧ avg (f y)≤1 :=
    ⟨avg_nonneg (fun ω ↦ (hf y ω).1),by
      rw [← avg_const (Ω := Ω) 1]; exact avg_mono (fun ω ↦ (hf y ω).2)⟩
  have hb₂ (yy : Y × Y) : 0≤avg (fun ω ↦ f yy.1 ω*f yy.2 ω) ∧
      avg (fun ω ↦ f yy.1 ω*f yy.2 ω)≤1 := by
    constructor
    · exact avg_nonneg (fun ω ↦ mul_nonneg (hf _ _).1 (hf _ _).1)
    · rw [← avg_const (Ω := Ω) 1]
      exact avg_mono (fun ω ↦ (mul_le_of_le_one_left (hf _ _).1 (hf _ _).2).trans (hf _ _).2)
  apply avg_square_error hp hp1
  · rw [avg_comm]
    exact (avg_error_on_bad _ good hp hp1 hb hfirst).trans hbad
  · rw [avg_square]
    exact (avg_error_on_bad _ good₂ (sq_nonneg _) (by nlinarith) hb₂ hsecond).trans hbad₂

end Average
end
end Packing
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
open scoped BigOperators
open Finset


theorem solution.{uΩ,uY} : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.moments_from_good.{uΩ,uY} := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.moments_from_good.{uΩ,uY}
