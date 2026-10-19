-- Prove2me | solution 2 for OAI.FiniteResampling.Transition.iterates_tendsto_constant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:34:59.433999+00:00
-- url     : https://prove2.me/submissions/6bf7f000-2b2b-435a-ad65-efd554ef9863

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Resampling.lean:L97-L149
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteResampling.Transition.iterates_tendsto_constant. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Theorems.Thm_OAI_FiniteResampling_Transition_common_atom_bounds

-- ---- from OAI.Probability.CriticalZ3.Resampling ----
namespace OAI

universe uI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
open scoped ENNReal

open scoped BigOperators Matrix
open Filter

namespace FiniteResampling
variable {I : Type uI} [Fintype I] [Nonempty I]

theorem lower_le (f : I → ℝ) (i : I) : lower f ≤ f i :=
  Finset.inf'_le f (Finset.mem_univ i)
theorem le_upper (f : I → ℝ) (i : I) : f i ≤ upper f :=
  Finset.le_sup' f (Finset.mem_univ i)
theorem le_lower {f : I → ℝ} {a : ℝ} (h : ∀ i, a ≤ f i) : a ≤ lower f :=
  Finset.le_inf' Finset.univ_nonempty f (fun i _ => h i)
theorem upper_le {f : I → ℝ} {a : ℝ} (h : ∀ i, f i ≤ a) : upper f ≤ a :=
  Finset.sup'_le Finset.univ_nonempty f (fun i _ => h i)
theorem lower_le_upper (f : I → ℝ) : lower f ≤ upper f := by
  obtain ⟨i⟩ := ‹Nonempty I›
  exact (lower_le f i).trans (le_upper f i)

namespace Transition
variable (K : Transition I)
omit [Nonempty I] in
theorem act_const (a : ℝ) (i : I) : K.act (fun _ => a) i = a := by
  simp [act, ← Finset.sum_mul, K.total]

omit [Nonempty I] in
theorem act_mono {f g : I → ℝ} (h : f ≤ g) : K.act f ≤ K.act g := by
  intro i
  exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h j) (K.nonneg i j))

theorem lower_le_act (f : I → ℝ) (i : I) : lower f ≤ K.act f i := by
  rw [← K.act_const (lower f) i]
  exact K.act_mono (fun j => lower_le f j) i

theorem act_le_upper (f : I → ℝ) (i : I) : K.act f i ≤ upper f := by
  rw [← K.act_const (upper f) i]
  exact K.act_mono (fun j => le_upper f j) i

theorem lower_le_lower_act (f : I → ℝ) : lower f ≤ lower (K.act f) :=
  le_lower (K.lower_le_act f)

theorem upper_act_le_upper (f : I → ℝ) : upper (K.act f) ≤ upper f :=
  upper_le (K.act_le_upper f)

theorem oscillation_contract (z : I) (a : ℝ) (ha : ∀ i, a ≤ K.weight i z)
    (f : I → ℝ) :
    upper (K.act f) - lower (K.act f) ≤ (1-a) * (upper f-lower f) := by
  have hl := le_lower (fun i => (K.common_atom_bounds z a ha f i).1)
  have hu := upper_le (fun i => (K.common_atom_bounds z a ha f i).2)
  nlinarith

/-- All finite transition iterates converge to a constant when every row shares
one positive atom. Zero-probability states are permitted and not discarded. -/
theorem iterates_tendsto_constant (z : I) (a : ℝ) (ha0 : 0 < a) (ha1 : a ≤ 1)
    (ha : ∀ i, a ≤ K.weight i z) (f : I → ℝ) :
    ∃ c : ℝ, lower f ≤ c ∧ c ≤ upper f ∧
      ∀ i, Tendsto (fun n : ℕ => ((K.act)^[n] f) i) atTop (nhds c) := by
  let g : ℕ → I → ℝ := fun n => (K.act)^[n] f
  have hstep (n : ℕ) : g (n+1) = K.act (g n) := by
    exact Function.iterate_succ_apply' _ _ _
  have hl : Monotone (fun n => lower (g n)) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hstep]
    exact K.lower_le_lower_act _
  have hu : Antitone (fun n => upper (g n)) := by
    apply antitone_nat_of_succ_le
    intro n
    rw [hstep]
    exact K.upper_act_le_upper _
  have hbb : ∀ n, lower (g n) ≤ upper f := by
    intro n
    exact (lower_le_upper _).trans (hu (Nat.zero_le n))
  have hbdd : BddAbove (Set.range (fun n => lower (g n))) := by
    exact ⟨upper f, fun _ ⟨n, hn⟩ => hn ▸ hbb n⟩
  have hdelta : ∀ n, upper (g n)-lower (g n) ≤
      (1-a)^n * (upper f-lower f) := by
    intro n
    induction n with
    | zero => simp [g]
    | succ n ih =>
      calc
        upper (g (n+1))-lower (g (n+1)) ≤ (1-a) * (upper (g n)-lower (g n)) := by
          rw [hstep]
          exact K.oscillation_contract z a ha _
        _ ≤ (1-a) * ((1-a)^n * (upper f-lower f)) :=
          mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr ha1)
        _ = (1-a)^(n+1) * (upper f-lower f) := by ring
  have hdlim : Tendsto (fun n => upper (g n)-lower (g n)) atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun n => sub_nonneg.mpr (lower_le_upper _)))
      (Filter.Eventually.of_forall hdelta)
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr ha1)
      (by linarith : 1-a < 1)).mul_const (upper f-lower f)
  let c := ⨆ n, lower (g n)
  have hllim : Tendsto (fun n => lower (g n)) atTop (nhds c) :=
    tendsto_atTop_ciSup hl hbdd
  have hulim : Tendsto (fun n => upper (g n)) atTop (nhds c) := by
    simpa only [add_sub_cancel, add_zero] using hllim.add hdlim
  refine ⟨c, ?_, ?_, ?_⟩
  · exact le_ciSup hbdd 0
  · exact ciSup_le hbb
  · intro i
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hllim hulim
      (fun n => lower_le (g n) i) (fun n => le_upper (g n) i)

end Transition
end FiniteResampling

end OAI

-- ---- platform node ----
open OAI OAI.FiniteResampling OAI.FiniteResampling.Transition
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
open scoped ENNReal
open scoped BigOperators Matrix
open Filter


theorem solution.{uI} : type_of% @_root_.OAI.FiniteResampling.Transition.iterates_tendsto_constant.{uI} := @_root_.OAI.FiniteResampling.Transition.iterates_tendsto_constant.{uI}
