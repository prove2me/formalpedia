-- Prove2me | solution 1 for OAI.FiniteCircle.expect_histDist_ofFn_ge
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:54:37.67079+00:00
-- url     : https://prove2.me/submissions/ca5e3166-59be-4b86-9c20-918b9826b034

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Histograms.lean:L201-L234
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.expect_histDist_ofFn_ge. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Lower
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Windows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Partitions
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Histograms
import Theorems.Thm_OAI_FiniteCircle_FiniteLaw_event_exists_le_sum

-- ---- from OAI.Combinatorics.FiniteCircle.Partitions ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem event_eq_expect (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P] :
    μ.event P = μ.expect (fun ω => if P ω then 1 else 0) := by
  classical
  unfold event expect
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : P ω <;> simp [h]

theorem expect_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    μ.expect f ≤ μ.expect g :=
  Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω))

theorem expect_smul (μ : FiniteLaw Ω) (a : ℝ) (f : Ω → ℝ) :
    μ.expect (fun ω => a * f ω) = a * μ.expect f := by
  simp only [expect, mul_left_comm _ a, Finset.mul_sum]

theorem event_compl (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.event (fun ω => ¬P ω) = 1 - μ.event P := by
  classical
  rw [← μ.total]
  unfold event
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : P ω <;> simp [h]

end FiniteLaw

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Histograms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem histDist_nonneg {X Y : Type*} [Fintype Y] (label : X → Y) (xs ys : List X) :
    0 ≤ histDist label xs ys := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem expect_histDist_ofFn_ge {X Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (μ : FiniteLaw Ω) (label : Ω → X → Y) {s : ℕ} (f g : Fin s → X)
    (p : ℝ) (hp : ∀ i j, μ.event (fun ω => label ω (f i) = label ω (g j)) ≤ p)
    (hsp : (s : ℝ)^2 * p ≤ 1 / 2) :
    (s : ℝ) ≤ μ.expect (fun ω => histDist (label ω) (List.ofFn f) (List.ofFn g)) := by
  classical
  let Collision := fun ω => ∃ ij : Fin s × Fin s, label ω (f ij.1) = label ω (g ij.2)
  have hc : μ.event Collision ≤ 1 / 2 := by
    calc
      _ ≤ ∑ ij : Fin s × Fin s, μ.event (fun ω => label ω (f ij.1) = label ω (g ij.2)) :=
        μ.event_exists_le_sum _
      _ ≤ ∑ _ij : Fin s × Fin s, p := Finset.sum_le_sum (fun ij _ => hp ij.1 ij.2)
      _ = (s : ℝ)^2 * p := by simp [sq, mul_assoc]
      _ ≤ _ := hsp
  have hn : 1 / 2 ≤ μ.event (fun ω => ¬Collision ω) := by rw [μ.event_compl]; linarith
  have hd : 2 * s * μ.event (fun ω => ¬Collision ω) ≤
      μ.expect (fun ω => histDist (label ω) (List.ofFn f) (List.ofFn g)) := by
    rw [FiniteLaw.event_eq_expect, ← μ.expect_smul]
    apply μ.expect_mono
    intro ω
    by_cases h : Collision ω
    · simp only [ite_eq_right (not_not_intro h), mul_zero]
      exact histDist_nonneg _ _ _
    · rw [ite_eq_left h, mul_one]
      have hdis : ∀ x ∈ List.ofFn f, ∀ y ∈ List.ofFn g, label ω x ≠ label ω y := by
        intro x hx y hy heq
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
        exact h ⟨(i,j), heq⟩
      rw [histDist_disjoint _ _ _ hdis]
      simp only [List.length_ofFn]
      linarith
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  nlinarith

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical


theorem solution : type_of% @_root_.OAI.FiniteCircle.expect_histDist_ofFn_ge := @_root_.OAI.FiniteCircle.expect_histDist_ofFn_ge
