-- Prove2me | solution 1 for OAI.FiniteCircle.FiniteLaw.event_exists_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:47:30.796055+00:00
-- url     : https://prove2.me/submissions/cc244e8d-33e3-4564-b645-413c3b02b5b9

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Partitions.lean:L97-L110
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.FiniteLaw.event_exists_le_sum. The node keeps its source
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

-- ---- from OAI.Combinatorics.FiniteCircle.Partitions ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

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

theorem expect_sum {ι : Type*} (μ : FiniteLaw Ω) (s : Finset ι) (f : ι → Ω → ℝ) :
    μ.expect (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, μ.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem event_exists_le_sum {ι : Type*} [Fintype ι] (μ : FiniteLaw Ω) (P : ι → Ω → Prop) :
    μ.event (fun ω => ∃ i, P i ω) ≤ ∑ i, μ.event (P i) := by
  classical
  simp only [event_eq_expect]
  rw [← μ.expect_sum]
  apply μ.expect_mono
  intro ω
  by_cases h : ∃ i, P i ω
  · obtain ⟨i, hi⟩ := h
    rw [ite_eq_left ⟨i, hi⟩]
    exact (by simpa only [ite_eq_left hi] using
      (Finset.single_le_sum (f := fun j : ι => if P j ω then (1 : ℝ) else 0)
        (fun j _ => by split <;> norm_num) (Finset.mem_univ i)))
  · simp [show ∀ i, ¬ P i ω from fun i hi => h ⟨i, hi⟩]
end FiniteLaw

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle OAI.FiniteCircle.FiniteLaw
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical


theorem solution : type_of% @_root_.OAI.FiniteCircle.FiniteLaw.event_exists_le_sum := @_root_.OAI.FiniteCircle.FiniteLaw.event_exists_le_sum
