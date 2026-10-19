-- Prove2me | solution 1 for OAI.FiniteCircle.expect_histDist_ofFn_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:51:51.28667+00:00
-- url     : https://prove2.me/submissions/3c5bb73d-71a6-491b-bebb-358f2b0dd6f6

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Histograms.lean:L181-L199
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.expect_histDist_ofFn_le. The node keeps its source
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

theorem expect_sum {ι : Type*} (μ : FiniteLaw Ω) (s : Finset ι) (f : ι → Ω → ℝ) :
    μ.expect (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, μ.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

end FiniteLaw

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Histograms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem histDist_append_le {X Y : Type*} [Fintype Y] (label : X → Y)
    (xs ys us vs : List X) :
    histDist label (xs ++ us) (ys ++ vs) ≤ histDist label xs ys + histDist label us vs := by
  unfold histDist
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y _
  simp only [histogram_append]
  convert abs_add_le (histogram label xs y - histogram label ys y)
    (histogram label us y - histogram label vs y) using 1
  congr 1
  ring

theorem histDist_cons_le {X Y : Type*} [Fintype Y] [DecidableEq Y] (label : X → Y) (x y : X) (xs ys : List X) :
    histDist label (x :: xs) (y :: ys) ≤
      (if label x = label y then 0 else 2) + histDist label xs ys := by
  classical
  simpa only [List.singleton_append, histDist_singleton] using histDist_append_le label [x] [y] xs ys

theorem histDist_ofFn_le {X Y : Type*} [Fintype Y] [DecidableEq Y]
    (label : X → Y) {s : ℕ} (f g : Fin s → X) :
    histDist label (List.ofFn f) (List.ofFn g) ≤
      2 * ∑ i, (if label (f i) = label (g i) then (0 : ℝ) else 1) := by
  induction s with
  | zero => simp [histDist]
  | succ s ih =>
    rw [List.ofFn_succ, List.ofFn_succ, Fin.sum_univ_succ, mul_add]
    refine (histDist_cons_le _ _ _ _ _).trans (add_le_add ?_ (ih _ _))
    split <;> norm_num

theorem expect_histDist_ofFn_le {X Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (μ : FiniteLaw Ω) (label : Ω → X → Y) {s : ℕ} (f g : Fin s → X)
    (p : ℝ) (hp : ∀ i, μ.event (fun ω => label ω (f i) ≠ label ω (g i)) ≤ p) :
    μ.expect (fun ω => histDist (label ω) (List.ofFn f) (List.ofFn g)) ≤ 2 * s * p := by
  classical
  calc
    _ ≤ μ.expect (fun ω => 2 * ∑ i, if label ω (f i) = label ω (g i) then 0 else 1) :=
      μ.expect_mono (fun _ => histDist_ofFn_le _ _ _)
    _ = 2 * ∑ i, μ.event (fun ω => label ω (f i) ≠ label ω (g i)) := by
      rw [μ.expect_smul, μ.expect_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [FiniteLaw.event_eq_expect]
      congr 1
      funext ω
      split <;> simp_all
    _ ≤ 2 * ∑ _i : Fin s, p := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hp i)) (by norm_num)
    _ = _ := by simp; ring

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical


theorem solution : type_of% @_root_.OAI.FiniteCircle.expect_histDist_ofFn_le := @_root_.OAI.FiniteCircle.expect_histDist_ofFn_le
