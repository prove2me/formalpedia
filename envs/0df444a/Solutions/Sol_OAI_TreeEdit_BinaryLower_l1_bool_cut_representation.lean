-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.l1_bool_cut_representation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:31:59.561575+00:00
-- url     : https://prove2.me/submissions/4db935fc-360c-4fcd-8ff1-1796250edd34

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteDisplacement.lean:L26-L72
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.l1_bool_cut_representation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool
import Theorems.Thm_OAI_TreeEdit_BinaryLower_BoolCuts_scalar_cut_representation
import Theorems.Thm_OAI_TreeEdit_BinaryLower_CutAggregation_aggregate
import Theorems.Thm_OAI_TreeEdit_BinaryLower_CutAggregation_cut_mass_bound

-- ---- from OAI.Combinatorics.BinaryEdit.CutAggregation ----
namespace OAI

/-! Countable-coordinate aggregation in the finite cut representation. -/

noncomputable section

namespace TreeEdit.BinaryLower.CutAggregation

universe u v

/-- Countable scalar decompositions yield a finite cut representation with bounded total weight. -/
theorem aggregate_with_mass_bound {S : Type u} {C : Type v}
    [Fintype S] [Fintype C]
    (F : S → TreeEdit.RealL1) (U : C → S → ℝ) (a : ℕ → C → ℝ)
    (ha : ∀ n c, 0 ≤ a n c)
    (hcut : ∀ c, (∀ n, a n c = 0) ∨ ∃ x y, |U c x - U c y| = 1)
    (hrep : ∀ n x y,
      |F x n - F y n| = ∑ c, a n c * |U c x - U c y|) :
    ∃ A : C → ℝ, (∀ c, 0 ≤ A c) ∧
      (∀ c, A c = ∑' n, a n c) ∧
      (∀ x y, ‖F x - F y‖ = ∑ c, A c * |U c x - U c y|) ∧
      (∑ c, A c ≤ (∑ p : S × S, ‖F p.1 - F p.2‖) / 2) := by
  obtain ⟨A, hA, hsum, hrepr⟩ := aggregate F U a ha hcut hrep
  refine ⟨A, hA, hsum, hrepr, cut_mass_bound F U A hA ?_ hrepr⟩
  intro c
  rcases hcut c with hz | hnontrivial
  · left
    simp [hsum, hz]
  · exact Or.inr hnontrivial

end TreeEdit.BinaryLower.CutAggregation

end

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteDisplacement ----
namespace OAI

/-!
# Finite-group displacement for arbitrary maps to ℓ₁

The finite-group displacement identity `lem:finite-fourier` holds for maps
from any finite abelian group into `TreeEdit.RealL1`, the full space of
absolutely summable real sequences. No injectivity or finite-support
assumption is needed.

The proof combines finite scalar cuts, summable-coordinate aggregation,
Parseval's identity and finite nonnegative summation.
-/

noncomputable section

open scoped BigOperators

namespace TreeEdit.BinaryLower

/-- Concrete finite-cut representation of any finite family of absolutely
summable real sequences. The two constant cuts have zero weight. The final
bound is the half ordered-pair form of the finite total-mass estimate. -/
theorem l1_bool_cut_representation {S : Type*} [Fintype S] [DecidableEq S]
    (F : S → RealL1) :
    ∃ a : (S → Bool) → ℝ, (∀ C, 0 ≤ a C) ∧
      (∀ x y, ‖F x - F y‖ = ∑ C, a C * BoolCuts.cutDistance C x y) ∧
      a (fun _ => false) = 0 ∧ a (fun _ => true) = 0 ∧
      (∑ C, a C) ≤ (∑ p : S × S, ‖F p.1 - F p.2‖) / 2 := by
  classical
  choose a ha hrep hfalse htrue using
    (fun n : ℕ => BoolCuts.scalar_cut_representation (fun x => F x n))
  have hcut : ∀ C : S → Bool, (∀ n, a n C = 0) ∨
      ∃ x y, |BoolCuts.bit (C x) - BoolCuts.bit (C y)| = 1 := by
    intro C
    by_cases hf : C = fun _ => false
    · subst C
      exact Or.inl hfalse
    by_cases ht : C = fun _ => true
    · subst C
      exact Or.inl htrue
    right
    have hx : ∃ x, C x = true := by
      by_contra h
      push Not at h
      apply hf
      funext x
      cases hc : C x with
      | false => rfl
      | true => exact False.elim (h x hc)
    have hy : ∃ y, C y = false := by
      by_contra h
      push Not at h
      apply ht
      funext y
      cases hc : C y with
      | false => exact False.elim (h y hc)
      | true => rfl
    obtain ⟨x, hx⟩ := hx
    obtain ⟨y, hy⟩ := hy
    exact ⟨x, y, by simp [hx, hy, BoolCuts.bit]⟩
  obtain ⟨A, hA, hsum, hARep, hmass⟩ :=
    CutAggregation.aggregate_with_mass_bound F
      (fun (C : S → Bool) (x : S) => BoolCuts.bit (C x)) a ha hcut hrep
  refine ⟨A, hA, hARep, ?_, ?_, hmass⟩
  · simp [hsum, hfalse]
  · simp [hsum, htrue]

end TreeEdit.BinaryLower

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.l1_bool_cut_representation := @_root_.OAI.TreeEdit.BinaryLower.l1_bool_cut_representation
