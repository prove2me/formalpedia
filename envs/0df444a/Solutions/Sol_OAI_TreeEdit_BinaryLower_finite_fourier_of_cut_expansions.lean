-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.finite_fourier_of_cut_expansions
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:22:04.87785+00:00
-- url     : https://prove2.me/submissions/f298d55d-7d55-4b0a-9c94-814a174d29d2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteFourierAssembly.lean:L41-L75
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.finite_fourier_of_cut_expansions. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteFourierAssembly ----
namespace OAI

/-!
# Assembly of the finite-group displacement identity

Summing finite cut representations and the Parseval identities for cut
indicators gives the finite-group displacement identity.
-/

noncomputable section

open scoped BigOperators

namespace TreeEdit.BinaryLower

/-- Summing nonnegative spectral weights with nonnegative cut coefficients
preserves nonnegativity. -/
theorem cut_spectral_weight_nonneg {C K : Type*} [Fintype C]
    (a : C → ℝ) (b : C → K → ℝ)
    (ha : ∀ c, 0 ≤ a c) (hb : ∀ c k, 0 ≤ b c k) (k : K) :
    0 ≤ ∑ c, a c * b c k := by
  exact Finset.sum_nonneg fun c _ => mul_nonneg (ha c) (hb c k)

/-- Interchange a finite cut sum and a finite spectral sum. -/
theorem sum_cut_spectral_weights {C K : Type*} [Fintype C] [Fintype K]
    (a : C → ℝ) (b : C → K → ℝ) (multiplier : K → ℝ) :
    (∑ c, a c * ∑ k, multiplier k * b c k) =
      ∑ k, multiplier k * ∑ c, a c * b c k := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- A finite cut expansion together with the spectral expansion of each cut
implies the averaged displacement representation.  Neither injectivity of
`F` nor nontriviality of the individual cuts is needed. -/
theorem finite_fourier_of_cut_expansions
    {A C E : Type*} [AddCommGroup A] [Fintype A] [Fintype C]
    [NormedAddCommGroup E]
    (F : A → E) (a : C → ℝ) (U : C → A → ℝ)
    (b : C → AddChar A ℂ → ℝ)
    (ha : ∀ c, 0 ≤ a c) (hb : ∀ c χ, 0 ≤ b c χ)
    (hcut : ∀ x y, ‖F x - F y‖ = ∑ c, a c * |U c x - U c y|)
    (hfourier : ∀ c z,
      (𝔼 x, |U c (x + z) - U c x|) =
        ∑ χ : AddChar A ℂ, ‖1 - χ z‖ ^ 2 * b c χ) :
    ∃ H : AddChar A ℂ → ℝ, (∀ χ, 0 ≤ H χ) ∧
      ∀ z, (𝔼 x, ‖F (x + z) - F x‖) =
        ∑ χ : AddChar A ℂ, ‖1 - χ z‖ ^ 2 * H χ := by
  classical
  refine ⟨fun χ => ∑ c, a c * b c χ,
    cut_spectral_weight_nonneg a b ha hb, ?_⟩
  intro z
  calc
    (𝔼 x, ‖F (x + z) - F x‖) =
        𝔼 x, ∑ c, a c * |U c (x + z) - U c x| := by
          apply Finset.expect_congr rfl
          intro x _
          exact hcut (x + z) x
    _ = ∑ c, a c * (𝔼 x, |U c (x + z) - U c x|) := by
          rw [Finset.expect_sum_comm]
          apply Finset.sum_congr rfl
          intro c _
          exact (Finset.mul_expect _ _ _).symm
    _ = ∑ c, a c * ∑ χ : AddChar A ℂ, ‖1 - χ z‖ ^ 2 * b c χ := by
          simp_rw [hfourier]
    _ = ∑ χ : AddChar A ℂ, ‖1 - χ z‖ ^ 2 * ∑ c, a c * b c χ :=
          sum_cut_spectral_weights a b (fun χ => ‖1 - χ z‖ ^ 2)

end TreeEdit.BinaryLower

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.finite_fourier_of_cut_expansions := @_root_.OAI.TreeEdit.BinaryLower.finite_fourier_of_cut_expansions
