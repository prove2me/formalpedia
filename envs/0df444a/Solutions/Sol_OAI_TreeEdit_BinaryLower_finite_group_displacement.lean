-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.finite_group_displacement
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:33:39.185091+00:00
-- url     : https://prove2.me/submissions/0e8ae404-aa64-400d-a8ea-1120c22b02b1

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteDisplacement.lean:L74-L95
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.finite_group_displacement. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_finite_fourier_of_cut_expansions
import Theorems.Thm_OAI_TreeEdit_BinaryLower_l1_bool_cut_representation

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteFourier ----
namespace OAI

/-!
# Fourier identities for the finite-tree obstruction

The scalar Fourier identities establish `lem:finite-fourier`.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
open Finset RCLike

namespace TreeEdit.BinaryLower.FiniteFourier

variable {A : Type*} [AddCommGroup A] [Fintype A]

omit [AddCommGroup A] in
lemma wInner_sum_left {ι : Type*} (s : Finset ι) (w : A → ℝ)
    (f : ι → A → ℂ) (g : A → ℂ) :
    RCLike.wInner (𝕜 := ℂ) w (∑ i ∈ s, f i) g =
      ∑ i ∈ s, RCLike.wInner (𝕜 := ℂ) w (f i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, RCLike.wInner_add_left, ih]

omit [AddCommGroup A] in
lemma wInner_sum_right {ι : Type*} (s : Finset ι) (w : A → ℝ)
    (f : A → ℂ) (g : ι → A → ℂ) :
    RCLike.wInner (𝕜 := ℂ) w f (∑ i ∈ s, g i) =
      ∑ i ∈ s, RCLike.wInner (𝕜 := ℂ) w f (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, RCLike.wInner_add_right, ih]

lemma coefficient_eq_repr (f : A → ℂ) (χ : AddChar A ℂ) :
    coefficient f χ = (AddChar.complexBasis A).repr f χ := by
  classical
  unfold coefficient
  conv_lhs => arg 3; rw [← (AddChar.complexBasis A).sum_repr f]
  rw [wInner_sum_right]
  simp [RCLike.wInner_smul_right, AddChar.wInner_cWeight_eq_boole]

lemma expansion (f : A → ℂ) :
    (∑ χ : AddChar A ℂ, coefficient f χ • (χ : A → ℂ)) = f := by
  simp_rw [coefficient_eq_repr, ← AddChar.complexBasis_apply]
  exact (AddChar.complexBasis A).sum_repr f

lemma parseval_complex (f : A → ℂ) :
    RCLike.wInner RCLike.cWeight f f =
      ∑ χ : AddChar A ℂ, star (coefficient f χ) * coefficient f χ := by
  conv_lhs => arg 2; rw [← expansion f]
  rw [wInner_sum_left]
  simp only [RCLike.wInner_smul_left, smul_eq_mul, coefficient]

lemma parseval (f : A → ℂ) :
    (∑ x : A, ‖f x‖ ^ 2) / Fintype.card A =
      ∑ χ : AddChar A ℂ, ‖coefficient f χ‖ ^ 2 := by
  have h := congrArg Complex.re (parseval_complex f)
  simpa [RCLike.wInner_cWeight_eq_expect, Fintype.expect_eq_sum_div_card,
    RCLike.inner_apply, Complex.div_ofReal_re,
    ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    ← Complex.ofReal_pow] using h

lemma coefficient_sum {ι : Type*} (s : Finset ι) (f : ι → A → ℂ)
    (χ : AddChar A ℂ) :
    coefficient (∑ i ∈ s, f i) χ = ∑ i ∈ s, coefficient (f i) χ := by
  exact wInner_sum_right s _ _ _

lemma coefficient_smul (a : ℂ) (f : A → ℂ) (χ : AddChar A ℂ) :
    coefficient (a • f) χ = a * coefficient f χ := by
  exact RCLike.wInner_smul_right a _ _ _

lemma coefficient_char (ψ χ : AddChar A ℂ) :
    coefficient (ψ : A → ℂ) χ = if χ = ψ then 1 else 0 :=
  AddChar.wInner_cWeight_eq_boole χ ψ

lemma displacement_expansion (f : A → ℂ) (z : A) :
    (fun x => f (x + z) - f x) =
      ∑ χ : AddChar A ℂ, ((χ z - 1) * coefficient f χ) • (χ : A → ℂ) := by
  funext x
  have h₁ := congrFun (expansion f) (x + z)
  have h₂ := congrFun (expansion f) x
  rw [← h₁, ← h₂]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro χ _
  rw [AddChar.map_add_eq_mul]
  ring

lemma coefficient_displacement (f : A → ℂ) (z : A) (χ : AddChar A ℂ) :
    coefficient (fun x => f (x + z) - f x) χ =
      (χ z - 1) * coefficient f χ := by
  classical
  rw [displacement_expansion, coefficient_sum]
  simp [coefficient_smul, coefficient_char]

/-- Parseval for the displacement by a fixed group element. -/
lemma displacement_parseval (f : A → ℂ) (z : A) :
    (∑ x : A, ‖f (x + z) - f x‖ ^ 2) / Fintype.card A =
      ∑ χ : AddChar A ℂ, ‖1 - χ z‖ ^ 2 * ‖coefficient f χ‖ ^ 2 := by
  rw [parseval]
  apply Finset.sum_congr rfl
  intro χ _
  rw [coefficient_displacement, norm_mul, mul_pow, norm_sub_rev]

/-- Indicator differences have equal absolute value and squared complex norm. -/
lemma indicator_difference (u v : ℝ) (hu : u = 0 ∨ u = 1) (hv : v = 0 ∨ v = 1) :
    |u - v| = ‖(u : ℂ) - (v : ℂ)‖ ^ 2 := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> norm_num

/-- The identity for one zero-one valued cut. -/
lemma indicator_displacement (U : A → ℝ) (hU : ∀ x, U x = 0 ∨ U x = 1) (z : A) :
    (∑ x : A, |U (x + z) - U x|) / Fintype.card A =
      ∑ χ : AddChar A ℂ,
        ‖1 - χ z‖ ^ 2 * ‖coefficient (fun x => (U x : ℂ)) χ‖ ^ 2 := by
  simp_rw [indicator_difference _ _ (hU _) (hU _)]
  exact displacement_parseval (fun x => (U x : ℂ)) z

end TreeEdit.BinaryLower.FiniteFourier

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

/-- The finite-group displacement lemma, for the actual full ℓ₁ sequence
space. Uniform probability averaging is denoted by `𝔼`. -/
theorem finite_group_displacement {A : Type*} [AddCommGroup A] [Fintype A]
    (F : A → RealL1) :
    ∃ H : AddChar A ℂ → ℝ, (∀ χ, 0 ≤ H χ) ∧
      ∀ z, (𝔼 x, ‖F (x + z) - F x‖) =
        ∑ χ : AddChar A ℂ, ‖1 - χ z‖ ^ 2 * H χ := by
  classical
  obtain ⟨a, ha, hrep, -, -, -⟩ := l1_bool_cut_representation F
  apply finite_fourier_of_cut_expansions F a
    (fun C x => BoolCuts.bit (C x))
    (fun C χ => ‖FiniteFourier.coefficient (fun x =>
      (BoolCuts.bit (C x) : ℂ)) χ‖ ^ 2) ha
  · intro C χ
    exact sq_nonneg _
  · exact hrep
  · intro C z
    have hC : ∀ x, BoolCuts.bit (C x) = 0 ∨ BoolCuts.bit (C x) = 1 := by
      intro x
      cases C x <;> simp [BoolCuts.bit]
    simpa only [Fintype.expect_eq_sum_div_card] using
      FiniteFourier.indicator_displacement (fun x => BoolCuts.bit (C x)) hC z

end TreeEdit.BinaryLower

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.finite_group_displacement := @_root_.OAI.TreeEdit.BinaryLower.finite_group_displacement
