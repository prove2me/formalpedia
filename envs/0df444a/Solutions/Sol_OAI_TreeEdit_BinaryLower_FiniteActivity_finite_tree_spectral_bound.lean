-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.FiniteActivity.finite_tree_spectral_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:20:15.211955+00:00
-- url     : https://prove2.me/submissions/0b6ffbfa-9ab4-42ae-811e-c9e06cb14aa4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteSpectralTree.lean:L21-L54
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.FiniteActivity.finite_tree_spectral_bound. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_FiniteActivity_dense_of_no_sparse
import Theorems.Thm_OAI_TreeEdit_BinaryLower_TreeDistortion_FiniteMass_finite_spectral_root_bound

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteActivityBridge ----
namespace OAI

/-!
# Finite indices for the sparse-activity obstruction

Internal nodes are indexed by their depth and finite sequence of child
indices. Absence of a sparse active node bounds the cardinality of active
leaves, which controls the Fourier mass.
-/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteActivity

open Classical

/-- For a root-active character that escapes every sparse-node test, the
number of active terminal vectors is at least the branching factor to the
height. -/
theorem character_dense_of_no_sparse {α G : Type*}
    [Fintype α] [AddCommGroup G]
    (w : List α → G) (b h : ℕ) (χ : AddChar G ℂ)
    (hroot : χ (w []) ≠ 1)
    (hno : ¬ ∃ v : InternalNode α h, characterSparse w b v χ) :
    (b : ℝ) ^ h ≤
      ((Finset.univ.filter fun f : Fin h → α => χ (w (List.ofFn f)) ≠ 1).card : ℝ) := by
  classical
  have hd := dense_of_no_sparse (fun p => χ (w p) ≠ 1) b h hroot hno
  exact_mod_cast hd

/-- Adapter to the actual cyclic coordinate generators used by the spectral
leaf tests. The only structural identity needed here is `w_leaf = e_leaf`. -/
theorem character_dense_of_leaf_generators {α G : Type*}
    [Fintype α] [AddCommGroup G]
    (w : List α → G) (b h : ℕ) (e : (Fin h → α) → G) (χ : AddChar G ℂ)
    (hgen : ∀ f : Fin h → α, w (List.ofFn f) = e f)
    (hroot : χ (w []) ≠ 1)
    (hno : ¬ ∃ v : InternalNode α h, characterSparse w b v χ) :
    (b : ℝ) ^ h ≤
      ((Finset.univ.filter fun f : Fin h → α => χ (e f) ≠ 1).card : ℝ) := by
  classical
  simpa only [hgen] using character_dense_of_no_sparse w b h χ hroot hno

/-- Exact sum of the reciprocal-subtree budgets over the finite internal-node
index. The result is independent of the branching width. -/
theorem internal_node_budget (m h : ℕ) (hm : m ≠ 0) (C : ℝ) :
    (∑ v : InternalNode (Fin m) h, C / (m : ℝ) ^ (v.1 : ℕ)) = h * C := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [Fintype.sum_sigma]
  have hlevel : ∀ j : Fin h,
      (∑ _f : Fin (j : ℕ) → Fin m, C / (m : ℝ) ^ (j : ℕ)) = C := by
    intro j
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
    rw [mul_comm, div_mul_cancel₀ _ (pow_ne_zero _ hm')]
  simp only [hlevel, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The leaf-coordinate edit budgets sum to exactly the word length. -/
theorem leaf_budget (m h : ℕ) (hm : m ≠ 0) (M : ℝ) :
    (∑ _f : Fin h → Fin m, M / (m : ℝ) ^ h) = M := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
  rw [mul_comm, div_mul_cancel₀ _ (pow_ne_zero _ hm')]

end TreeEdit.BinaryLower.FiniteActivity

end

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteSpectralTree ----
namespace OAI

/-!
# Finite-tree spectral obstruction

The sparse/dense counting and Fourier-mass estimates give the spectral
bound used in `prop:finite-lower` for the cyclic leaf coordinates and
cheap translations.
-/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteActivity

open Classical
open scoped BigOperators

/-- The complete sparse/dense spectral estimate on a finite tree. For the
manuscript instantiate `h=b=k`, `m=20*k`, and `C=(2*J/T)*M`. The conclusion
then reproduces `eq:finite-root-upper` before the final numerical estimate. -/
theorem finite_tree_spectral_bound {A σ : Type*}
    [AddCommGroup A] [Fintype A] [Fintype σ] [Nonempty σ]
    (m b h : ℕ) (hm : m ≠ 0) (hb : 0 < b)
    (w : List (Fin m) → A)
    (Q : (Fin h → Fin m) → ℕ) [∀ f, NeZero (Q f)]
    (φ : ∀ f, ZMod (Q f) →+ A)
    (hgen : ∀ f : Fin h → Fin m, w (List.ofFn f) = φ f 1)
    (H : AddChar A ℂ → ℝ) (hH : ∀ χ, 0 ≤ H χ)
    (shift : InternalNode (Fin m) h → σ → A) (M C : ℝ)
    (hleaf : ∀ f (z : ZMod (Q f)),
      (∑ χ, ‖1 - χ (φ f z)‖ ^ 2 * H χ) ≤ M / (m : ℝ) ^ h)
    (hdetect : ∀ v χ, characterSparse w b v χ →
      (Fintype.card σ : ℝ) ≤ ∑ s, ‖1 - χ (shift v s)‖ ^ 2)
    (hcost : ∀ v s,
      (∑ χ, ‖1 - χ (shift v s)‖ ^ 2 * H χ) ≤ C / (m : ℝ) ^ (v.1 : ℕ)) :
    (∑ χ : AddChar A ℂ, ‖1 - χ (w [])‖ ^ 2 * H χ) ≤
      4 * ((h : ℝ) * C + M / (2 * (b : ℝ) ^ h)) := by
  classical
  apply TreeEdit.BinaryLower.TreeDistortion.FiniteMass.finite_spectral_root_bound Q φ H (w [])
    (characterSparse w b) shift
    (fun v => C / (m : ℝ) ^ (v.1 : ℕ))
    (fun _f => M / (m : ℝ) ^ h) M ((h : ℝ) * C) ((b : ℝ) ^ h)
  · exact pow_pos (Nat.cast_pos.mpr hb) _
  · exact hH
  · intro χ hr hn
    exact character_dense_of_leaf_generators w b h (fun f => φ f 1) χ hgen hr hn
  · exact hleaf
  · exact le_of_eq (leaf_budget m h hm M)
  · exact hdetect
  · exact hcost
  · exact le_of_eq (internal_node_budget m h hm C)

end TreeEdit.BinaryLower.FiniteActivity

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.FiniteActivity
open Classical
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.FiniteActivity.finite_tree_spectral_bound := @_root_.OAI.TreeEdit.BinaryLower.FiniteActivity.finite_tree_spectral_bound
