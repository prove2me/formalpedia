-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.fixed_length_binary_conversion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:30:17.52732+00:00
-- url     : https://prove2.me/submissions/1fe6017b-b801-4263-b8e4-5d4bfc6d040d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FixedLengthBinaryConversion.lean:L15-L46
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.fixed_length_binary_conversion. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CheapTranslations
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Distortion
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ParameterImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteParameters
import Definitions.Def_OAI_Combinatorics_BinaryEdit_EncodedImage
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFamilyTransfer
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeNumerics
import Definitions.Def_OAI_Combinatorics_BinaryEdit_RandomMatching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentMatchingCount
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeUnionBound
import Definitions.Def_OAI_Combinatorics_BinaryEdit_SegmentCode
import Definitions.Def_OAI_Combinatorics_BinaryEdit_CodeAdditive
import Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSpanBudget
import Definitions.Def_OAI_Combinatorics_BinaryEdit_MatchingSegments
import Definitions.Def_OAI_Combinatorics_BinaryEdit_UnequalSegments
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Code_additive_of_unequal_matching_bound
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Code_block_pair_bad_count_le
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Code_block_pair_charge_of_segment_separation
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Code_code_union_bound_lt_one
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Code_encoded_block_segment_separation
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Code_eventually_short_pair_error
import Theorems.Thm_OAI_TreeEdit_BinaryLower_EditStep_common_subsequence
import Theorems.Thm_OAI_TreeEdit_BinaryLower_SegmentCode_SegmentSeparated_lcs_le
import Theorems.Thm_OAI_TreeEdit_BinaryLower_SegmentCode_exists_segmentSeparated
import Theorems.Thm_OAI_TreeEdit_BinaryLower_common_sublist_lower_bound

-- ---- from OAI.Combinatorics.TreeEdit.EditMetric ----
namespace OAI

namespace TreeEdit

universe u v

namespace EditStep

variable {α : Type u} {x y : List α}

protected theorem append_left (h : EditStep x y) (p : List α) :
    EditStep (p ++ x) (p ++ y) := by
  cases h with
  | insert q r a => simpa [List.append_assoc] using EditStep.insert (p ++ q) r a
  | delete q r a => simpa [List.append_assoc] using EditStep.delete (p ++ q) r a
  | substitute q r a b =>
      simpa [List.append_assoc] using EditStep.substitute (p ++ q) r a b

protected theorem append_right (h : EditStep x y) (r : List α) :
    EditStep (x ++ r) (y ++ r) := by
  cases h with
  | insert p q a => simpa [List.append_assoc] using EditStep.insert p (q ++ r) a
  | delete p q a => simpa [List.append_assoc] using EditStep.delete p (q ++ r) a
  | substitute p q a b =>
      simpa [List.append_assoc] using EditStep.substitute p (q ++ r) a b

end EditStep

namespace EditScript

variable {α : Type u} {x y z : List α} {m n : ℕ}

protected theorem append_left (h : EditScript x y n) (p : List α) :
    EditScript (p ++ x) (p ++ y) n := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.append_left p) ih

protected theorem append_right (h : EditScript x y n) (p : List α) :
    EditScript (x ++ p) (y ++ p) n := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.append_right p) ih

end EditScript

variable {α : Type u} {x y z : List α}

theorem sublist_script (h : z.Sublist x) : EditScript x z (x.length - z.length) := by
  induction h with
  | slnil => exact .nil []
  | @cons l₁ l₂ a h ih =>
      have hl := h.length_le
      have he : (a :: l₂).length - l₁.length = (l₂.length - l₁.length) + 1 := by
        simp only [List.length_cons]; omega
      rw [he]
      exact .cons (.delete [] l₂ a) ih
  | cons_cons a h ih =>
      simpa using ih.append_left [a]

theorem ed_le_deficits (x y : List α) :
    ed x y ≤ (x.length - lcs x y) + (y.length - lcs x y) := by
  obtain ⟨z, hx, hy, hz⟩ := exists_lcs x y
  simpa [hz] using ed_le_of_script ((sublist_script hx).trans (sublist_script hy).symm)

theorem substitution_script (h : x.length = y.length) : EditScript x y x.length := by
  induction x generalizing y with
  | nil =>
      have : y = [] := List.length_eq_zero_iff.mp h.symm
      subst y; exact .nil []
  | cons a x ih =>
      cases y with
      | nil => simp at h
      | cons b y =>
          have hh : x.length = y.length := by simpa using h
          exact .cons (.substitute [] x a b) (by simpa using (ih hh).append_left [b])

theorem encode_step {P : ℕ} {β : Type v} (c : α → Word β P) (h : EditStep x y) :
    EditScript (encode c x) (encode c y) P := by
  cases h with
  | insert p q a =>
      simpa [List.append_assoc, (c a).property] using
        (((EditScript.erase (c a).val).symm.append_right (encode c q)).append_left (encode c p))
  | delete p q a =>
      simpa [List.append_assoc, (c a).property] using
        (((EditScript.erase (c a).val).append_right (encode c q)).append_left (encode c p))
  | substitute p q a b =>
      have hh := substitution_script ((c a).property.trans (c b).property.symm)
      simpa [List.append_assoc, (c a).property] using
        ((hh.append_right (encode c q)).append_left (encode c p))

theorem encode_script {P n : ℕ} {β : Type v} (c : α → Word β P) (h : EditScript x y n) :
    EditScript (encode c x) (encode c y) (P * n) := by
  induction h with
  | nil => simpa using EditScript.nil (encode c _)
  | cons h _ ih =>
      simpa [Nat.mul_add, Nat.add_comm] using (encode_step c h).trans ih

theorem ed_encode_le {P : ℕ} {β : Type v} (c : α → Word β P) (x y : List α) :
    ed (encode c x) (encode c y) ≤ P * ed x y :=
  ed_le_of_script (encode_script c (ed_script x y))

end TreeEdit

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.EncodingUpper ----
namespace OAI

namespace TreeEdit.BinaryLower

universe u v

/-- The real-valued form of the upper estimate used in `thm:804`. -/
theorem encode_editDistance_le_real {α : Type u} {β : Type v} {P : ℕ}
    (c : α → Word β P) (x y : List α) :
    (ed (encode c x) (encode c y) : ℝ) ≤
      (P : ℝ) * (ed x y : ℝ) := by
  exact_mod_cast ed_encode_le c x y

end TreeEdit.BinaryLower

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.LCSEditUpper ----
namespace OAI

/-! The deletion/insertion half of the source's edit--LCS comparison. -/
namespace TreeEdit.BinaryLower

/-- Ordinary edit distance is bounded by the insertion--deletion distance
computed from a longest common subsequence. -/
theorem editDistance_add_twice_lcs_le {α : Type*} (x y : List α) :
    ed x y + 2 * lcs x y ≤ x.length + y.length := by
  have hd := TreeEdit.ed_le_deficits x y
  have hx := TreeEdit.lcs_le_length_left x y
  have hy := TreeEdit.lcs_le_length_right x y
  omega

/-- Upper inequality of source equation `eq:deficit`, on equal-length words. -/
theorem editDistance_le_twice_deficit {α : Type*} {n : ℕ} {x y : List α}
    (hx : x.length = n) (hy : y.length = n) :
    ed x y ≤ 2 * deficit n x y := by
  have h := editDistance_add_twice_lcs_le x y
  rw [hx, hy] at h
  unfold deficit
  omega

end TreeEdit.BinaryLower

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.SubsequenceIntersection ----
namespace OAI

namespace TreeEdit.BinaryLower

/-- Composing two common-subsequence loss bounds adds their costs. -/
theorem common_subsequence_compose {α : Type*} {x y z : List α} {m n : ℕ}
    (hxy : ∃ u : List α, u.Sublist x ∧ u.Sublist y ∧
      x.length + y.length ≤ m + 2 * u.length)
    (hyz : ∃ v : List α, v.Sublist y ∧ v.Sublist z ∧
      y.length + z.length ≤ n + 2 * v.length) :
    ∃ w : List α, w.Sublist x ∧ w.Sublist z ∧
      x.length + z.length ≤ m + n + 2 * w.length := by
  obtain ⟨u, hux, huy, hu⟩ := hxy
  obtain ⟨v, hvy, hvz, hv⟩ := hyz
  obtain ⟨w, hwu, hwv, hw⟩ := common_sublist_lower_bound huy hvy
  exact ⟨w, hwu.trans hux, hwv.trans hvz, by omega⟩

end TreeEdit.BinaryLower

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.EditLCSLower ----
namespace OAI

namespace TreeEdit.BinaryLower

/-- A script of cost `n` has a common subsequence with at most `2*n` unmatched
symbols in its two endpoints. Intermediate words are unrestricted. -/
theorem EditScript.common_subsequence {α : Type*} {x y : List α} {n : ℕ}
    (h : EditScript x y n) :
    ∃ z : List α, z.Sublist x ∧ z.Sublist y ∧
      x.length + y.length ≤ 2 * n + 2 * z.length := by
  induction h with
  | nil x =>
      exact ⟨x, List.Sublist.refl _, List.Sublist.refl _, by omega⟩
  | cons hstep hscript ih =>
      obtain ⟨z, hzx, hzy, hlen⟩ :=
        common_subsequence_compose (EditStep.common_subsequence hstep) ih
      exact ⟨z, hzx, hzy, by omega⟩

/-- The insertion/deletion deficit of a script's endpoints is at most twice
its ordinary unit-edit cost. -/
theorem EditScript.lcs_loss_le {α : Type*} {x y : List α} {n : ℕ}
    (h : EditScript x y n) :
    x.length + y.length - 2 * lcs x y ≤ 2 * n := by
  obtain ⟨z, hzx, hzy, hlen⟩ := EditScript.common_subsequence h
  have hz : z.length ≤ lcs x y := by
    apply le_csSup
    · refine ⟨x.length, ?_⟩
      rintro k ⟨w, hwx, hwy, rfl⟩
      exact hwx.length_le
    · exact ⟨z, hzx, hzy, rfl⟩
  omega

end TreeEdit.BinaryLower

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.EditDeficit ----
namespace OAI

/-!
Both metric comparisons in the preliminary section, for the actual unrestricted
unit-cost edit scripts and longest-common-subsequence definitions.
-/
namespace TreeEdit.BinaryLower

/-- Second inequality of source equation `eq:metric-conversion`. -/
theorem delta_le_twice_editDistance {α : Type*} (x y : List α) :
    x.length + y.length - 2 * lcs x y ≤ 2 * ed x y := by
  have hs : EditScript x y (ed x y) :=
    TreeEdit.ed_script x y
  exact EditScript.lcs_loss_le hs

/-- Lower inequality of source equation `eq:deficit`, on equal-length words. -/
theorem deficit_le_editDistance {α : Type*} {n : ℕ} {x y : List α}
    (hx : x.length = n) (hy : y.length = n) :
    deficit n x y ≤ ed x y := by
  have h := delta_le_twice_editDistance x y
  rw [hx, hy] at h
  unfold deficit
  omega

/-- Real-valued form used in the fixed-length binary conversion inequalities. -/
theorem editDistance_deficit_bounds_real {α : Type*} {n : ℕ} {x y : List α}
    (hx : x.length = n) (hy : y.length = n) :
    (deficit n x y : ℝ) ≤ (ed x y : ℝ) ∧
      (ed x y : ℝ) ≤ 2 * (deficit n x y : ℝ) := by
  constructor
  · exact_mod_cast deficit_le_editDistance hx hy
  · exact_mod_cast editDistance_le_twice_deficit hx hy

end TreeEdit.BinaryLower

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.CodeNumerics ----
namespace OAI

/-! Numerical estimates used in the fixed-length binary conversion. -/

open Filter Asymptotics

namespace TreeEdit.BinaryLower.Code

/-- An absolute integer threshold exists, as required in the manuscript. -/
theorem exists_short_pair_threshold :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      0 < M ∧ 2 * (M : ℝ) * segmentThreshold M ≤ (M : ℝ) ^ 2 / 2 := by
  exact eventually_atTop.1 eventually_short_pair_error

/-- Combining the deficit inequality with the two ordinary-edit comparisons
produces exactly the constant 804, without changing the edit metric. -/
theorem edit_lower_from_deficit {P r r' d d' : ℝ}
    (hP : 0 ≤ P) (hdeficit : P / 402 * r ≤ r')
    (hleft : r' ≤ d') (hright : d ≤ 2 * r) :
    P / 804 * d ≤ d' := by
  have := mul_le_mul_of_nonneg_left hright (show 0 ≤ P / 804 by positivity)
  nlinarith

/-- Integral form of the error absorption, including the zero-deficit case. -/
theorem natural_deficit_from_additive {P r δ e : ℕ}
    (hadd : P * r ≤ 201 * δ + e) (herr : 2 * e ≤ P) :
    P * r ≤ 402 * δ := by
  by_cases hr : r = 0
  · simp [hr]
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
  have hPr : P ≤ P * r := by nlinarith
  nlinarith

/-- Cast the integral matching conclusion into the exact real-valued lower
bound used in the statement of the fixed-length conversion theorem. -/
theorem real_deficit_of_natural {P r δ : ℕ}
    (h : P * r ≤ 402 * δ) :
    (P : ℝ) / 402 * r ≤ δ := by
  have h' : (P : ℝ) * r ≤ 402 * δ := by exact_mod_cast h
  linarith

/-- One absolute threshold supplies both probabilistic and deterministic estimates. -/
theorem exists_code_numerical_threshold :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      2 ≤ M ∧
      2 * (M : ℝ) * segmentThreshold M ≤ (M : ℝ) ^ 2 / 2 ∧
      (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 + 1) ^ 3 *
        (9 / 10 : ℝ) ^ segmentThreshold M < 1 := by
  rcases exists_short_pair_threshold with ⟨M₀, hM₀⟩
  refine ⟨max M₀ 2, fun M hM => ?_⟩
  have hMtwo : 2 ≤ M := (le_max_right M₀ 2).trans hM
  exact ⟨hMtwo, (hM₀ M ((le_max_left M₀ 2).trans hM)).2,
    code_union_bound_lt_one hMtwo⟩

/-- Alphabet sizes below M only decrease the comparison count. -/
theorem code_union_bound_for_alphabet {K M : ℕ} (hK : K ≤ M) (hM : 2 ≤ M) :
    (K : ℝ) ^ 2 * ((M : ℝ) ^ 2 + 1) ^ 3 *
      (9 / 10 : ℝ) ^ segmentThreshold M < 1 := by
  apply lt_of_le_of_lt _ (code_union_bound_lt_one hM)
  gcongr

end TreeEdit.BinaryLower.Code

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.SegmentCodeLCS ----
namespace OAI

namespace TreeEdit.BinaryLower.SegmentCode
open RandomMatching

/-- The codebook construction for an arbitrary finite alphabet, using the
canonical concrete word type and the actual longest common subsequence. -/
theorem exists_lcs_separated_code (Γ : Type*) [Fintype Γ] (P a₀ : ℕ)
    (hprob : (Fintype.card Γ : ℝ)^2 * ((P+1 : ℕ) : ℝ)^3 *
      (9/10 : ℝ)^a₀ < 1) :
    ∃ c : Γ → Word Bool P,
      ∀ (k l : Γ), k ≠ l → ∀ (a i j : ℕ), a₀ ≤ a →
        i+a ≤ P → j+a ≤ P →
          100 * lcs (((c k).val.drop i).take a) (((c l).val.drop j).take a) ≤ 99*a := by
  classical
  obtain ⟨c, hc⟩ := exists_segmentSeparated (Fintype.card Γ) P a₀ hprob
  let e := Fintype.equivFin Γ
  let c' : Γ → Word Bool P := fun k => ⟨List.ofFn (c (e k)), by simp⟩
  refine ⟨c', ?_⟩
  intro k l hkl a i j ha hi hj
  exact hc.lcs_le (e k) (e l) (fun h => hkl (e.injective h)) a i j ha hi hj

end TreeEdit.BinaryLower.SegmentCode

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.CodeExistence ----
namespace OAI

/-! Closing the probabilistic segment-code construction at the exact source
parameters: block width M² and cutoff ceil(120 log₂ M). -/

namespace TreeEdit.BinaryLower.Code

universe u

/-- A single binary codebook separates all long segments of unequal labels.
The alphabet can be arbitrary finite; its size is only bounded by M. -/
theorem exists_fixed_width_separated_code {M : ℕ} (hM : 2 ≤ M)
    (Γ : Type u) [Fintype Γ] (hΓ : Fintype.card Γ ≤ M) :
    ∃ c : Γ → Word Bool (M ^ 2),
      ∀ (k l : Γ), k ≠ l → ∀ (a i j : ℕ), segmentThreshold M ≤ a →
        i + a ≤ M ^ 2 → j + a ≤ M ^ 2 →
          100 * lcs (((c k).val.drop i).take a)
            (((c l).val.drop j).take a) ≤ 99 * a := by
  apply SegmentCode.exists_lcs_separated_code Γ (M ^ 2) (segmentThreshold M)
  simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using
    code_union_bound_for_alphabet hΓ hM

/-- There is an absolute threshold at which the actual codebook and the
short-pair error budget needed by the deterministic proof coexist. -/
theorem exists_binary_code_with_error_budget :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      2 ≤ M ∧
      2 * (M : ℝ) * segmentThreshold M ≤ (M : ℝ) ^ 2 / 2 ∧
      ∀ (Γ : Type u) [Fintype Γ], Fintype.card Γ ≤ M →
        ∃ c : Γ → Word Bool (M ^ 2),
          ∀ (k l : Γ), k ≠ l → ∀ (a i j : ℕ), segmentThreshold M ≤ a →
            i + a ≤ M ^ 2 → j + a ≤ M ^ 2 →
              100 * lcs (((c k).val.drop i).take a)
                (((c l).val.drop j).take a) ≤ 99 * a := by
  obtain ⟨M₀, hM₀⟩ := exists_code_numerical_threshold
  refine ⟨M₀, fun M hM => ?_⟩
  obtain ⟨hM2, herr, _⟩ := hM₀ M hM
  exact ⟨hM2, herr, fun Γ _ hΓ => exists_fixed_width_separated_code hM2 Γ hΓ⟩

end TreeEdit.BinaryLower.Code

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.CodeConversion ----
namespace OAI

/-! The exact arithmetic and metric estimates for fixed-length binary conversion. -/

namespace TreeEdit.BinaryLower.Code

universe u v

/-- The precise 402 deficit estimate implies the required 804 ordinary-edit
estimate for a fixed pair of original words. Both metrics are the actual
unrestricted unit-cost edit distance. -/
theorem encode_bounds_of_deficit {α : Type u} {β : Type v} {M P : ℕ}
    (c : α → Word β P) {x y : List α}
    (hx : x.length = M) (hy : y.length = M)
    (hdef : (P : ℝ) / 402 * (deficit M x y : ℝ) ≤
      (deficit (M * P) (encode c x) (encode c y) : ℝ)) :
    (P : ℝ) / 804 * (ed x y : ℝ) ≤
        (ed (encode c x) (encode c y) : ℝ) ∧
      (ed (encode c x) (encode c y) : ℝ) ≤
        (P : ℝ) * (ed x y : ℝ) := by
  have hencx : (encode c x).length = M * P := by rw [length_encode, hx]
  have hency : (encode c y).length = M * P := by rw [length_encode, hy]
  have hsource := editDistance_deficit_bounds_real hx hy
  have htarget := editDistance_deficit_bounds_real hencx hency
  exact ⟨edit_lower_from_deficit (Nat.cast_nonneg P) hdef htarget.1 hsource.2,
    encode_editDistance_le_real c x y⟩

/-- A code satisfying the additive block-pair estimate, with short-pair error
at most half a block, has both advertised inequalities and the stronger
one-sided-deficit inequality. The zero-deficit case is included. -/
theorem encode_bounds_of_additive {α : Type u} {β : Type v}
    {M P error : ℕ} (c : α → Word β P) {x y : List α}
    (hx : x.length = M) (hy : y.length = M)
    (hadd : P * deficit M x y ≤
      201 * deficit (M * P) (encode c x) (encode c y) + error)
    (herr : 2 * error ≤ P) :
    ((P : ℝ) / 804 * (ed x y : ℝ) ≤
        (ed (encode c x) (encode c y) : ℝ) ∧
      (ed (encode c x) (encode c y) : ℝ) ≤
        (P : ℝ) * (ed x y : ℝ)) ∧
    (P : ℝ) / 402 * (deficit M x y : ℝ) ≤
      (deficit (M * P) (encode c x) (encode c y) : ℝ) := by
  have hdef := real_deficit_of_natural (natural_deficit_from_additive hadd herr)
  exact ⟨encode_bounds_of_deficit c hx hy hdef, hdef⟩

/-- The source's real-valued short-pair threshold gives its integer loss
budget without rounding changes. -/
theorem natural_short_pair_error {M : ℕ}
    (h : 2 * (M : ℝ) * segmentThreshold M ≤ (M : ℝ) ^ 2 / 2) :
    2 * (2 * M * segmentThreshold M) ≤ M ^ 2 := by
  have h' : (2 : ℝ) * (2 * (M : ℝ) * segmentThreshold M) ≤ (M : ℝ) ^ 2 := by
    linarith
  exact_mod_cast h'

end TreeEdit.BinaryLower.Code

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.CodeAdditive ----
namespace OAI

/-! The longest encoded matching is partitioned by equality of its
original block labels. Segment separation and the span loss budget bound
the number of unequal-label matches. -/

namespace TreeEdit.BinaryLower.Code

universe u v

/-- Optional lookup at an encoded position's block always succeeds and
returns exactly its original letter. This avoids partial-label conventions. -/
theorem getElem?_blockLetter {α : Type u} {M P : ℕ} (x : List α)
    (hx : x.length = M) (hP : 0 < P) (q : Fin (M*P)) :
    x[q.val/P]? = some (originalLetterAtBit x hx hP q) := by
  have hq : q.val/P < x.length := by
    rw [hx]
    exact (Nat.div_lt_iff_lt_mul hP).mpr q.isLt
  simp only [List.getElem?_eq_getElem hq, originalLetterAtBit, List.get_eq_getElem]

/-- Unequal-edge selection can equivalently be expressed by a total predicate
on the two natural-number block indices using optional original-word lookup. -/
theorem unequalEdges_eq_filter_getElem? {α : Type u} [DecidableEq α] {M P r : ℕ}
    (x y : List α) (hx : x.length = M) (hy : y.length = M) (hP : 0 < P)
    (f g : Fin r → Fin (M*P)) :
    unequalEdges x y hx hy hP f g =
      Finset.univ.filter (fun t => x[(f t).val/P]? ≠ y[(g t).val/P]?) := by
  classical
  ext t
  simp only [unequalEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    getElem?_blockLetter x hx hP, getElem?_blockLetter y hy hP, ne_eq, Option.some.injEq]

end TreeEdit.BinaryLower.Code

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.UnequalSegments ----
namespace OAI

namespace TreeEdit.BinaryLower.Code

/-- The manuscript's unequal-label estimate for an arbitrary increasing bit
matching, from concrete separation of the segments in bad block pairs. -/
theorem unequal_matches_le_of_segment_separation
    {α : Type*} {r M P : ℕ} (hP : 0 < P)
    (x y : Fin (M * P) → α)
    (f g : Fin r → Fin (M * P)) (hf : StrictMono f) (hg : StrictMono g)
    (hmatch : ∀ t, x (f t) = y (g t))
    (bad : ℕ × ℕ → Prop) [DecidablePred bad] (a₀ : ℕ)
    (hsep : BlockSegmentSeparation x y bad a₀) :
    (Finset.univ.filter (fun t => bad ((f t).val / P, (g t).val / P))).card ≤
      200 * (M * P - r) + 2 * M * a₀ := by
  apply block_pair_bad_count_le hP f g hf hg bad a₀
  intro b hb hlarge
  obtain ⟨himage, hbad⟩ := Finset.mem_filter.mp hb
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp himage
  exact block_pair_charge_of_segment_separation hP x y f g hf hg hmatch
    bad a₀ hsep b hbad ⟨t, ht⟩ hlarge

end TreeEdit.BinaryLower.Code

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.EncodedSegmentSeparation ----
namespace OAI

namespace TreeEdit.BinaryLower.Code

universe u v

/-- The actual codebook's segment property gives the full additive deficit
bound, with no remaining local charge or matching-count hypothesis. -/
theorem additive_of_codeword_separation {α : Type u} {β : Type v}
    {M P a₀ : ℕ} (hP : 0 < P) (c : α → Word β P)
    (hsep : ∀ k l : α, k ≠ l → ∀ a i j : ℕ, a₀ ≤ a →
      i + a ≤ P → j + a ≤ P →
      100 * lcs (((c k).val.drop i).take a) (((c l).val.drop j).take a) ≤ 99 * a)
    (x y : List α) (hx : x.length = M) (hy : y.length = M) :
    P * deficit M x y ≤
      201 * deficit (M * P) (encode c x) (encode c y) + 2 * M * a₀ := by
  classical
  apply additive_of_unequal_matching_bound c x y hx hy hP
  intro r f g hf hg hmatch
  rw [unequalEdges_eq_filter_getElem?]
  exact unequal_matches_le_of_segment_separation hP
    (encodedBit c x hx) (encodedBit c y hy) f g hf hg hmatch
    (fun b => x[b.1]? ≠ y[b.2]?) a₀
    (encoded_block_segment_separation c hsep x y hx hy)

end TreeEdit.BinaryLower.Code

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FixedLengthBinaryConversion ----
namespace OAI

/-! The unconditional prescribed-length binary conversion theorem. The code
is selected once for the alphabet and input length, before either input word.
The edits used throughout are ordinary unrestricted unit-cost edits. -/

namespace TreeEdit.BinaryLower

universe u

/-- Polynomial code, `thm:804`, including the sharper `eq:402` and the exact
encoded length. The code is chosen once and works for every input pair. -/
theorem fixed_length_binary_conversion :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∀ (Γ : Type u) [Fintype Γ],
        1 ≤ Fintype.card Γ → Fintype.card Γ ≤ M →
        ∃ c : Γ → Word Bool (M ^ 2),
          (∀ x : Word Γ M, (encode c x.val).length = M ^ 3) ∧
          ∀ x y : Word Γ M,
            (((M ^ 2 : ℕ) : ℝ) / 804 * (ed x.val y.val : ℝ) ≤
                (ed (encode c x.val) (encode c y.val) : ℝ)) ∧
            ((ed (encode c x.val) (encode c y.val) : ℝ) ≤
                ((M ^ 2 : ℕ) : ℝ) * (ed x.val y.val : ℝ)) ∧
            (((M ^ 2 : ℕ) : ℝ) / 402 * (deficit M x.val y.val : ℝ) ≤
                (deficit (M * M ^ 2) (encode c x.val) (encode c y.val) : ℝ)) := by
  obtain ⟨M₀, hM₀⟩ := Code.exists_binary_code_with_error_budget.{u}
  refine ⟨M₀, ?_⟩
  intro M hM Γ inst _hΓpos hΓ
  obtain ⟨hMtwo, herr, hcode⟩ := hM₀ M hM
  obtain ⟨c, hsep⟩ := hcode Γ hΓ
  refine ⟨c, ?_, ?_⟩
  · intro x
    rw [length_encode, x.property]
    ring
  · intro x y
    have hMpos : 0 < M := by omega
    have hP : 0 < M ^ 2 := pow_pos hMpos 2
    have hadd := Code.additive_of_codeword_separation hP c hsep
      x.val y.val x.property y.property
    have hbounds := Code.encode_bounds_of_additive c x.property y.property
      hadd (Code.natural_short_pair_error herr)
    exact ⟨hbounds.1.1, hbounds.1.2, hbounds.2⟩

end TreeEdit.BinaryLower

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower


theorem solution.{u} : type_of% @_root_.OAI.TreeEdit.BinaryLower.fixed_length_binary_conversion.{u} := @_root_.OAI.TreeEdit.BinaryLower.fixed_length_binary_conversion.{u}
