-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.binary_lower_bound_of_finite_source_family
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:26:38.475361+00:00
-- url     : https://prove2.me/submissions/3e312d63-c9f2-4d97-9254-27b6ed9964e4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteFamilyTransfer.lean:L29-L75
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.binary_lower_bound_of_finite_source_family. The node keeps its source
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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Parameters_exists_finite_cap_parameters
import Theorems.Thm_OAI_TreeEdit_BinaryLower_c1_le_encodedSet_mul

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

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteParameters ----
namespace OAI

namespace TreeEdit.BinaryLower.Parameters

lemma finiteLength_pos {k : ℕ} (hk : 0 < k) : 0 < finiteLength k := by
  unfold finiteLength
  positivity

end TreeEdit.BinaryLower.Parameters

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteCapTransfer ----
namespace OAI

namespace TreeEdit.BinaryLower

/-- Apply the numerical cap interpolation to actual finite sets of binary
words.  The hypothesis is exactly the output needed from the finite-tree
obstruction followed by the fixed-length binary code. -/
theorem binary_lower_bound_of_finite_family
    (hfamily : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∃ W : Finset (Word Bool (Parameters.finiteLength k)),
        2 ≤ W.card ∧ c₀ * ((k : ℝ) / 4) ^ k ≤ binarySetDistortion W) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ d ∧
        ∃ W : Finset (Word Bool n), 2 ≤ W.card ∧
          growth c d ≤ binarySetDistortion W := by
  obtain ⟨c₀, hc₀, K, hfamily⟩ := hfamily
  obtain ⟨d₀, hd₀⟩ := Parameters.exists_finite_cap_parameters hc₀ K
  refine ⟨1 / 160, by norm_num, d₀, ?_⟩
  intro d hd
  obtain ⟨k, hkK, hk20, hkcap, hkgrowth⟩ := hd₀ d hd
  obtain ⟨W, hWcard, hWdist⟩ := hfamily k hkK
  refine ⟨Parameters.finiteLength k, ?_, hkcap, W, hWcard, ?_⟩
  · exact Parameters.finiteLength_pos (by omega : 0 < k)
  · exact hkgrowth.trans hWdist

end TreeEdit.BinaryLower

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

-- ---- from OAI.Combinatorics.BinaryEdit.EncodedImage ----
namespace OAI

/-! Distortion transport through finite images of fixed-width codes. -/

noncomputable section
namespace TreeEdit.BinaryLower

universe u

lemma encodedWord_injective_of_lower {α : Type u} {M P : ℕ}
    (c : α → Word Bool P) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ x y : Word α M,
      a * (ed x.val y.val : ℝ) ≤
        (ed (encode c x.val) (encode c y.val) : ℝ)) :
    Function.Injective (encodedWord (M := M) c) := by
  intro x y hxy
  apply Subtype.ext
  apply ed_eq_zero_iff.mp
  have hval : encode c x.val = encode c y.val := congrArg Subtype.val hxy
  have h := hlower x y
  rw [hval, ed_self, Nat.cast_zero] at h
  have hed : (ed x.val y.val : ℝ) ≤ 0 := nonpos_of_mul_nonpos_right h ha
  exact Nat.eq_zero_of_le_zero (by exact_mod_cast hed)

lemma encodedSet_card {α : Type u} {M P : ℕ}
    (c : α → Word Bool P) {a : ℝ} (ha : 0 < a)
    (hlower : ∀ x y : Word α M,
      a * (ed x.val y.val : ℝ) ≤
        (ed (encode c x.val) (encode c y.val) : ℝ))
    (W : Finset (Word α M)) : (encodedSet c W).card = W.card := by
  exact Finset.card_image_of_injective W (encodedWord_injective_of_lower c ha hlower)

/-- The scale cancels: lower factor `P/804` and upper factor `P` lose only `804`. -/
lemma c1_le_804_encodedSet {α : Type u} {M P : ℕ}
    (c : α → Word Bool P) (hP : 0 < P)
    (W : Finset (Word α M)) (hW : 2 ≤ W.card)
    (hlower : ∀ x y : Word α M,
      ((P : ℝ) / 804) * (ed x.val y.val : ℝ) ≤
        (ed (encode c x.val) (encode c y.val) : ℝ)) :
    c1 {x : Word α M // x ∈ W}
      (fun x y => (ed x.val.val y.val.val : ℝ)) ≤
        804 * binarySetDistortion (encodedSet c W) := by
  have hPR : (0 : ℝ) < P := Nat.cast_pos.mpr hP
  have h := c1_le_encodedSet_mul c W hW (a := (P : ℝ) / 804) (b := (P : ℝ))
    (by positivity) hPR hlower (fun x y => encode_editDistance_le_real c x.val y.val)
  have hratio : (P : ℝ) / ((P : ℝ) / 804) = 804 := by
    field_simp
  simpa only [hratio] using h

/-- Existential form used by the finite-tree binary-family construction. -/
theorem exists_binary_image_of_code {α : Type u} {M P : ℕ}
    (c : α → Word Bool P) (hP : 0 < P)
    (W : Finset (Word α M)) (hW : 2 ≤ W.card)
    (hlower : ∀ x y : Word α M,
      ((P : ℝ) / 804) * (ed x.val y.val : ℝ) ≤
        (ed (encode c x.val) (encode c y.val) : ℝ)) :
    ∃ V : Finset (Word Bool (M * P)), 2 ≤ V.card ∧
      c1 {x : Word α M // x ∈ W}
        (fun x y => (ed x.val.val y.val.val : ℝ)) / 804 ≤
          binarySetDistortion V := by
  have hPR : (0 : ℝ) < P := Nat.cast_pos.mpr hP
  refine ⟨encodedSet c W, ?_, ?_⟩
  · rw [encodedSet_card c (by positivity : (0 : ℝ) < P / 804) hlower W]
    exact hW
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 804)).mpr
    simpa only [mul_comm] using c1_le_804_encodedSet c hP W hW hlower

end TreeEdit.BinaryLower

end

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.FiniteFamilyTransfer ----
namespace OAI

noncomputable section
namespace TreeEdit.BinaryLower

universe u

lemma le_finiteSourceLength {k : ℕ} (hk : 0 < k) : k ≤ finiteSourceLength k := by
  have hp : 1 ≤ k ^ (20 * k) := Nat.one_le_pow _ _ hk
  have hb : k ≤ 20 * k * k ^ (20 * k) := by
    have := Nat.mul_le_mul_left (20 * k) hp
    nlinarith
  exact hb.trans (Nat.le_pow hk)

lemma finiteSourceLength_mul_sq (k : ℕ) :
    finiteSourceLength k * finiteSourceLength k ^ 2 = Parameters.finiteLength k := by
  unfold finiteSourceLength Parameters.finiteLength
  calc
    _ = ((20 * k * k ^ (20 * k)) ^ k) ^ 3 := by ring
    _ = (20 * k * k ^ (20 * k)) ^ (k * 3) := (pow_mul _ _ _).symm
    _ = _ := by rw [Nat.mul_comm k 3]

/-- A finite-alphabet lower bound transfers to the all-cap binary lower bound
through a fixed-width binary code. -/
theorem binary_lower_bound_of_finite_source_family
    (hcode : ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ∀ (Γ : Type u) [Fintype Γ],
        1 ≤ Fintype.card Γ → Fintype.card Γ ≤ M →
        ∃ c : Γ → Word Bool (M ^ 2), ∀ x y : Word Γ M,
          (((M ^ 2 : ℕ) : ℝ) / 804) * (ed x.val y.val : ℝ) ≤
            (ed (encode c x.val) (encode c y.val) : ℝ))
    (hfamily : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∃ Γ : Type u, ∃ inst : Fintype Γ,
        1 ≤ @Fintype.card Γ inst ∧ @Fintype.card Γ inst ≤ finiteSourceLength k ∧
        ∃ W : Finset (Word Γ (finiteSourceLength k)), 2 ≤ W.card ∧
          c₀ * ((k : ℝ) / 4) ^ k ≤
            c1 {x : Word Γ (finiteSourceLength k) // x ∈ W}
              (fun x y => (ed x.val.val y.val.val : ℝ))) :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∃ n : ℕ, 1 ≤ n ∧ n ≤ d ∧
        ∃ W : Finset (Word Bool n), 2 ≤ W.card ∧
          growth c d ≤ binarySetDistortion W := by
  obtain ⟨M₀, hcode⟩ := hcode
  obtain ⟨c₀, hc₀, K, hfamily⟩ := hfamily
  apply binary_lower_bound_of_finite_family
  refine ⟨c₀ / 804, by positivity, max K (max M₀ 1), ?_⟩
  intro k hk
  have hkK : K ≤ k := (le_max_left _ _).trans hk
  have hkM : M₀ ≤ k := (le_max_left M₀ 1).trans ((le_max_right _ _).trans hk)
  have hk1 : 1 ≤ k := (le_max_right M₀ 1).trans ((le_max_right _ _).trans hk)
  have hMk : k ≤ finiteSourceLength k := le_finiteSourceLength hk1
  obtain ⟨Γ, inst, hΓ1, hΓM, W, hW, hdist⟩ := hfamily k hkK
  let : Fintype Γ := inst
  obtain ⟨c, hc⟩ := hcode (finiteSourceLength k) (hkM.trans hMk) Γ hΓ1 hΓM
  have hP : 0 < finiteSourceLength k ^ 2 := by
    have : 0 < finiteSourceLength k := hk1.trans hMk
    positivity
  obtain ⟨V, hV, hVdist⟩ := exists_binary_image_of_code c hP W hW hc
  have hresult : ∃ V : Finset (Word Bool (finiteSourceLength k * finiteSourceLength k ^ 2)),
      2 ≤ V.card ∧ (c₀ / 804) * ((k : ℝ) / 4) ^ k ≤ binarySetDistortion V := by
    refine ⟨V, hV, ?_⟩
    calc
      _ = (c₀ * ((k : ℝ) / 4) ^ k) / 804 := by ring
      _ ≤ c1 {x : Word Γ (finiteSourceLength k) // x ∈ W}
          (fun x y => (ed x.val.val y.val.val : ℝ)) / 804 :=
        div_le_div_of_nonneg_right hdist (by norm_num)
      _ ≤ binarySetDistortion V := hVdist
  rw [finiteSourceLength_mul_sq] at hresult
  exact hresult

end TreeEdit.BinaryLower

end

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower


theorem solution.{u} : type_of% @_root_.OAI.TreeEdit.BinaryLower.binary_lower_bound_of_finite_source_family.{u} := @_root_.OAI.TreeEdit.BinaryLower.binary_lower_bound_of_finite_source_family.{u}
