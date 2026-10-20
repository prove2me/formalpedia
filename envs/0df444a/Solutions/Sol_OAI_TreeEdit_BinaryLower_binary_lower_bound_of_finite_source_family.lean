-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.binary_lower_bound_of_finite_source_family
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:47:07.742793+00:00
-- url     : https://prove2.me/submissions/bb8e7e57-c1fd-4f23-be1d-a9a838277d51

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
import Theorems.Thm_OAI_TreeEdit_BinaryLower_c1_le_encodedSet_mul
import Theorems.Thm_OAI_TreeEdit_BinaryLower_Parameters_exists_finite_cap_parameters

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower
universe u
theorem h49_ins {β : Type*} (w : List β) : ∀ (u v : List β), EditScript (u ++ v) (u ++ w ++ v) w.length := by
  induction w with
  | nil => intro u v; simpa using EditScript.nil (u ++ v)
  | cons a w ih =>
    intro u v
    have h1 : EditStep (u ++ v) (u ++ a :: v) := EditStep.insert u v a
    have h2 := ih (u ++ [a]) v
    have e1 : (u ++ [a]) ++ v = u ++ a :: v := by simp
    have e2 : u ++ [a] ++ w ++ v = u ++ a :: w ++ v := by simp
    rw [e1, e2] at h2
    have := EditScript.cons h1 h2
    simpa [Nat.add_comm] using this

theorem h49_tri {β : Type*} (x y z : List β) : ed x z ≤ ed x y + ed y z :=
  ed_le_of_script ((ed_script x y).trans (ed_script y z))

theorem h49_enc_step {α : Type*} {P : ℕ} (c : α → Word Bool P) {x y : List α} (h : EditStep x y) :
    ed (encode c x) (encode c y) ≤ 2 * P := by
  have hins : ∀ (p q : List α) (a : α), ed (encode c (p ++ q)) (encode c (p ++ a :: q)) ≤ P := by
    intro p q a
    have := h49_ins (c a).val (encode c p) (encode c q)
    rw [(c a).property] at this
    have e1 : encode c (p ++ q) = encode c p ++ encode c q := by simp
    have e2 : encode c (p ++ a :: q) = encode c p ++ (c a).val ++ encode c q := by simp
    rw [e1, e2]; exact ed_le_of_script this
  cases h with
  | insert p q a => have := hins p q a; omega
  | delete p q a => rw [ed_comm]; have := hins p q a; omega
  | substitute p q a b =>
    have h1 := hins p q a
    have h2 := hins p q b
    rw [ed_comm] at h1
    have := h49_tri (encode c (p ++ a :: q)) (encode c (p ++ q)) (encode c (p ++ b :: q))
    omega

theorem h49_enc_le {α : Type*} {P : ℕ} (c : α → Word Bool P) (x y : List α) :
    ed (encode c x) (encode c y) ≤ 2 * P * ed x y := by
  have key : ∀ n (x y : List α), EditScript x y n → ed (encode c x) (encode c y) ≤ 2 * P * n := by
    intro n x y h
    induction h with
    | nil x => simp
    | @cons x' y' z' m hs hrest ih =>
      have := h49_enc_step c hs
      refine (h49_tri _ (encode c y') _).trans ?_
      rw [Nat.mul_succ]; omega
  exact key _ x y (ed_script x y)

theorem solution
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
  obtain ⟨M₀, hM₀⟩ := hcode
  obtain ⟨c₀, hc₀, K, hK⟩ := hfamily
  obtain ⟨d₀, hd₀⟩ := Parameters.exists_finite_cap_parameters (c₀ := c₀ / 1608) (by positivity) (max K M₀)
  refine ⟨1/160, by norm_num, d₀, fun d hd => ?_⟩
  obtain ⟨k, hkK, hk20, hfl, hexp⟩ := hd₀ d hd
  have hkM : k ≤ finiteSourceLength k := by
    unfold finiteSourceLength
    have h1 : 1 ≤ 20 * k * k ^ (20 * k) := Nat.one_le_iff_ne_zero.2 (by positivity)
    calc k ≤ 20 * k * k ^ (20 * k) := by
          have : 1 ≤ k ^ (20 * k) := Nat.one_le_iff_ne_zero.2 (by positivity)
          nlinarith
      _ ≤ (20 * k * k ^ (20 * k)) ^ k := Nat.le_self_pow (by omega) _
  set M := finiteSourceLength k with hMdef
  have hM1 : 1 ≤ M := by omega
  obtain ⟨Γ, inst, hΓ1, hΓM, W, hW2, hW⟩ := hK k (le_of_max_le_left hkK)
  obtain ⟨c, hc⟩ := @hM₀ M (by have := le_of_max_le_right hkK; omega) Γ inst hΓ1 hΓM
  have hM2pos : (0:ℝ) < ((M^2 : ℕ) : ℝ) := by positivity
  have hlow : ∀ x y : Word Γ M, ((M^2 : ℕ) : ℝ) / 804 * (ed x.val y.val : ℝ) ≤
      (ed (encode c x.val) (encode c y.val) : ℝ) := hc
  have hup : ∀ x y : Word Γ M, (ed (encode c x.val) (encode c y.val) : ℝ) ≤
      (2 * ((M^2 : ℕ) : ℝ)) * (ed x.val y.val : ℝ) := by
    intro x y
    have := h49_enc_le c x.val y.val
    exact_mod_cast this
  have hmain := c1_le_encodedSet_mul c W hW2 (a := ((M^2 : ℕ) : ℝ) / 804) (b := 2 * ((M^2 : ℕ) : ℝ))
    (by positivity) (by positivity) hlow hup
  have hratio : (2 * ((M^2 : ℕ) : ℝ)) / (((M^2 : ℕ) : ℝ) / 804) = 1608 := by
    field_simp; ring
  rw [hratio] at hmain
  refine ⟨M * M^2, ?_, ?_, encodedSet c W, ?_, ?_⟩
  · have : 1 ≤ M^2 := Nat.one_le_pow _ _ hM1
    nlinarith
  · have : Parameters.finiteLength k = M * M^2 := by
      rw [hMdef]; unfold Parameters.finiteLength finiteSourceLength; rw [mul_comm 3 k, pow_mul]; ring
    omega
  · unfold encodedSet
    rw [Finset.card_image_of_injOn]
    · exact hW2
    · intro x _ y _ hxy
      have h1 := hlow x y
      have h2 : encode c x.val = encode c y.val := congrArg Subtype.val hxy
      rw [h2, ed_self, Nat.cast_zero] at h1
      have h3 : (ed x.val y.val : ℝ) ≤ 0 := by
        have ha : (0:ℝ) < ((M^2 : ℕ) : ℝ) / 804 := by positivity
        by_contra hcon; push_neg at hcon
        have := mul_pos ha hcon
        linarith
      have h4 : ed x.val y.val = 0 := by exact_mod_cast le_antisymm h3 (by positivity)
      exact Subtype.ext (ed_eq_zero_iff.1 h4)
  · unfold growth
    calc Real.exp (1 / 160 * Real.sqrt (Real.log (d:ℝ) * Real.log (Real.log (d:ℝ))))
        ≤ c₀ / 1608 * ((k:ℝ) / 4) ^ k := hexp
      _ = (c₀ * ((k:ℝ) / 4) ^ k) / 1608 := by ring
      _ ≤ c1 {x : Word Γ (finiteSourceLength k) // x ∈ W}
            (fun x y => (ed x.val.val y.val.val : ℝ)) / 1608 := by gcongr
      _ ≤ binarySetDistortion (encodedSet c W) := by
            rw [div_le_iff₀ (by norm_num)]; linarith

