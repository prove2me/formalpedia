-- Prove2me | solution 1 for OAI.TreeEdit.BinaryLower.Code.equal_match_count_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:13:10.474521+00:00
-- url     : https://prove2.me/submissions/c2a45212-bcc8-4659-97df-3567a5d6b3ce

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

open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.Code
theorem h49_gap {N : ℕ} (f : Fin N → ℕ) (hf : StrictMono f) :
    ∀ (k : ℕ) (a b : Fin N), b.val = a.val + k → f a + k ≤ f b := by
  intro k
  induction k with
  | zero => intro a b h; rw [show a = b from Fin.ext (by omega)]; simp
  | succ k ih =>
    intro a b h
    have hc : a.val + k < N := by omega
    have h1 := ih a ⟨a.val + k, hc⟩ rfl
    have h2 : f ⟨a.val + k, hc⟩ < f b := hf (Fin.mk_lt_of_lt_val (by omega))
    omega

theorem h49_step {N P : ℕ} (hP : 0 < P) (f : Fin N → ℕ) (hf : StrictMono f) (a b : Fin N)
    (hab : a < b) (hmod : a.val % P = b.val % P) : f a / P < f b / P := by
  have hb : a.val + P ≤ b.val := by
    have e1 := Nat.div_add_mod a.val P
    have e2 := Nat.div_add_mod b.val P
    have hlt : a.val / P < b.val / P := by
      by_contra hcon
      push_neg at hcon
      have : P * (b.val / P) ≤ P * (a.val / P) := Nat.mul_le_mul_left _ hcon
      have : (b:ℕ) < a := by omega
      exact absurd hab (not_lt.2 (le_of_lt this))
    have : P * (a.val / P) + P ≤ P * (b.val / P) := by
      have := Nat.mul_le_mul_left P hlt
      rw [Nat.mul_succ] at this; exact this
    omega
  have := h49_gap f hf (b.val - a.val) a b (by omega)
  have h3 : f a + P ≤ f b := by omega
  calc f a / P < f a / P + 1 := Nat.lt_succ_self _
    _ = (f a + P) / P := (Nat.add_div_right _ hP).symm
    _ ≤ f b / P := Nat.div_le_div_right h3

theorem solution {N P L : ℕ} (hP : 0 < P)
    (f g : Fin N → ℕ) (hf : StrictMono f) (hg : StrictMono g)
    (hL : ∀ s : Finset (Fin N),
      StrictMonoOn (fun i => f i / P) (s : Set (Fin N)) →
      StrictMonoOn (fun i => g i / P) (s : Set (Fin N)) → s.card ≤ L) :
    N ≤ P * L := by
  classical
  have hcard : N = ∑ r ∈ Finset.range P, (Finset.univ.filter fun i : Fin N => i.val % P = r).card := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin N)))
      (t := Finset.range P) (f := fun i : Fin N => i.val % P)
      (fun i _ => Finset.mem_range.2 (Nat.mod_lt _ hP))
    simpa using this
  rw [hcard]
  calc ∑ r ∈ Finset.range P, (Finset.univ.filter fun i : Fin N => i.val % P = r).card
      ≤ ∑ _r ∈ Finset.range P, L := by
        refine Finset.sum_le_sum fun r _ => hL _ ?_ ?_
        · intro a ha b hb hab
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
          exact h49_step hP f hf a b hab (ha.trans hb.symm)
        · intro a ha b hb hab
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha hb
          exact h49_step hP g hg a b hab (ha.trans hb.symm)
    _ = P * L := by simp

