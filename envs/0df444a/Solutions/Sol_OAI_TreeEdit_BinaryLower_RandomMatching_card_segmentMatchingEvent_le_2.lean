-- Prove2me | solution 2 for OAI.TreeEdit.BinaryLower.RandomMatching.card_segmentMatchingEvent_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T20:53:10.054467+00:00
-- url     : https://prove2.me/submissions/6963c9f4-c937-4f20-b7f0-816f3d8017e2

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/SegmentMatchingCount.lean:L43-L73
-- (upload_full_project.md Phase 4): solution for node OAI.TreeEdit.BinaryLower.RandomMatching.card_segmentMatchingEvent_le. The node keeps its source
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

-- ---- from OAI.Combinatorics.BinaryEdit.RandomMatching ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Exact finite counting for the prescribed-match probability in
`polynomial-code.tex`, Lemma `lem:random-segments`.
The constraints identify distinct target coordinates with coordinates outside
that target set.
-/

namespace TreeEdit.BinaryLower.RandomMatching

open Function

variable {A I B : Type*}

/-- Each independent equality removes exactly one free coordinate. -/
theorem card_constraints [Fintype A] [Fintype I] [Fintype B]
    (l : I → A) (r : I ↪ A) (hdisj : ∀ i j, l i ≠ r j) :
    Nat.card {f : A → B // ∀ i, f (l i) = f (r i)} =
      Fintype.card B ^ (Fintype.card A - Fintype.card I) := by
  classical
  rw [Nat.card_congr (constraintEquiv l r hdisj)]
  rw [Nat.card_eq_fintype_card, Fintype.card_fun,
    Fintype.card_subtype_compl, Fintype.card_range]

/-- The number of Boolean codebooks realizing one prescribed increasing
matching in two different codewords. Only injectivity of target positions is
needed; increasing matchings in particular satisfy it. -/
theorem card_prescribed_matching {K P s : ℕ}
    (i j : Fin K) (hne : i ≠ j) (u v : Fin s → Fin P)
    (hv : Function.Injective v) :
    Nat.card {c : Fin K × Fin P → Bool //
      ∀ t, c (i, u t) = c (j, v t)} = 2 ^ (K * P - s) := by
  let r : Fin s ↪ Fin K × Fin P :=
    ⟨fun t => (j, v t), fun _ _ h => hv (congrArg Prod.snd h)⟩
  have hd : ∀ t t', (i, u t) ≠ r t' := by
    intro t t' h
    exact hne (congrArg Prod.fst h)
  have h := card_constraints (B := Bool) (fun t => (i, u t)) r hd
  change Nat.card {c : Fin K × Fin P → Bool //
    ∀ t, c (i, u t) = c (j, v t)} =
      Fintype.card Bool ^ (Fintype.card (Fin K × Fin P) - Fintype.card (Fin s)) at h
  simpa only [Fintype.card_bool, Fintype.card_prod, Fintype.card_fin] using h

/-- Curried codebooks have the same exact count. -/
theorem card_prescribed_matching_curried {K P s : ℕ}
    (i j : Fin K) (hne : i ≠ j) (u v : Fin s → Fin P)
    (hv : Function.Injective v) :
    Nat.card {c : Fin K → Fin P → Bool //
      ∀ t, c i (u t) = c j (v t)} = 2 ^ (K * P - s) := by
  let e : {c : Fin K → Fin P → Bool // ∀ t, c i (u t) = c j (v t)} ≃
      {c : Fin K × Fin P → Bool // ∀ t, c (i, u t) = c (j, v t)} :=
    { toFun := fun c => ⟨fun p => c.1 p.1 p.2, c.2⟩
      invFun := fun c => ⟨fun a b => c.1 (a, b), c.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (card_prescribed_matching i j hne u v hv)

/-- Finset form, suitable for a finite union bound over forbidden matchings. -/
theorem filter_card_prescribed_matching {K P s : ℕ}
    (i j : Fin K) (hne : i ≠ j) (u v : Fin s → Fin P)
    (hv : Function.Injective v) :
    (Finset.univ.filter (fun c : Fin K → Fin P → Bool =>
      ∀ t, c i (u t) = c j (v t))).card = 2 ^ (K * P - s) := by
  classical
  rw [← Fintype.card_subtype]
  simpa only [Nat.card_eq_fintype_card] using
    card_prescribed_matching_curried i j hne u v hv

end TreeEdit.BinaryLower.RandomMatching

end OAI

-- ---- from OAI.Combinatorics.BinaryEdit.SegmentMatchingCount ----
namespace OAI

namespace TreeEdit.BinaryLower.RandomMatching

theorem card_increasingPositions (a s : ℕ) :
    Nat.card (IncreasingPositions a s) = a.choose s := by
  classical
  rw [Nat.card_congr (increasingPositionsEquiv a s), Nat.card_eq_fintype_card]
  simp

/-- Finite union estimate for one pair of unequal-label windows. -/
theorem card_segmentMatchingEvent_le {K P a s : ℕ}
    (i j : Fin K) (hne : i ≠ j) (u v : Fin a → Fin P)
    (hv : Function.Injective v) :
    (segmentMatchingEvent s i j u v).card ≤
      (a.choose s) ^ 2 * 2 ^ (K * P - s) := by
  classical
  let event (fg : IncreasingPositions a s × IncreasingPositions a s) :=
    Finset.univ.filter fun c : Fin K → Fin P → Bool =>
      ∀ t, c i (u (fg.1.1 t)) = c j (v (fg.2.1 t))
  have hcard (fg : IncreasingPositions a s × IncreasingPositions a s) :
      (event fg).card = 2 ^ (K * P - s) :=
    filter_card_prescribed_matching i j hne (u ∘ fg.1.1) (v ∘ fg.2.1)
      (hv.comp fg.2.2.injective)
  have heq : segmentMatchingEvent s i j u v = Finset.univ.biUnion event := by
    ext c
    simp only [segmentMatchingEvent, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_biUnion, event]
    constructor
    · rintro ⟨f, g, hfg⟩
      exact ⟨(f, g), hfg⟩
    · rintro ⟨⟨f, g⟩, hfg⟩
      exact ⟨f, g, hfg⟩
  have hc : Fintype.card (IncreasingPositions a s) = a.choose s := by
    simpa only [Nat.card_eq_fintype_card] using card_increasingPositions a s
  rw [heq]
  calc
    (Finset.univ.biUnion event).card ≤ ∑ fg, (event fg).card := Finset.card_biUnion_le
    _ = (a.choose s) ^ 2 * 2 ^ (K * P - s) := by
      simp only [hcard, Finset.sum_const, Finset.card_univ, Fintype.card_prod, hc,
        smul_eq_mul, pow_two]

end TreeEdit.BinaryLower.RandomMatching

end OAI

-- ---- platform node ----
open OAI OAI.TreeEdit OAI.TreeEdit.BinaryLower OAI.TreeEdit.BinaryLower.RandomMatching


theorem solution : type_of% @_root_.OAI.TreeEdit.BinaryLower.RandomMatching.card_segmentMatchingEvent_le := @_root_.OAI.TreeEdit.BinaryLower.RandomMatching.card_segmentMatchingEvent_le
