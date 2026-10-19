-- Prove2me | solution 1 for OAI.Saxl.extendColor_count_new
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T01:51:57.066479+00:00
-- url     : https://prove2.me/submissions/c82812b1-4560-4584-91a3-d263bb9bdec2

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/StripExtension.lean:L107-L120
-- (upload_full_project.md Phase 4): solution for node OAI.Saxl.extendColor_count_new. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence
import Definitions.Def_OAI_RepresentationTheory_Saxl_PieriRestriction
import Definitions.Def_OAI_RepresentationTheory_Saxl_StripExtension

-- ---- from OAI.RepresentationTheory.Saxl.StripExtension ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

lemma extendColor_mem {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (hc : ∀ x, c x ≤ q) (x : Fin n) :
    extendColor i c (q+1) x ≤ q ↔ x ∈ Set.range i := by
  classical
  unfold extendColor
  split_ifs with h
  · exact iff_of_true (hc _) h
  · simp [h]

lemma extendColor_le {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (hc : ∀ x, c x ≤ q) (x : Fin n) : extendColor i c (q+1) x ≤ q+1 := by
  classical
  unfold extendColor
  split_ifs
  · exact (hc _).trans (Nat.le_succ q)
  · exact le_rfl

lemma extendColor_count_new {a n : ℕ} (i : Fin a ↪ Fin n) (c : Fin a → ℕ) (q : ℕ)
    (hc : ∀ x, c x ≤ q) :
    (Finset.univ.filter (fun x => extendColor i c (q+1) x = q+1)).card = n-a := by
  classical
  have he : Finset.univ.filter (fun x => extendColor i c (q+1) x = q+1) =
      Finset.univ \ Finset.univ.map i := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, Finset.mem_map]
    change extendColor i c (q+1) x = q+1 ↔ ¬ x ∈ Set.range i
    rw [← extendColor_mem i c q hc x]
    have hl := extendColor_le i c q hc x
    omega
  rw [he, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    Finset.card_map, Finset.card_univ, Fintype.card_fin]

end Saxl

end

end OAI

-- ---- platform node ----
open OAI OAI.Saxl
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.Saxl.extendColor_count_new := @_root_.OAI.Saxl.extendColor_count_new
