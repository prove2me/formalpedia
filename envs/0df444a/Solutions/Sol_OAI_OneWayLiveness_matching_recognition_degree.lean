-- Prove2me | solution 1 for OAI.OneWayLiveness.matching_recognition_degree
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:09:21.178369+00:00
-- url     : https://prove2.me/submissions/35ae1c9f-0955-407c-9d4c-21dbdfeace10

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/Syntactic.lean:L22-L55
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.matching_recognition_degree. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners
import Definitions.Def_OAI_Combinatorics_Automata_Relations
import Definitions.Def_OAI_Combinatorics_Automata_RankLoss
import Theorems.Thm_OAI_OneWayLiveness_relation_divisor_degree

-- ---- from OAI.Combinatorics.Automata.Syntactic ----
namespace OAI

namespace OneWayLiveness
open scoped Classical

namespace BRel
variable {H : Type*}
lemma singleton_context (a : BRel H) (i j : H) :
    (∃ x y, (restrictedId {i} * a * restrictedId {j}).holds x y) ↔ a.holds i j := by
  simp only [mul_restrictedId, restrictedId_mul, Set.mem_singleton_iff]
  aesop

lemma context_separates (u v : List (BRel H))
    (h : ∀ x y : List (BRel H), live (x ++ u ++ y) ↔ live (x ++ v ++ y)) : u.prod = v.prod := by
  ext i j
  have hh := h [restrictedId {i}] [restrictedId {j}]
  simpa only [live, List.prod_append, List.prod_cons, List.prod_nil, mul_one, singleton_context] using hh
end BRel

/-- Any matching recognition of liveness induces the full relation divisor.
The recognizer predicate may in particular sandwich the fixed endmarkers
and inspect the designated test ports. -/
theorem matching_recognition_degree {H A : Type} [Fintype H] [Fintype A]
    (η : BRel H → Pairing (A ⊕ A)) (test : Pairing (A ⊕ A) → Prop)
    (hη : ∀ w : List (BRel H), test (w.map η).prod ↔ BRel.live w)
    (x y : H) (hxy : x ≠ y) : rankLoss (Fintype.card H) ≤ Fintype.card A := by
  classical
  let S : Submonoid (Pairing (A ⊕ A) × BRel H) := {
    carrier := {p | ∃ w : List (BRel H), p = ((w.map η).prod, w.prod)}
    one_mem' := ⟨[], by simp only [List.map_nil, List.prod_nil]; rfl⟩
    mul_mem' := by
      rintro a b ⟨u, rfl⟩ ⟨v, rfl⟩
      exact ⟨u ++ v, by simp⟩ }
  let ρ : S →* Pairing (A ⊕ A) := (MonoidHom.fst _ _).comp S.subtype
  let φ : S →* BRel H := (MonoidHom.snd _ _).comp S.subtype
  have hρ : Function.Injective ρ := by
    intro a b hab
    obtain ⟨u, hu⟩ := a.property
    obtain ⟨v, hv⟩ := b.property
    have hd : (u.map η).prod = (v.map η).prod := by
      change a.val.1 = b.val.1 at hab
      simpa only [hu, hv] using hab
    have hr : u.prod = v.prod := by
      apply BRel.context_separates
      intro l r
      rw [← hη, ← hη]
      simp only [List.map_append, List.prod_append, hd]
    apply Subtype.ext
    rw [hu, hv, hd, hr]
  have hφ : Function.Surjective φ := by
    intro R
    exact ⟨⟨(η R, R), [R], by simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]⟩, rfl⟩
  exact relation_divisor_degree ρ hρ φ hφ x y hxy

end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness
open scoped Classical


theorem solution : type_of% @_root_.OAI.OneWayLiveness.matching_recognition_degree := @_root_.OAI.OneWayLiveness.matching_recognition_degree
