-- Prove2me | solution 1 for OAI.CHObstruction.Tests.no_pattern
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:22:21.633159+00:00
-- url     : https://prove2.me/submissions/da02a8b4-d747-48ec-9483-90f9938e1f78

-- Generated from openai/math@1581d4c lean/OAI/ModelTheory/Categoricity/Colors.lean:L173-L201
-- (upload_full_project.md Phase 4): solution for node OAI.CHObstruction.Tests.no_pattern. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CHObstruction
import Definitions.Def_OAI_ModelTheory_Categoricity_Collapse
import Definitions.Def_OAI_ModelTheory_Categoricity_Diagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_Partition
import Definitions.Def_OAI_ModelTheory_Categoricity_Colors

-- ---- from OAI.ModelTheory.Categoricity.Diagrams ----
namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Diagrams

namespace Label

end Label

namespace Diagram

variable {A : Type v} {B : Type w}

end Diagram

end Diagrams

namespace NoPattern

open Diagrams

variable (d : ∀ k : ℕ, Diagram.{u} (Fin k))
  (valid : ∀ k, (d k).Valid)
  (coherent : ∀ m n (e : Fin m ↪o Fin n), d m = (d n).restrict e.toEmbedding)

section FiniteStages

variable {J : Type u} [LinearOrder J]

end FiniteStages

include d valid coherent in

theorem impossible : False := by
  let V := ZFSet.vonNeumann (ω_ (1 : Ordinal.{u}))
  let J := (succ V.card).ord.ToType
  let e : J ↪ Shrink.{u} V :=
    (rootsEmbedding d valid coherent (J := J)).trans (equivShrink V).toEmbedding
  have hle : succ V.card ≤ V.card := by
    simpa only [J, Cardinal.mk_toType, Cardinal.card_ord, ZFSet.card]
      using Cardinal.mk_le_of_injective e.injective
  exact (lt_succ V.card).not_ge hle

end NoPattern

end CHObstruction

end

end OAI

-- ---- from OAI.ModelTheory.Categoricity.Colors ----
namespace OAI

universe u v w

noncomputable section

namespace CHObstruction

open Cardinal Ordinal Order

namespace Colors

open Diagrams

end Colors

namespace Tuples

end Tuples

namespace Tests

theorem embedding_refl (A : Type v) [Preorder A] :
    (OrderIso.refl A).toOrderEmbedding.toEmbedding = Function.Embedding.refl A := by
  ext x
  rfl

open Diagrams Colors Tuples

variable (hCH : CH.{u})

theorem empty_valid : emptyDiagram.{u}.Valid := by
  constructor
  · exact ⟨fun a => isEmptyElim a, fun {a} => isEmptyElim a, fun {a} => isEmptyElim a⟩
  all_goals intro a; exact isEmptyElim a

theorem empty_unique (d : Diagram.{u} (Fin 0)) : d = emptyDiagram := by
  cases d
  congr <;> funext a <;> exact isEmptyElim a

theorem no_pattern (p : ℕ → Palette.{u})
    (hp : ∀ n : ℕ, Passes hCH (n := n) (fun m _ => p m)) : False := by
  choose d hd using hp
  have hvalid : ∀ n, (d n).Valid := by
    intro n
    simpa only [embedding_refl, Diagram.restrict_refl] using (hd n n (OrderIso.refl _).toOrderEmbedding).1
  have hcode : ∀ n, code hCH ⟨n, d n⟩ = p n := by
    intro n
    simpa only [embedding_refl, Diagram.restrict_refl] using (hd n n (OrderIso.refl _).toOrderEmbedding).2
  have hcoh : ∀ m n (e : Fin (m + 1) ↪o Fin (n + 1)),
      d m = (d n).restrict e.toEmbedding := by
    intro m n e
    have he := (code hCH).injective ((hcode m).trans (hd n m e).2.symm)
    exact eq_of_heq (Sigma.mk.inj_iff.1 he).2
  let allD : ∀ k : ℕ, Diagram.{u} (Fin k)
    | 0 => emptyDiagram
    | n + 1 => d n
  apply NoPattern.impossible allD
  · intro k
    cases k with
    | zero => exact empty_valid
    | succ n => exact hvalid n
  · intro m n e
    cases m with
    | zero => exact (empty_unique ((allD n).restrict e.toEmbedding)).symm
    | succ m =>
      cases n with
      | zero => exact Fin.elim0 (e 0)
      | succ n => exact hcoh m n e

end Tests

end CHObstruction

end

end OAI

-- ---- platform node ----
open OAI OAI.CHObstruction OAI.CHObstruction.Tests
open Cardinal Ordinal Order
open Diagrams Colors Tuples


theorem solution.{u} : type_of% @_root_.OAI.CHObstruction.Tests.no_pattern.{u} := @_root_.OAI.CHObstruction.Tests.no_pattern.{u}
