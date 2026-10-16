-- Prove2me | solution 1 for OAI.Thorp.Young.partition_count_le_sqrt_pow
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:07:40.707604+00:00
-- url     : https://prove2.me/submissions/3a00a625-233d-47a4-9fdb-61c692c89176

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/PartitionBounds.lean:L136-L170
-- (upload_full_project.md Phase 4): solution for node OAI.Thorp.Young.partition_count_le_sqrt_pow. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
import Definitions.Def_OAI_Probability_ThorpShuffle_Classification
import Definitions.Def_OAI_Probability_ThorpShuffle_LinearExtensions
import Definitions.Def_OAI_Probability_ThorpShuffle_ExtensionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_PartitionBounds

-- ---- from OAI.Probability.ThorpShuffle.Classification ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uG uI uV uα

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

lemma card_ofPartition {n : ℕ} (p : Nat.Partition n) : Fintype.card (Cells (ofPartition p)) = n := by
  rw [card_cells_eq_sum, rowLens_ofPartition]
  simpa only [← Multiset.sum_coe, Multiset.sort_eq] using p.parts_sum

end Thorp.Young

namespace Thorp.Fourier
open scoped Classical

variable {G : Type uG} [Group G] [Fintype G]

end Thorp.Fourier

namespace Thorp.Specht
open scoped Classical
variable {α : Type uα} [Fintype α]

end Thorp.Specht

namespace Thorp.Specht
open scoped Classical
variable {α : Type uα} [Fintype α]

end Thorp.Specht

end

end OAI

-- ---- from OAI.Probability.ThorpShuffle.PartitionBounds ----
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

end Thorp.Young

namespace Thorp.Young
open scoped Classical

lemma rectangle_card_le (D : YoungDiagram) (x : Cells D) :
    (x.val.1 + 1) * (x.val.2 + 1) ≤ Fintype.card (Cells D) := by
  let f : Fin (x.val.1 + 1) × Fin (x.val.2 + 1) → Cells D := fun p =>
    ⟨(p.1, p.2), D.up_left_mem (i2 := x.val.1) (j2 := x.val.2)
      (by have := p.1.isLt; omega) (by have := p.2.isLt; omega) x.property⟩
  have hf : Function.Injective f := by
    intro p q hpq
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg (fun z : Cells D => z.val.1) hpq
    · exact congrArg (fun z : Cells D => z.val.2) hpq
  simpa only [Fintype.card_prod, Fintype.card_fin] using Fintype.card_le_of_injective f hf

lemma cell_small_coord (D : YoungDiagram) (x : Cells D) :
    x.val.1 < Nat.sqrt (Fintype.card (Cells D)) ∨ x.val.2 < Nat.sqrt (Fintype.card (Cells D)) := by
  by_contra h
  push Not at h
  have hh := rectangle_card_le D x
  have hs := Nat.lt_succ_sqrt' (Fintype.card (Cells D))
  have hm := Nat.mul_le_mul (Nat.succ_le_succ h.1) (Nat.succ_le_succ h.2)
  nlinarith

lemma rowLen_le_card (D : YoungDiagram) (i : ℕ) : D.rowLen i ≤ Fintype.card (Cells D) := by
  rw [← card_row_subtype D i]
  exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective

lemma colLen_le_card (D : YoungDiagram) (j : ℕ) : D.colLen j ≤ Fintype.card (Cells D) := by
  rw [← card_column D j]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_univ)

theorem partition_count_le_sqrt_pow (n : ℕ) :
    Fintype.card (Nat.Partition n) ≤ (n + 1) ^ (2 * Nat.sqrt n) := by
  let F (p : Nat.Partition n) : (Fin (Nat.sqrt n) → Fin (n + 1)) × (Fin (Nat.sqrt n) → Fin (n + 1)) :=
    (fun i => ⟨(ofPartition p).rowLen i, by
      have := rowLen_le_card (ofPartition p) i
      rw [card_ofPartition] at this
      omega⟩,
     fun j => ⟨(ofPartition p).colLen j, by
      have := colLen_le_card (ofPartition p) j
      rw [card_ofPartition] at this
      omega⟩)
  have hf : Function.Injective F := by
    intro p q hpq
    apply ofPartition_injective
    apply YoungDiagram.ext
    ext z
    have aux (p q : Nat.Partition n) (hpq : F p = F q) (hz : z ∈ ofPartition p) : z ∈ ofPartition q := by
      have hs := cell_small_coord (ofPartition p) ⟨z, hz⟩
      rw [card_ofPartition] at hs
      rcases hs with hs | hs
      · have he := congrArg (fun v : (Fin (Nat.sqrt n) → Fin (n + 1)) × (Fin (Nat.sqrt n) → Fin (n + 1)) =>
            (v.1 ⟨z.1, hs⟩).val) hpq
        change (ofPartition p).rowLen z.1 = (ofPartition q).rowLen z.1 at he
        apply YoungDiagram.mem_iff_lt_rowLen.mpr
        rw [← he]
        exact YoungDiagram.mem_iff_lt_rowLen.mp hz
      · have he := congrArg (fun v : (Fin (Nat.sqrt n) → Fin (n + 1)) × (Fin (Nat.sqrt n) → Fin (n + 1)) =>
            (v.2 ⟨z.2, hs⟩).val) hpq
        change (ofPartition p).colLen z.2 = (ofPartition q).colLen z.2 at he
        apply YoungDiagram.mem_iff_lt_colLen.mpr
        rw [← he]
        exact YoungDiagram.mem_iff_lt_colLen.mp hz
    exact ⟨aux p q hpq, aux q p hpq.symm⟩
  have hh := Fintype.card_le_of_injective F hf
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, two_mul, pow_add] using hh

end Thorp.Young

namespace Thorp.Young
open scoped Classical

end Thorp.Young

end

end OAI

-- ---- platform node ----
open OAI OAI.Thorp OAI.Thorp.Young
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter
open scoped Classical


theorem solution : type_of% @_root_.OAI.Thorp.Young.partition_count_le_sqrt_pow := @_root_.OAI.Thorp.Young.partition_count_le_sqrt_pow
