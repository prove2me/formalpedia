-- Prove2me | solution 1 for OAI.Thorp.Specht.defect_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:16:16.842998+00:00
-- url     : https://prove2.me/submissions/987fcd06-693e-4e92-acda-6f28dac8c3fa

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/DegreeBounds.lean:L219-L232
-- (upload_full_project.md Phase 4): solution for node OAI.Thorp.Specht.defect_card_bound. The node keeps its source
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
import Definitions.Def_OAI_Probability_ThorpShuffle_DegreeBounds

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

lemma of_toPartition (D : YoungDiagram) (n : ℕ) (hn : Fintype.card (Cells D) = n) :
    ofPartition (toPartition D n hn) = D := by
  have hs : (D.rowLens : Multiset ℕ).sort (· ≥ ·) = D.rowLens := by
    rw [Multiset.coe_sort]
    exact List.mergeSort_eq_self _ D.rowLens_sorted.pairwise
  unfold ofPartition toPartition
  simp only [hs]
  exact YoungDiagram.ofRowLens_to_rowLens_eq_self

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

-- ---- from OAI.Probability.ThorpShuffle.ExtensionBounds ----
namespace OAI

universe uA

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical
variable {A : Type uA} [Fintype A] [PartialOrder A]

end Thorp.Young

namespace Thorp.Young
open scoped Classical
variable {A : Type uA} [Fintype A] [PartialOrder A]

end Thorp.Young

namespace Thorp.Young
open scoped Classical

lemma card_lower_add (D : YoungDiagram) :
    D.rowLen 0 + Fintype.card (Lower D) = Fintype.card (Cells D) := by
  have h := Fintype.card_congr (Equiv.sumCompl (fun x : Cells D => x.val.1 = 0))
  simpa only [Fintype.card_sum, card_row_subtype] using h

end Thorp.Young

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

lemma partition_count_le_pow (n : ℕ) : Fintype.card (Nat.Partition n) ≤ 2 ^ n := by
  have h := Fintype.card_le_of_surjective (Nat.Partition.ofComposition n) Nat.Partition.ofComposition_surj
  rw [composition_card] at h
  exact h.trans (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))

lemma rowLen_le_card (D : YoungDiagram) (i : ℕ) : D.rowLen i ≤ Fintype.card (Cells D) := by
  rw [← card_row_subtype D i]
  exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective

lemma colLen_le_card (D : YoungDiagram) (j : ℕ) : D.colLen j ≤ Fintype.card (Cells D) := by
  rw [← card_column D j]
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_univ)

end Thorp.Young

namespace Thorp.Young
open scoped Classical

end Thorp.Young

end

end OAI

-- ---- from OAI.Probability.ThorpShuffle.DegreeBounds ----
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

lemma rowTail_ext {D E : YoungDiagram} (hrow : D.rowLen 0 = E.rowLen 0) (ht : rowTail D = rowTail E) : D = E := by
  apply YoungDiagram.ext
  ext p
  rcases p with ⟨i, j⟩
  cases i with
  | zero => simp only [YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen, hrow]
  | succ i => simp only [YoungDiagram.mem_cells, ← mem_rowTail, ht]

lemma orient_rowLen (D : YoungDiagram) : (orient D).rowLen 0 = longest D := by
  unfold orient longest
  split_ifs with h
  · exact (max_eq_left h).symm
  · rw [YoungDiagram.rowLen_transpose, max_eq_right (by omega)]

lemma orient_card (D : YoungDiagram) : Fintype.card (Cells (orient D)) = Fintype.card (Cells D) := by
  unfold orient
  split_ifs
  · rfl
  · exact (Fintype.card_congr (transposeCells D).toEquiv).symm

lemma recover_orientation (D : YoungDiagram) :
    (if orientation D then orient D else (orient D).transpose) = D := by
  unfold orientation orient
  split_ifs <;> simp_all

lemma longest_le_card (D : YoungDiagram) : longest D ≤ Fintype.card (Cells D) :=
  max_le (rowLen_le_card D 0) (colLen_le_card D 0)

theorem defect_count_le (n u : ℕ) :
    Fintype.card {p : Nat.Partition n // n - longest (ofPartition p) = u} ≤
      2 * Fintype.card (Nat.Partition u) := by
  let T := {p : Nat.Partition n // n - longest (ofPartition p) = u}
  have hcard (p : T) : Fintype.card (Cells (rowTail (orient (ofPartition p.val)))) = u := by
    rw [Fintype.card_congr (rowTailCells _)]
    have hh := card_lower_add (orient (ofPartition p.val))
    rw [orient_rowLen, orient_card, card_ofPartition] at hh
    have hp := p.property
    omega
  let f (p : T) : Bool × Nat.Partition u :=
    (orientation (ofPartition p.val), toPartition (rowTail (orient (ofPartition p.val))) u (hcard p))
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply ofPartition_injective
    have hflag : orientation (ofPartition p.val) = orientation (ofPartition q.val) := congrArg Prod.fst hpq
    have ht : rowTail (orient (ofPartition p.val)) = rowTail (orient (ofPartition q.val)) := by
      have he := congrArg (fun z : Bool × Nat.Partition u => ofPartition z.2) hpq
      simpa only [f, of_toPartition] using he
    have hr : (orient (ofPartition p.val)).rowLen 0 = (orient (ofPartition q.val)).rowLen 0 := by
      simp only [orient_rowLen]
      have hp := p.property
      have hq := q.property
      have hp' := longest_le_card (ofPartition p.val)
      have hq' := longest_le_card (ofPartition q.val)
      rw [card_ofPartition] at hp' hq'
      omega
    have ho := rowTail_ext hr ht
    rw [← recover_orientation (ofPartition p.val), ← recover_orientation (ofPartition q.val), hflag, ho]
  have hh := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod, Fintype.card_bool] using hh

end Thorp.Young

namespace Thorp.Specht
open scoped Classical
open Thorp.Young

lemma defect_card_bound (n u : ℕ) :
    Fintype.card {p : NShape n // defect p = u} ≤ 2 ^ (u + 1) := by
  have hh : Nat.card {p : Nat.Partition n // n - longest (ofPartition p) = u} ≤ 2 ^ (u+1) := by
    rw [← Fintype.card_eq_nat_card]
    calc
      _ ≤ 2 * Fintype.card (Nat.Partition u) := defect_count_le n u
      _ ≤ 2 * 2^u := Nat.mul_le_mul_left 2 (partition_count_le_pow u)
      _ = _ := by ring
  rw [Fintype.card_eq_nat_card]
  change Nat.card {p : Nat.Partition (Fintype.card (Fin n)) // n - longest (ofPartition p) = u} ≤ _
  have he (m k : ℕ) (h : m = k) :
      Nat.card {p : Nat.Partition m // n - longest (ofPartition p) = u} =
      Nat.card {p : Nat.Partition k // n - longest (ofPartition p) = u} := by subst k; rfl
  exact (he _ _ (Fintype.card_fin n)).trans_le hh

end Thorp.Specht

end

end OAI

-- ---- platform node ----
open OAI OAI.Thorp OAI.Thorp.Specht
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter
open scoped Classical
open Thorp.Young


theorem solution : type_of% @_root_.OAI.Thorp.Specht.defect_card_bound := @_root_.OAI.Thorp.Specht.defect_card_bound
