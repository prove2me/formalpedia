-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.strict_deficit_of_augmentation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:43:04.224979+00:00
-- url     : https://prove2.me/submissions/0ea936ed-d7d3-42a4-bab6-0429c693cf87

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/SubsetAugmentation.lean:L11-L56
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.strict_deficit_of_augmentation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.Tauto
import Definitions.Def_SeymourSecondNeighborhood
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Basic
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_ReductionCore
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Reindex
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_MinimalCounterexample

-- ---- from OAI.Combinatorics.SecondNeighborhood.SubsetAugmentation ----
namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*} [DecidableEq V]

theorem strict_deficit_of_augmentation (E : Finset V) (hE : E.Nonempty)
    (g : Finset V → ℕ) (hempty : g ∅ = 0)
    (step : ∀ T : Finset V, T ⊆ E → T ≠ E →
      ∃ Q : Finset V, Q.Nonempty ∧ Q ⊆ E \ T ∧
        g (T ∪ Q) < g T + Q.card) :
    g E < E.card := by
  classical
  let feasible := E.powerset.filter fun T => T = ∅ ∨ g T < T.card
  have hfeasible : feasible.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [feasible]
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image feasible Finset.card hfeasible
  have hTE : T ⊆ E := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
  have hinvariant : T = ∅ ∨ g T < T.card := (Finset.mem_filter.mp hT).2
  have hgle : g T ≤ T.card := by
    rcases hinvariant with ht | ht
    · subst T
      simp [hempty]
    · exact Nat.le_of_lt ht
  have heq : T = E := by
    by_contra hne
    obtain ⟨Q, hQnonempty, hQ, hstep⟩ := step T hTE hne
    have hdisjoint : Disjoint T Q := by
      apply Finset.disjoint_left.mpr
      intro v hvT hvQ
      exact (Finset.mem_sdiff.mp (hQ hvQ)).2 hvT
    have hcard : (T ∪ Q).card = T.card + Q.card :=
      Finset.card_union_of_disjoint hdisjoint
    have hunion : T ∪ Q ⊆ E := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact hTE hv
      · exact (Finset.mem_sdiff.mp (hQ hv)).1
    have hstrict : g (T ∪ Q) < (T ∪ Q).card := by
      rw [hcard]
      omega
    have hnew : T ∪ Q ∈ feasible := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_powerset.mpr hunion, Or.inr hstrict⟩
    have hmax' := hmax (T ∪ Q) hnew
    have hpos : 0 < Q.card := Finset.card_pos.mpr hQnonempty
    omega
  rcases hinvariant with hempty' | hstrict
  · have : E = ∅ := heq.symm.trans hempty'
    exact (hE.ne_empty this).elim
  · simpa only [heq] using hstrict

end SeymourSecondNeighborhood

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.strict_deficit_of_augmentation := @_root_.OAI.SeymourSecondNeighborhood.strict_deficit_of_augmentation
