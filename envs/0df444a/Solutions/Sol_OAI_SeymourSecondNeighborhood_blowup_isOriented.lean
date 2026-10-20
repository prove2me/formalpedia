-- Prove2me | solution 1 for OAI.SeymourSecondNeighborhood.blowup_isOriented
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T12:46:59.001551+00:00
-- url     : https://prove2.me/submissions/2837b6de-6d35-465b-b1e7-5dfc63cdbcbd

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SecondNeighborhood/TransitiveBlowup.lean:L13-L29
-- (upload_full_project.md Phase 4): solution for node OAI.SeymourSecondNeighborhood.blowup_isOriented. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_Deletion
import Definitions.Def_OAI_Combinatorics_SecondNeighborhood_TransitiveBlowup

-- ---- from OAI.Combinatorics.SecondNeighborhood.TransitiveBlowup ----
namespace OAI

namespace SeymourSecondNeighborhood

variable {V : Type*}

theorem blowup_isOriented {r : V → V → Prop} (hr : IsOriented r) (m : ℕ) :
    IsOriented (blowup r m) := by
  constructor
  · intro p hp
    rcases hp with hp | ⟨_, hp⟩
    · exact hr.loopless p.1 hp
    · exact (lt_irrefl p.2) hp
  · intro p q hpq hqp
    rcases hpq with hpq | ⟨heq, hlt⟩
    · rcases hqp with hqp | ⟨heq, _⟩
      · exact hr.asymmetric hpq hqp
      · apply hr.loopless p.1
        simpa only [heq] using hpq
    · rcases hqp with hqp | ⟨_, hgt⟩
      · apply hr.loopless q.1
        simpa only [heq] using hqp
      · exact (not_lt_of_gt hlt) hgt

variable [Fintype V] [DecidableEq V]

end SeymourSecondNeighborhood

end OAI

-- ---- platform node ----
open OAI OAI.SeymourSecondNeighborhood


theorem solution : type_of% @_root_.OAI.SeymourSecondNeighborhood.blowup_isOriented := @_root_.OAI.SeymourSecondNeighborhood.blowup_isOriented
