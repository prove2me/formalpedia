-- Prove2me | solution 1 for OAI.Release075.MarkedLineData.presentation_not_residuallyFinite
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:37:44.561984+00:00
-- url     : https://prove2.me/submissions/bf94e31f-b9eb-4dd9-9433-7bf07dea2cdd

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/Presentation.lean:L467-L482
-- (upload_full_project.md Phase 4): solution for node OAI.Release075.MarkedLineData.presentation_not_residuallyFinite. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Theorems.Thm_OAI_Release075_not_residuallyFinite_of_line_blocks

-- ---- from OAI.GroupTheory.Hyperbolic.Incidence ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace Release075
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

section ProjectiveLines
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end ProjectiveLines

section CycleCount
variable {A K V : Type*} [Field K] [AddCommGroup V] [Module K V]

namespace CycleCandidate
variable {S : Finset V} {σ : A → A}

end CycleCandidate

end CycleCount

section Degrees
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype (Projectivization K V)] [Nontrivial V]

end Degrees

section EncodingIncidence
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

end EncodingIncidence

section Alteration
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable [Fintype K] [Fintype V]

end Alteration

section Exceptional
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Fintype V]

end Exceptional

section AlterationMean
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Fintype V] [Nontrivial V] [Fintype (Projectivization K V)]

end AlterationMean

section DimensionTwenty
variable (q : ℕ) [Fact q.Prime]

variable [Fintype (Projectivization (ZMod q) (Fin 20 → ZMod q))]

end DimensionTwenty

attribute [instance] MarkedLineData.labelFintype

namespace MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

theorem degree_cutoff (hq : 200 ≤ q) : 2*(20*(d.scalarGrid.card-1)) < q-1 := by
  rw [d.grid_card]
  omega
end MarkedLineData

end
end Release075

end OAI

-- ---- from OAI.GroupTheory.Hyperbolic.Presentation ----
namespace OAI

namespace Release075

namespace ShiftScheme
variable {I P B : Type*} {r : ℕ} {inc : P → Finset I} (d : ShiftScheme I P B r inc)

end ShiftScheme

end Release075

namespace Release075

namespace BlockPresentation
variable {I B : Type*} {r : ℕ} (d : BlockPresentation I B r)

theorem block_relations (b : B) : (d.block b).Relations d.x :=
  ⟨d.l b,d.rr b,d.triangle_relation b⟩

end BlockPresentation

namespace BlockPresentation
variable {I B : Type*} {r : ℕ} (d : BlockPresentation I B r)

end BlockPresentation
end Release075

namespace Release075
noncomputable section
open scoped BigOperators
attribute [local instance] OAI.Release075.instDecidableEq_oAI
namespace MarkedLineData
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r)

/-- The complete finite-quotient argument applied to the actual fixed
presentation. The geometric nontriviality premise is established below. -/
theorem presentation_not_residuallyFinite (hr : 0 < r) (hq : r < q) (hq200 : 200 ≤ q)
    (hrect : d.RectangularNontriviality hr) :
    ¬ Group.ResiduallyFinite (d.presentation hr).GroupType := by
  classical
  apply not_residuallyFinite_of_line_blocks r q hq d.scalarGrid d.mark
    (fun i => (d.direction i).rep) d.marks_mem d.marks_injective
    (fun i => (d.direction i).rep_nonzero) (by simpa only [Fintype.card_fin] using d.degree_cutoff hq200)
    d.exceptional (d.presentation hr).x hrect _ (by
      simpa only [Fintype.card_fun,Fintype.card_fin,ZMod.card] using d.budget)
  intro z hz
  let p := d.partition hr ⟨z,hz⟩
  refine ⟨p.zero,p.one,p.disjoint,p.cover,?_,?_⟩
  · exact (d.presentation hr).block_relations (⟨z,hz⟩,false)
  · exact (d.presentation hr).block_relations (⟨z,hz⟩,true)

end MarkedLineData

end
end Release075

end OAI

-- ---- platform node ----
open OAI OAI.Release075 OAI.Release075.MarkedLineData
open scoped BigOperators
attribute [local instance] OAI.Release075.instDecidableEq_oAI


theorem solution : type_of% @_root_.OAI.Release075.MarkedLineData.presentation_not_residuallyFinite := @_root_.OAI.Release075.MarkedLineData.presentation_not_residuallyFinite
