-- Prove2me | solution 2 for OAI.C0Absorption.nat_constant_or_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:15:01.455125+00:00
-- url     : https://prove2.me/submissions/10e2f159-cb05-458c-8075-3b08c5249a5a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Selection.lean:L49-L64
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.nat_constant_or_tendsto. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection

-- ---- from OAI.Analysis.C0Absorption.Selection ----
namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology

theorem nat_constant_or_tendsto (f : ℕ → ℕ) :
    (∃ a, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, f (φ i)=a) ∨
    Tendsto f atTop atTop := by
  by_cases h : ∃ a, ∃ᶠ i in atTop, f i=a
  · obtain ⟨a,ha⟩ := h
    obtain ⟨φ,hm,hp⟩ := extraction_of_frequently_atTop ha
    exact Or.inl ⟨a,φ,hm,hp⟩
  · push Not at h
    apply Or.inr
    apply tendsto_atTop.mpr
    intro N
    have hh : ∀ᶠ i in atTop, ∀ a ∈ Finset.range N, f i≠a :=
      (eventually_all_finite (Finset.range N).finite_toSet).mpr (fun a _ => h a)
    filter_upwards [hh] with i hi
    by_contra hn
    exact hi (f i) (Finset.mem_range.mpr (lt_of_not_ge hn)) rfl

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

namespace TagLocalization
variable {Γ : Type*} {B : CylinderBases Γ} (loc : TagLocalization B)

end TagLocalization

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

end
end C0Absorption

end OAI

-- ---- platform node ----
open OAI OAI.C0Absorption
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace
open Set Filter Topology


theorem solution : type_of% @_root_.OAI.C0Absorption.nat_constant_or_tendsto := @_root_.OAI.C0Absorption.nat_constant_or_tendsto
