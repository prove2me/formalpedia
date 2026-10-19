-- Prove2me | solution 2 for OAI.C0Absorption.constant_or_injective_subsequence
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:13:41.337739+00:00
-- url     : https://prove2.me/submissions/09915c52-a580-424e-8395-230d23ac223c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Selection.lean:L33-L47
-- (upload_full_project.md Phase 4): solution for node OAI.C0Absorption.constant_or_injective_subsequence. The node keeps its source
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

theorem thin_sequence {r : ℕ → ℕ → Prop} (hr : ∀ i, ∀ᶠ j in atTop, r i j) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i j, i < j → r (φ i) (φ j) := by
  have he (t : Set ℕ) (ht : t.Finite) : ∀ᶠ j in atTop, ∀ i ∈ t, i<j ∧ r i j :=
    (eventually_all_finite ht).mpr (fun i _ => (eventually_gt_atTop i).and (hr i))
  obtain ⟨φ,hφ⟩ := seq_of_forall_finite_exists (fun t ht => (he t ht).exists)
  simp only [forall_mem_image, forall_and, mem_Iio] at hφ
  exact ⟨φ, forall_comm.mp hφ.1, forall_comm.mp hφ.2⟩

theorem constant_or_injective_subsequence {A : Type*} (f : ℕ → A) :
    (∃ a, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, f (φ i)=a) ∨
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ Function.Injective (f ∘ φ)) := by
  by_cases h : ∃ a, ∃ᶠ i in atTop, f i=a
  · obtain ⟨a,ha⟩ := h
    obtain ⟨φ,hm,hp⟩ := extraction_of_frequently_atTop ha
    exact Or.inl ⟨a,φ,hm,hp⟩
  · push Not at h
    obtain ⟨φ,hm,hp⟩ := thin_sequence (r := fun i j => f i≠f j) (fun i => by
      simpa only [ne_eq, eq_comm] using h (f i))
    refine Or.inr ⟨φ,hm,?_⟩
    intro i j hij
    apply le_antisymm <;> by_contra hn
    · exact hp j i (lt_of_not_ge hn) hij.symm
    · exact hp i j (lt_of_not_ge hn) hij

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


theorem solution : type_of% @_root_.OAI.C0Absorption.constant_or_injective_subsequence := @_root_.OAI.C0Absorption.constant_or_injective_subsequence
