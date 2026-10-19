-- Prove2me | solution 1 for OAI.Barnette.Network.flow_no_leaf
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:21:13.162816+00:00
-- url     : https://prove2.me/submissions/222e963b-daf7-47e4-81b2-fd380b152ee8

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/CutSpaces.lean:L200-L224
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.Network.flow_no_leaf. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces

-- ---- from OAI.Combinatorics.Hamiltonian.CutSpaces ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Cuts, simplicity, and connectivity of finite oriented networks. -/

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

end
end Barnette.Network

namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} (N : Network V E)

variable [Fintype V] [Fintype E]
variable {F : Type*} [Fintype F] (D : Network F E)

end
end Barnette.Network
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)

omit [Fintype V] in

lemma flow_no_leaf (hN : N.Simple) (x : E → ℝ) (hx : N.boundary x = 0)
    {e : E} {v : V} (he : x e ≠ 0) (hev : N.Incident e v) :
    ∃ f, f ≠ e ∧ x f ≠ 0 ∧ N.Incident f v := by
  by_contra hn
  have other (f : E) (hfe : f ≠ e) :
      (if N.head f = v then x f else 0) - (if N.tail f = v then x f else 0) = 0 := by
    by_cases hxf : x f = 0
    · simp [hxf]
    · have hif : ¬N.Incident f v := fun hf => hn ⟨f,hfe,hxf,hf⟩
      have hh : N.head f ≠ v := fun h => hif (Or.inr h)
      have ht : N.tail f ≠ v := fun h => hif (Or.inl h)
      simp [hh,ht]
  have hz := congrFun hx v
  rw [boundary_apply, Finset.sum_eq_single e] at hz
  · rcases hev with ht | hh
    · have hh : N.head e ≠ v := fun hh => (hN.loopless e) (ht.trans hh.symm)
      simp only [hh, ht, ite_false, ite_true, zero_sub, Pi.zero_apply, neg_eq_zero] at hz
      exact he hz
    · have ht : N.tail e ≠ v := fun ht => (hN.loopless e) (ht.trans hh.symm)
      simp only [hh, ht, ite_false, ite_true, sub_zero, Pi.zero_apply] at hz
      exact he hz
  · intro f _ hfe; exact other f hfe
  · simp

end
end Barnette.Network

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.Network
open scoped Classical


theorem solution : type_of% @_root_.OAI.Barnette.Network.flow_no_leaf := @_root_.OAI.Barnette.Network.flow_no_leaf
