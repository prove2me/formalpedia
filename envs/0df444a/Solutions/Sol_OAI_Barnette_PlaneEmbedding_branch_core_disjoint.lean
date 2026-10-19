-- Prove2me | solution 1 for OAI.Barnette.PlaneEmbedding.branch_core_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:04:56.611562+00:00
-- url     : https://prove2.me/submissions/fba42ac0-b5a2-4af3-b5be-5d7259d3f827

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Traces.lean:L156-L179
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.PlaneEmbedding.branch_core_disjoint. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BarnetteHamiltonian
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Network
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CutSpaces
import Definitions.Def_OAI_Combinatorics_Hamiltonian_FlowCircuits
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Bonds
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Quotients
import Definitions.Def_OAI_Combinatorics_Hamiltonian_DiskRegions
import Definitions.Def_OAI_Combinatorics_Hamiltonian_StateDisk
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Circulation
import Definitions.Def_OAI_Combinatorics_Hamiltonian_TriangleSystem
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ColoredDual
import Definitions.Def_OAI_Combinatorics_Hamiltonian_CycleReversal
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPhases
import Definitions.Def_OAI_Combinatorics_Hamiltonian_PairPolynomials
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Forest
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Contraction
import Definitions.Def_OAI_Combinatorics_Hamiltonian_MinorDuality
import Definitions.Def_OAI_Combinatorics_Hamiltonian_BMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Matching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ForestMatching
import Definitions.Def_OAI_Combinatorics_Hamiltonian_ThreeCuts
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Gluing
import Definitions.Def_OAI_Combinatorics_Hamiltonian_Traces

-- ---- from OAI.Combinatorics.Hamiltonian.Traces ----
namespace OAI

/-! Compact connected arc traces and uniform positive thickenings. -/

namespace Barnette.PlaneEmbedding

noncomputable section

variable {V : Type*} {G : SimpleGraph V} (E : PlaneEmbedding G)

theorem curve_eq_point_iff (d : G.Dart) (t : unitInterval) (v : V) :
    E.curve d t = E.point v ↔ (t = 0 ∧ v = d.fst) ∨ (t = 1 ∧ v = d.snd) := by
  constructor
  · exact E.arc_avoids_vertices d.fst d.snd d.adj t v
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

theorem curve_eq_curve_interior {d e : G.Dart} {t s : unitInterval}
    (ht₀ : t ≠ 0) (ht₁ : t ≠ 1) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1)
    (h : E.curve d t = E.curve e s) : d = e ∨ d = e.symm := by
  rcases E.interiors_disjoint d.fst d.snd e.fst e.snd d.adj e.adj
    t s ht₀ ht₁ hs₀ hs₁ h with h | h
  · exact Or.inl (SimpleGraph.Dart.ext _ _ (Prod.ext h.1 h.2))
  · exact Or.inr (SimpleGraph.Dart.ext _ _ (Prod.ext h.1 h.2))

private theorem middle_nonendpoint {t : unitInterval} (ht : t ∈ Set.Icc third twoThirds) :
    t ≠ 0 ∧ t ≠ 1 := by
  constructor
  · intro h
    have hh : (1 : ℝ) / 3 ≤ t := ht.1
    rw [h] at hh
    norm_num at hh
  · intro h
    have hh : (t : ℝ) ≤ 2 / 3 := ht.2
    rw [h] at hh
    norm_num at hh

theorem core_avoids_vertices (d : G.Dart) (v : V) : E.point v ∉ E.core d := by
  rintro ⟨t, ht, heq⟩
  have hn := middle_nonendpoint ht
  rcases (E.curve_eq_point_iff d t v).mp heq with h | h
  · exact hn.1 h.1
  · exact hn.2 h.1

theorem branch_core_disjoint {v : V} {e : G.Dart}
    (hv₁ : v ≠ e.fst) (hv₂ : v ≠ e.snd) : Disjoint (E.branch v) (E.core e) := by
  rw [Set.disjoint_left]
  intro p hp hq
  rcases hp with hp | hp
  · exact E.core_avoids_vertices e v (hp ▸ hq)
  obtain ⟨⟨d, hd⟩, t, ht, heq⟩ := Set.mem_iUnion.mp hp
  obtain ⟨s, hs, heq'⟩ := hq
  have h : E.curve d t = E.curve e s := heq.trans heq'.symm
  obtain ⟨hs₀, hs₁⟩ := middle_nonendpoint hs
  have ht₁ : t ≠ 1 := by
    intro heq
    have hh : (t : ℝ) ≤ 1 / 3 := ht.2
    rw [heq] at hh
    norm_num at hh
  by_cases ht₀ : t = 0
  · subst t
    rw [E.curve_zero] at h
    rcases (E.curve_eq_point_iff e s d.fst).mp h.symm with h | h
    · exact hs₀ h.1
    · exact hs₁ h.1
  rcases E.curve_eq_curve_interior ht₀ ht₁ hs₀ hs₁ h with h | h
  · exact hv₁ (hd.symm.trans (congrArg (fun d : G.Dart => d.fst) h))
  · exact hv₂ (hd.symm.trans (congrArg (fun d : G.Dart => d.fst) h))

end
end Barnette.PlaneEmbedding

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.PlaneEmbedding


theorem solution : type_of% @_root_.OAI.Barnette.PlaneEmbedding.branch_core_disjoint := @_root_.OAI.Barnette.PlaneEmbedding.branch_core_disjoint
