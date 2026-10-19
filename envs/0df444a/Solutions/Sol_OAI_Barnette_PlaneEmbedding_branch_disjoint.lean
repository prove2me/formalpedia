-- Prove2me | solution 1 for OAI.Barnette.PlaneEmbedding.branch_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T05:03:06.873657+00:00
-- url     : https://prove2.me/submissions/7b3d99de-dca5-469b-891e-341f2248efbf

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Hamiltonian/Traces.lean:L103-L125
-- (upload_full_project.md Phase 4): solution for node OAI.Barnette.PlaneEmbedding.branch_disjoint. The node keeps its source
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

theorem curve_injective (d : G.Dart) : Function.Injective (E.curve d) :=
  E.arc_injective d.fst d.snd d.adj

theorem curve_symm (d : G.Dart) (t : unitInterval) :
    E.curve d.symm t = E.curve d (unitInterval.symm t) := by
  change E.arc d.snd d.fst d.adj.symm t = _
  rw [E.arc_reverse]
  rfl

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

private theorem initial_meeting {d e : G.Dart} {t s : unitInterval}
    (ht : (t : ℝ) ≤ 1 / 3) (hs : (s : ℝ) ≤ 1 / 3)
    (h : E.curve d t = E.curve e s) : d.fst = e.fst := by
  have ht₁ : t ≠ 1 := by intro heq; subst t; norm_num at ht
  have hs₁ : s ≠ 1 := by intro heq; subst s; norm_num at hs
  by_cases ht₀ : t = 0
  · subst t
    rw [E.curve_zero] at h
    rcases (E.curve_eq_point_iff e s d.fst).mp h.symm with h | h
    · exact h.2
    · exact (hs₁ h.1).elim
  by_cases hs₀ : s = 0
  · subst s
    rw [E.curve_zero] at h
    rcases (E.curve_eq_point_iff d t e.fst).mp h with h | h
    · exact h.2.symm
    · exact (ht₁ h.1).elim
  rcases E.curve_eq_curve_interior ht₀ ht₁ hs₀ hs₁ h with heq | heq
  · exact congrArg (fun d : G.Dart => d.fst) heq
  · subst d
    rw [E.curve_symm] at h
    have hp := congrArg Subtype.val (E.curve_injective e h)
    simp only [unitInterval.coe_symm_eq] at hp
    linarith

theorem branch_disjoint {v w : V} (hvw : v ≠ w) :
    Disjoint (E.branch v) (E.branch w) := by
  rw [Set.disjoint_left]
  intro p hp hq
  rcases hp with hp | hp <;> rcases hq with hq | hq
  · exact hvw (E.point_injective (hp.symm.trans hq))
  · obtain ⟨⟨d, hd⟩, t, ht, heq⟩ := Set.mem_iUnion.mp hq
    have ha : E.curve d t = E.point v := heq.trans hp
    rcases (E.curve_eq_point_iff d t v).mp ha with ha | ha
    · exact hvw (ha.2.trans hd)
    · have : (1 : unitInterval) ≤ third := ha.1 ▸ ht.2
      change (1 : ℝ) ≤ 1 / 3 at this
      norm_num at this
  · obtain ⟨⟨d, hd⟩, t, ht, heq⟩ := Set.mem_iUnion.mp hp
    have ha : E.curve d t = E.point w := heq.trans hq
    rcases (E.curve_eq_point_iff d t w).mp ha with ha | ha
    · exact hvw (hd.symm.trans ha.2.symm)
    · have : (1 : unitInterval) ≤ third := ha.1 ▸ ht.2
      change (1 : ℝ) ≤ 1 / 3 at this
      norm_num at this
  · obtain ⟨⟨d, hd⟩, t, ht, heq⟩ := Set.mem_iUnion.mp hp
    obtain ⟨⟨e, he⟩, s, hs, heq'⟩ := Set.mem_iUnion.mp hq
    exact hvw (hd.symm.trans ((E.initial_meeting ht.2 hs.2 (heq.trans heq'.symm)).trans he))

end
end Barnette.PlaneEmbedding

end OAI

-- ---- platform node ----
open OAI OAI.Barnette OAI.Barnette.PlaneEmbedding


theorem solution : type_of% @_root_.OAI.Barnette.PlaneEmbedding.branch_disjoint := @_root_.OAI.Barnette.PlaneEmbedding.branch_disjoint
