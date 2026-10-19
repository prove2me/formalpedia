-- Prove2me | solution 2 for OAI.CriticalZ3.Box.successBits_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:28:19.402049+00:00
-- url     : https://prove2.me/submissions/968db44e-25be-4b57-8413-8ee37176fa20

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/SeedTrials.lean:L88-L110
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.Box.successBits_disjoint. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials

-- ---- from OAI.Probability.CriticalZ3.BoxGeometry ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3

open Classical

namespace Box

theorem neighbor_coordinates {x y : Vertex} (h : NearestNeighbor x y) :
    ∃ i, |y i-x i| = 1 ∧ ∀ k, k ≠ i → y k = x k := by
  obtain ⟨i, h | h⟩ := h
  · subst y
    refine ⟨i,by simp [step],?_⟩
    intro k hk
    simp [step,Ne.symm hk]
  · subst x
    refine ⟨i,by simp [step],?_⟩
    intro k hk
    simp [step,Ne.symm hk]

theorem neighbor_distance {x y : Vertex} (h : NearestNeighbor x y) (i : Fin 3) :
    |y i-x i| ≤ 1 := by
  obtain ⟨k,hk,he⟩ := neighbor_coordinates h
  by_cases hik : i = k
  · simp [hik,hk]
  · simp [he i hik]

theorem seed_contains_entry (C : Box) (m : ℕ)
    (hw : ∀ i, C.lower i+m ≤ C.upper i-m) {z : Vertex} (hz : C.Contains z) :
    (cube (C.seedCenter m z) m).Contains z := by
  rw [contains_cube]
  intro i
  have hi := hz i
  have hwi := hw i
  dsimp [seedCenter]
  rw [abs_le]
  omega

theorem seed_center_near (C : Box) (m : ℕ)
    (hw : ∀ i, C.lower i+m ≤ C.upper i-m) {z y : Vertex}
    (hz : C.Contains z) (hyz : NearestNeighbor y z) (i : Fin 3) :
    |C.seedCenter m z i-y i| ≤ (m : ℤ)+1 := by
  have h1 := (contains_cube _ _ _).mp (C.seed_contains_entry m hw hz) i
  have h2 := neighbor_distance hyz i
  rw [abs_le] at h1 h2 ⊢
  omega

theorem disjoint_seeds {a b : Vertex} {m : ℕ}
    (h : ∃ i, (2*m : ℤ) < |a i-b i|) :
    Disjoint (cube a m).vertices (cube b m).vertices := by
  rw [Finset.disjoint_left]
  intro x hxa hxb
  obtain ⟨i,hi⟩ := h
  have ha := (contains_cube _ _ _).mp ((mem_vertices _ _).mp hxa) i
  have hb := (contains_cube _ _ _).mp ((mem_vertices _ _).mp hxb) i
  rw [abs_le] at ha hb
  have hab : |a i-b i| ≤ 2*m := by rw [abs_le]; omega
  omega

theorem separated_centers (C : Box) (m : ℕ)
    (hw : ∀ i, C.lower i+m ≤ C.upper i-m) {y y' z z' : Vertex}
    (hz : C.Contains z) (hz' : C.Contains z')
    (hy : NearestNeighbor y z) (hy' : NearestNeighbor y' z')
    (hsep : ∃ i, (4*m+2 : ℤ) < |y i-y' i|) :
    ∃ i, (2*m : ℤ) < |C.seedCenter m z i-C.seedCenter m z' i| := by
  obtain ⟨i,hi⟩ := hsep
  refine ⟨i,?_⟩
  have h1 := C.seed_center_near m hw hz hy i
  have h2 := C.seed_center_near m hw hz' hy' i
  by_contra! hbad
  rw [abs_le] at h1 h2 hbad
  have hh : |y i-y' i| ≤ 4*m+2 := by rw [abs_le]; omega
  omega

end Box
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.EntryLayers ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical

theorem neighborBond_incidence {x y : Vertex} (h : NearestNeighbor x y) :
    Incidence (neighborBond x y) x y := by
  simp only [neighborBond,dite_eq_left h]
  exact (LatticeGraph.neighbor_incidence h).choose_spec

namespace Box

theorem entry_spec {C : Box} {y : Vertex} (h : C.Exterior y) :
    C.Contains (C.entry y) ∧ NearestNeighbor y (C.entry y) := by
  simp only [entry,dite_eq_left h]
  exact h.2.choose_spec

end Box

namespace LatticeGraph
variable (G : LatticeGraph)

end LatticeGraph
end CriticalZ3

namespace CriticalZ3.LatticeGraph
open Classical
variable (G : LatticeGraph)

end CriticalZ3.LatticeGraph

end OAI

-- ---- from OAI.Probability.CriticalZ3.SeedTrials ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical
namespace Box

theorem disjoint_bits (m : Model) {B C : Box} (h : Disjoint B.vertices C.vertices) :
    Disjoint (B.bits m) (C.bits m) := by
  rw [Finset.disjoint_left] at h ⊢
  intro e he he'
  cases m
  · exact h ((mem_vertices B e.1).mpr ((mem_bonds B e).mp he).1)
      ((mem_vertices C e.1).mpr ((mem_bonds C e).mp he').1)
  · exact h he he'

theorem crossing_not_internal {C : Box} {y : Vertex} (hy : C.Exterior y) :
    C.entryBit .bond y ∉ C.bonds := by
  intro he
  obtain ⟨h0,h1⟩ := (mem_bonds C _).mp he
  have hi := neighborBond_incidence (entry_spec hy).2
  rcases hi with ⟨hx,_⟩ | ⟨_,hx⟩
  · exact hy.1 (hx ▸ h0)
  · exact hy.1 (hx ▸ h1)

theorem crossing_injective {C : Box} {y z : Vertex} (hy : C.Exterior y) (hz : C.Exterior z)
    (he : C.entryBit .bond y = C.entryBit .bond z) : y = z := by
  have hi := neighborBond_incidence (entry_spec hy).2
  have hj := neighborBond_incidence (entry_spec hz).2
  change Incidence (C.entryBit .bond y) y (C.entry y) at hi
  change Incidence (C.entryBit .bond z) z (C.entry z) at hj
  rw [←he] at hj
  rcases hi with ⟨hy0,hy1⟩ | ⟨hy1,hy0⟩ <;>
    rcases hj with ⟨hz0,hz1⟩ | ⟨hz1,hz0⟩
  · exact hy0.trans hz0.symm
  · exact False.elim (hy.1 ((hy0.trans hz1.symm).symm ▸ (entry_spec hz).1))
  · exact False.elim (hy.1 ((hy0.trans hz1.symm).symm ▸ (entry_spec hz).1))
  · exact hy0.trans hz0.symm

theorem successBits_disjoint (C : Box) (r : ℕ) (m : Model)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) {y z : Vertex}
    (hy : C.Exterior y) (hz : C.Exterior z) (hsep : ∃ i, (4*r+2 : ℤ) < |y i-z i|) :
    Disjoint (C.successBits r m y) (C.successBits r m z) := by
  have hcent := C.separated_centers r hw (entry_spec hy).1 (entry_spec hz).1
    (entry_spec hy).2 (entry_spec hz).2 hsep
  have hseed := disjoint_bits m (disjoint_seeds hcent)
  have hyz : y ≠ z := by
    intro he
    obtain ⟨i,hi⟩ := hsep
    rw [he,sub_self,abs_zero] at hi
    omega
  cases m
  · apply Finset.disjoint_left.mpr
    intro e he he'
    rcases Finset.mem_insert.mp he with he | he <;> rcases Finset.mem_insert.mp he' with he' | he'
    · exact hyz (C.crossing_injective hy hz (he.symm.trans he'))
    · subst e
      exact C.crossing_not_internal hy (bits_mono .bond (C.seedBox_contained r hw z) he')
    · subst e
      exact C.crossing_not_internal hz (bits_mono .bond (C.seedBox_contained r hw y) he)
    · exact Finset.disjoint_left.mp hseed he he'
  · exact hseed

end Box

namespace LatticeGraph
variable (G : LatticeGraph)

end LatticeGraph
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.Box
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical


theorem solution : type_of% @_root_.OAI.CriticalZ3.Box.successBits_disjoint := @_root_.OAI.CriticalZ3.Box.successBits_disjoint
