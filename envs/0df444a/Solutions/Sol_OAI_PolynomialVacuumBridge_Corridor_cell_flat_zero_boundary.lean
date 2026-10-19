-- Prove2me | solution 1 for OAI.PolynomialVacuumBridge.Corridor.cell_flat_zero_boundary
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T12:38:34.29899+00:00
-- url     : https://prove2.me/submissions/e2951532-4dae-47bf-aa57-1cad9422efd3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/HoneycombCorridor/PotentialSupport.lean:L169-L187
-- (upload_full_project.md Phase 4): solution for node OAI.PolynomialVacuumBridge.Corridor.cell_flat_zero_boundary. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport
import Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_nonboundary_vertex_all_edges

-- ---- from OAI.Combinatorics.HoneycombCorridor.PotentialSupport ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

theorem finite_vertex_flat_zero (f : Vertex →₀ ℚ)
    (hf : ∀ v k, f (neighbor v k) = f v) : f = 0 := by
  classical
  let row : Vertex → ℤ := fun v => match v with | .up _ j => j | .down _ j => j
  let M : ℕ := f.support.sup fun v => (row v).natAbs
  have hu (i j : ℤ) : f (.up i j) = 0 := by
    have hh (k : ℤ) : f (.up i (k+1)) = f (.up i k) := by
      have h0 := hf (.down i k) 0
      have h1 := hf (.down i k) 1
      simp only [neighbor,↓reduceIte,Fin.isValue] at h0 h1
      exact h0.trans h1.symm
    let k : ℤ := (M : ℤ) + 1
    have he := QFlow.int_function_constant (f := fun j => f (.up i j)) hh j k
    rw [he]
    by_contra hk
    have hb : (row (.up i k)).natAbs ≤ M :=
      Finset.le_sup (f := fun v : Vertex => (row v).natAbs)
        (Finsupp.mem_support_iff.mpr hk)
    dsimp [row,k] at hb
    omega
  ext v
  cases v with
  | up i j => exact hu i j
  | down i j =>
      have h := hf (.down i j) 1
      simpa [neighbor,hu] using h.symm

theorem flat_along_dart (S : Finset FaceIndex) (f : Vertex → ℚ)
    (hf : ∀ e ∈ cellEdges S, f (upEnd e) = f (downEnd e))
    (g : Germ) (h : edgeOf g ∈ cellEdges S) : f (neighbor g.1 g.2) = f g.1 := by
  have he := hf (edgeOf g) h
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;>
    simp [edgeOf,upEnd,downEnd,neighbor] at he ⊢ <;> first | exact he.symm | exact he

theorem cell_flat_zero_boundary (g : Germ) (w : List Bool)
    (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w))
    (f : Vertex →₀ ℚ) (hS : f.support ⊆ cellVertices p.support)
    (hflat : ∀ e ∈ cellEdges p.support, f (upEnd e) = f (downEnd e))
    (hbd : ∀ v ∈ traced g w, f v = 0) : f = 0 := by
  apply finite_vertex_flat_zero
  intro v k
  by_cases he : edgeOf (v,k) ∈ cellEdges p.support
  · exact flat_along_dart _ f hflat (v,k) he
  · have hz (d : Germ) (h : edgeOf d ∉ cellEdges p.support) : f d.1 = 0 := by
      by_cases hV : d.1 ∈ cellVertices p.support
      · apply hbd
        by_contra hnot
        exact h (nonboundary_vertex_all_edges g w hc p hp d.1 hV hnot d.2)
      · by_contra hne
        exact hV (hS (Finsupp.mem_support_iff.mpr hne))
    rw [hz (v,k) he]
    exact hz (reverseGerm (v,k)) (by simpa using he)

end PolynomialVacuumBridge.Corridor

end

end OAI

-- ---- platform node ----
open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor


theorem solution : type_of% @_root_.OAI.PolynomialVacuumBridge.Corridor.cell_flat_zero_boundary := @_root_.OAI.PolynomialVacuumBridge.Corridor.cell_flat_zero_boundary
