-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cell_geometry_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:12:19.502077+00:00
-- url     : https://prove2.me/submissions/83099a13-3a77-48a1-bf3f-dd68b651d293

import Mathlib
import Definitions.Def_OAIQ334E011
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry00_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry01_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry02_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry04_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry05_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry06_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry09_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry10_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry11_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry12_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry13_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry14_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry15_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry16_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry17_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry18_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry19_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry20_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry21_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry22_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry23_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry24_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry25_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry26_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry27_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry28_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry29_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_SineGrid0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry03 (k : Fin 100) :
    0 ≤ cellMagnitude 3 k ∧ cellMagnitude 3 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 3 → 0 ≤ cellSeparation 3 k j ∧ cellSeparation 3 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 3 k ∧ cellMagnitude 3 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 3 → 0 ≤ cellSeparation 3 k j ∧ cellSeparation 3 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry07 (k : Fin 100) :
    0 ≤ cellMagnitude 7 k ∧ cellMagnitude 7 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 7 → 0 ≤ cellSeparation 7 k j ∧ cellSeparation 7 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 7 k ∧ cellMagnitude 7 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 7 → 0 ≤ cellSeparation 7 k j ∧ cellSeparation 7 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cellGeometry08 (k : Fin 100) :
    0 ≤ cellMagnitude 8 k ∧ cellMagnitude 8 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 8 → 0 ≤ cellSeparation 8 k j ∧ cellSeparation 8 k j≤18) := by
  exact (show ∀ k : Fin 100,
    0 ≤ cellMagnitude 8 k ∧ cellMagnitude 8 k≤3 ∧
    (∀ j : Fin 15,j≠localPivot 8 → 0 ≤ cellSeparation 8 k j ∧ cellSeparation 8 k j≤18) by decide +kernel) k
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ334_EU.Triangular_Signs_SineGridChecks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cell_geometry_eu_oai (u : Fin 30) (k : Fin 100) :
    0 ≤ cellMagnitude u k ∧ cellMagnitude u k≤3 ∧
    (∀ j : Fin 15,j≠localPivot u → 0 ≤ cellSeparation u k j ∧ cellSeparation u k j≤18) := by
  fin_cases u
  · exact cellGeometry00_eu k
  · exact cellGeometry01_eu k
  · exact cellGeometry02_eu k
  · exact cellGeometry03 k
  · exact cellGeometry04_eu k
  · exact cellGeometry05_eu k
  · exact cellGeometry06_eu k
  · exact cellGeometry07 k
  · exact cellGeometry08 k
  · exact cellGeometry09_eu k
  · exact cellGeometry10_eu k
  · exact cellGeometry11_eu k
  · exact cellGeometry12_eu k
  · exact cellGeometry13_eu k
  · exact cellGeometry14_eu k
  · exact cellGeometry15_eu k
  · exact cellGeometry16_eu k
  · exact cellGeometry17_eu k
  · exact cellGeometry18_eu k
  · exact cellGeometry19_eu k
  · exact cellGeometry20_eu k
  · exact cellGeometry21_eu k
  · exact cellGeometry22_eu k
  · exact cellGeometry23_eu k
  · exact cellGeometry24_eu k
  · exact cellGeometry25_eu k
  · exact cellGeometry26_eu k
  · exact cellGeometry27_eu k
  · exact cellGeometry28_eu k
  · exact cellGeometry29_eu k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cell_geometry_eu_oai := @OAI.AtomicTriangular.Construction.cell_geometry_eu_oai
