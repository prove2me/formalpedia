-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cell_geometry_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:17:10.127214+00:00
-- url     : https://prove2.me/submissions/05ac573a-6657-45ac-97ad-1fdf44971a2d

import Mathlib
import Definitions.Def_OAIQ257X011
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry00_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry01_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry02_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry04_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry05_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry06_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry09_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry10_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry11_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry12_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry13_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry14_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry15_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry16_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry17_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry18_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry19_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry20_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry21_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry22_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry23_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry24_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry25_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry26_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry27_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry28_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellGeometry29_x

section
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGrid0
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
-- module Solutions.OAIQ250_TR.Triangular_Signs_SineGridChecks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.Construction
lemma cell_geometry_x_oai (u : Fin 30) (k : Fin 100) :
    0 ≤ cellMagnitude u k ∧ cellMagnitude u k≤3 ∧
    (∀ j : Fin 15,j≠localPivot u → 0 ≤ cellSeparation u k j ∧ cellSeparation u k j≤18) := by
  fin_cases u
  · exact cellGeometry00_x k
  · exact cellGeometry01_x k
  · exact cellGeometry02_x k
  · exact cellGeometry03 k
  · exact cellGeometry04_x k
  · exact cellGeometry05_x k
  · exact cellGeometry06_x k
  · exact cellGeometry07 k
  · exact cellGeometry08 k
  · exact cellGeometry09_x k
  · exact cellGeometry10_x k
  · exact cellGeometry11_x k
  · exact cellGeometry12_x k
  · exact cellGeometry13_x k
  · exact cellGeometry14_x k
  · exact cellGeometry15_x k
  · exact cellGeometry16_x k
  · exact cellGeometry17_x k
  · exact cellGeometry18_x k
  · exact cellGeometry19_x k
  · exact cellGeometry20_x k
  · exact cellGeometry21_x k
  · exact cellGeometry22_x k
  · exact cellGeometry23_x k
  · exact cellGeometry24_x k
  · exact cellGeometry25_x k
  · exact cellGeometry26_x k
  · exact cellGeometry27_x k
  · exact cellGeometry28_x k
  · exact cellGeometry29_x k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cell_geometry_x_oai := @OAI.AtomicTriangular.Construction.cell_geometry_x_oai
