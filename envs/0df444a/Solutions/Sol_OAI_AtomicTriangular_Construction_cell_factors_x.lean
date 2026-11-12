-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cell_factors_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:16:39.731478+00:00
-- url     : https://prove2.me/submissions/e236c228-73ed-4bd7-a376-f15d6fd965bc

import Mathlib
import Definitions.Def_OAIQ257X011
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors00_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors01_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors02_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors03_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors04_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors05_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors06_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors07_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors08_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors09_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors10_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors11_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors12_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors13_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors14_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors15_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors16_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors17_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors18_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors19_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors20_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors21_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors22_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors23_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors24_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors25_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors26_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors27_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors28_x
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors29_x

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
lemma cell_factors_x_oai (u : Fin 30) (k : Fin 100) :
    (∀ j : Fin 15,0 ≤ cellFactor u k j) ∧ cellBarrier u < ∏ j : Fin 15,(cellFactor u k j)^2 := by
  fin_cases u
  · exact cellFactors00_x k
  · exact cellFactors01_x k
  · exact cellFactors02_x k
  · exact cellFactors03_x k
  · exact cellFactors04_x k
  · exact cellFactors05_x k
  · exact cellFactors06_x k
  · exact cellFactors07_x k
  · exact cellFactors08_x k
  · exact cellFactors09_x k
  · exact cellFactors10_x k
  · exact cellFactors11_x k
  · exact cellFactors12_x k
  · exact cellFactors13_x k
  · exact cellFactors14_x k
  · exact cellFactors15_x k
  · exact cellFactors16_x k
  · exact cellFactors17_x k
  · exact cellFactors18_x k
  · exact cellFactors19_x k
  · exact cellFactors20_x k
  · exact cellFactors21_x k
  · exact cellFactors22_x k
  · exact cellFactors23_x k
  · exact cellFactors24_x k
  · exact cellFactors25_x k
  · exact cellFactors26_x k
  · exact cellFactors27_x k
  · exact cellFactors28_x k
  · exact cellFactors29_x k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cell_factors_x_oai := @OAI.AtomicTriangular.Construction.cell_factors_x_oai
