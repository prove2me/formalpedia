-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.cell_factors_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T13:12:18.185865+00:00
-- url     : https://prove2.me/submissions/49ee0005-7004-45c4-ae03-9644ae047c9b

import Mathlib
import Definitions.Def_OAIQ334E011
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors00_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors01_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors02_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors03_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors04_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors05_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors06_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors07_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors08_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors09_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors10_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors11_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors12_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors13_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors14_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors15_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors16_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors17_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors18_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors19_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors20_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors21_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors22_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors23_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors24_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors25_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors26_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors27_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors28_eu
import Theorems.Thm_OAI_AtomicTriangular_Construction_cellFactors29_eu

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
lemma cell_factors_eu_oai (u : Fin 30) (k : Fin 100) :
    (∀ j : Fin 15,0 ≤ cellFactor u k j) ∧ cellBarrier u < ∏ j : Fin 15,(cellFactor u k j)^2 := by
  fin_cases u
  · exact cellFactors00_eu k
  · exact cellFactors01_eu k
  · exact cellFactors02_eu k
  · exact cellFactors03_eu k
  · exact cellFactors04_eu k
  · exact cellFactors05_eu k
  · exact cellFactors06_eu k
  · exact cellFactors07_eu k
  · exact cellFactors08_eu k
  · exact cellFactors09_eu k
  · exact cellFactors10_eu k
  · exact cellFactors11_eu k
  · exact cellFactors12_eu k
  · exact cellFactors13_eu k
  · exact cellFactors14_eu k
  · exact cellFactors15_eu k
  · exact cellFactors16_eu k
  · exact cellFactors17_eu k
  · exact cellFactors18_eu k
  · exact cellFactors19_eu k
  · exact cellFactors20_eu k
  · exact cellFactors21_eu k
  · exact cellFactors22_eu k
  · exact cellFactors23_eu k
  · exact cellFactors24_eu k
  · exact cellFactors25_eu k
  · exact cellFactors26_eu k
  · exact cellFactors27_eu k
  · exact cellFactors28_eu k
  · exact cellFactors29_eu k
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.cell_factors_eu_oai := @OAI.AtomicTriangular.Construction.cell_factors_eu_oai
