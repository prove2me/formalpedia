-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.actualSchwartz_fourier_eu
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:54:34.339688+00:00
-- url     : https://prove2.me/submissions/e0d664c9-1bef-4510-92d0-bffde3378094

import Mathlib
import Definitions.Def_OAIQ334E006
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualSchwartz_fourier_side_eu

section
-- module Solutions.OAIQ334_EU.Triangular_Construction_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
lemma actualSchwartz_fourier_eu_oai {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (x : Plane) :
    realFourier (actualSchwartz 0 z hz hzB) x=(actualSchwartz 1 z hz hzB x:ℂ) :=
  actualSchwartz_fourier_side_eu 0 hz hzB x
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.actualSchwartz_fourier_eu_oai := @OAI.AtomicTriangular.Construction.actualSchwartz_fourier_eu_oai
