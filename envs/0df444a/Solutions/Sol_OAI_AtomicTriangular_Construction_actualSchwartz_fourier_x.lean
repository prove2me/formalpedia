-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.actualSchwartz_fourier_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T03:51:28.121991+00:00
-- url     : https://prove2.me/submissions/b8ed8ec4-3d7c-47be-8bf9-de985632ea3e

import Mathlib
import Definitions.Def_AtomicGaussian
import Definitions.Def_OAIQ257X006
import Theorems.Thm_OAI_AtomicTriangular_Construction_actualSchwartz_fourier_side_x

section
-- module Solutions.OAIQ250_TR.Triangular_Construction_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Complex
namespace AtomicTriangular.Construction
lemma actualSchwartz_fourier_x_oai {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (x : Plane) :
    realFourier (actualSchwartz 0 z hz hzB) x=(actualSchwartz 1 z hz hzB x:ℂ) :=
  actualSchwartz_fourier_side_x 0 hz hzB x
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.actualSchwartz_fourier_x_oai := @OAI.AtomicTriangular.Construction.actualSchwartz_fourier_x_oai
