-- Prove2me | solution 1 for OAI.SourceBurnside.ConcreteSource.matrix_nil_kernel
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T16:16:32.606097+00:00
-- url     : https://prove2.me/submissions/b9ac32f2-8310-4f41-bb18-3b9be9bbd3cb

import Mathlib
import Definitions.Def_OAIQ18Pg009
import Theorems.Thm_OAI_SourceBurnside_SourceMachine_MachineHierarchy_matrixNilKernel

section
-- module Solutions.OAIQ18_PG.PeriodicGroups_Steinberg_CoefficientQuotients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w

namespace SourceBurnside.ConcreteSource
noncomputable section

lemma dilation_large : 10*(10000+1)*(10+1)<dilation := by decide
theorem matrix_nil_kernel_oai : MatrixNilKernel augmentation.toRingHom :=
  machine.matrixNilKernel (by rfl) dilation_large
end
end SourceBurnside.ConcreteSource

end

end OAI
end

theorem solution : type_of% @OAI.SourceBurnside.ConcreteSource.matrix_nil_kernel_oai := @OAI.SourceBurnside.ConcreteSource.matrix_nil_kernel_oai
