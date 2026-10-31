-- Prove2me | solution 1 for OAI.NuclearUltrapower.SL3Certificate.gram_row_25
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:17:03.592422+00:00
-- url     : https://prove2.me/submissions/bbe7d552-af8a-43d8-83e6-234b33841668

import Mathlib
import Definitions.Def_OAIQ019N041

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/- Exact rational SOS data. All asserted computed identities reduce in the
   stock Lean kernel; the numerical program and these literals are untrusted. -/
namespace NuclearUltrapower.SL3Certificate
theorem gram_row_25_oai : columns.map (dot q25) = g25 := by decide +kernel
end NuclearUltrapower.SL3Certificate
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SL3Certificate.gram_row_25_oai := @OAI.NuclearUltrapower.SL3Certificate.gram_row_25_oai
