-- Prove2me | solution 1 for OAI.KadisonSimilarity.repeatedMultiplicityInclusion_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:25:33.994777+00:00
-- url     : https://prove2.me/submissions/4584eb00-2153-4ecd-8c10-51e0f0ac5f16

import Mathlib
import Definitions.Def_OAIQ075A016

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_WordMultiplicities
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual multiplicity spaces of the alternating tracial words, their
normalized repeated-letter inclusions, and the degree-zero identification. -/

noncomputable section
namespace KadisonSimilarity

universe u
variable {B : Type u} [NormedAddCommGroup B] [InnerProductSpace ℂ B]

variable [CompleteSpace B]

/-- Repeated insertion at degree zero is precisely the canonical unitary. -/
theorem repeatedMultiplicityInclusion_zero_oai (ΩA : B) (s : centeredSubspace ΩA)
    (hs : ‖s‖ = 1) :
    repeatedMultiplicityInclusion ΩA s hs 0 = (zeroMultiplicityEquiv ΩA).toLinearIsometry := by
  ext b
  change hilbertTensorInsert (completedTensorWord (fun _ : Fin 0 => s)) b =
    hilbertTensorInsert (completedTensorWord (Fin.elim0 : Fin 0 → centeredSubspace ΩA)) b
  congr 2

end KadisonSimilarity

end

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonSimilarity.repeatedMultiplicityInclusion_zero_oai.{u} := @OAI.KadisonSimilarity.repeatedMultiplicityInclusion_zero_oai.{u}
