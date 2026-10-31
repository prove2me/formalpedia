-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.residual_good
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:28:57.739183+00:00
-- url     : https://prove2.me/submissions/2b1b0b23-f337-4102-9650-b6f2a83cf669

import Mathlib
import Definitions.Def_OAIQ019N044
import Theorems.Thm_OAI_NuclearUltrapower_SOS_bucket_support_original
import Theorems.Thm_OAI_NuclearUltrapower_SOS_residualRows_good
import Theorems.Thm_OAI_NuclearUltrapower_SOS_row_normalizations

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace NuclearUltrapower.SOS

theorem residual_good_oai {p : Mat3 × ℤ} (hp : p ∈ residual) : GoodWord 4 p.1 := by
  change p ∈ (List.range 128).flatMap residualBucket at hp
  obtain ⟨b,_,hb⟩ := List.mem_flatMap.mp hp
  have h := bucket_support_original matLe residualRows allRowBuckets row_normalizations b
    (List.mem_map_of_mem (f := Prod.fst) hb)
  obtain ⟨q,hq,he⟩ := List.mem_map.mp h
  rw [← he]
  exact residualRows_good hq

end NuclearUltrapower.SOS
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.SOS.residual_good_oai := @OAI.NuclearUltrapower.SOS.residual_good_oai
