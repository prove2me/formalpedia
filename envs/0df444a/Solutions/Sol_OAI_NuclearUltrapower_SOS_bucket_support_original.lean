-- Prove2me | solution 1 for OAI.NuclearUltrapower.SOS.bucket_support_original
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:10:03.178711+00:00
-- url     : https://prove2.me/submissions/67e0c302-facc-46d1-8afd-57f67a80dcc4

import Mathlib
import Definitions.Def_OAIQ019N049
import Theorems.Thm_OAI_NuclearUltrapower_SOS_mem_getD_flatten
import Theorems.Thm_OAI_NuclearUltrapower_SOS_support_normalize_iff

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_IntegralCertificate
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace NuclearUltrapower.SOS
variable {α : Type*} [DecidableEq α]

theorem bucket_support_original_oai (le : α → α → Bool)
    (original : List (Poly α)) (buckets : List (List (Poly α)))
    (hnorm : original.map (normalize le) = buckets.map (fun r => normalize le r.flatten))
    (b : ℕ) {m : α}
    (hm : m ∈ (normalize le (buckets.flatMap (fun r => r.getD b []))).map Prod.fst) :
    m ∈ original.flatten.map Prod.fst := by
  have hm' := (support_normalize_iff le _ m).mp hm
  obtain ⟨p, hp, hpval⟩ := List.mem_map.mp hm'
  obtain ⟨r, hr, hpr⟩ := List.mem_flatMap.mp hp
  have hpr' : p ∈ r.flatten := mem_getD_flatten r b hpr
  have hn : normalize le r.flatten ∈ original.map (normalize le) := by
    rw [hnorm]
    exact List.mem_map_of_mem hr
  obtain ⟨q, hq, heq⟩ := List.mem_map.mp hn
  have hmnorm : m ∈ (normalize le r.flatten).map Prod.fst :=
    (support_normalize_iff le _ m).mpr (List.mem_map.mpr ⟨p,hpr',hpval⟩)
  rw [← heq] at hmnorm
  have hmq := (support_normalize_iff le q m).mp hmnorm
  obtain ⟨t, ht, htval⟩ := List.mem_map.mp hmq
  exact List.mem_map.mpr ⟨t, List.mem_flatten.mpr ⟨q,hq,ht⟩, htval⟩
end NuclearUltrapower.SOS

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.NuclearUltrapower.SOS.bucket_support_original_oai.{u_1} := @OAI.NuclearUltrapower.SOS.bucket_support_original_oai.{u_1}
