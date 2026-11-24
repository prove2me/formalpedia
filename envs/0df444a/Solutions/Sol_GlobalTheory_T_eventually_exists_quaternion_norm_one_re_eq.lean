-- Prove2me | solution 1 for GlobalTheory.T.eventually_exists_quaternion_norm_one_re_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:06:38.40307+00:00
-- url     : https://prove2.me/submissions/d3f35cdf-279c-40aa-8f58-91637afcf29b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EventuallyExistsQuaternionNormOneReEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EventuallyExistsQuaternionNormOneReEqStatement
import Theorems.Thm_GlobalTheory_QSA_IntRep_exists_nrm_eq_one_re_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ᶠ v in (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))), ∀ t ∈ v.adicCompletionIntegers F, ∃ u : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) b], nrm u = 1 ∧ u.re = t ∧ u.imI ∈ v.adicCompletionIntegers F ∧ u.imJ ∈ v.adicCompletionIntegers F ∧ u.imK ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.QSA.IntRep.exists_nrm_eq_one_re_eq | exact GlobalTheory.QSA.IntRep.exists_nrm_eq_one_re_eq | (intros; apply GlobalTheory.QSA.IntRep.exists_nrm_eq_one_re_eq <;> assumption)
end _root_.GlobalTheory.T
