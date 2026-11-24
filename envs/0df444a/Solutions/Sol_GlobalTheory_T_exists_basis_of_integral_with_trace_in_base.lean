-- Prove2me | solution 1 for GlobalTheory.T.exists_basis_of_integral_with_trace_in_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:47:49.607913+00:00
-- url     : https://prove2.me/submissions/1339f989-5ee3-479c-9f96-4eda36785883

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsBasisInFiniteDomainTraceMem
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsBasisInFiniteDomainTraceMemStatement
import Theorems.Thm_GlobalTheory_exists_basis_in_finite_domain_trace_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (T C F K : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [CommRing C] [IsDomain C] [Field F] [Field K] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Module.Finite T C], ∃ (n : ℕ) (b : Module.Basis (Fin n) F K), (∀ i, ∃ c : C, algebraMap C K c = b i) ∧ ∀ i j, ∃ t : T, algebraMap T F t = Algebra.trace F K (b i * b j) := by
  first | exact @GlobalTheory.exists_basis_in_finite_domain_trace_mem | exact GlobalTheory.exists_basis_in_finite_domain_trace_mem | (intros; apply GlobalTheory.exists_basis_in_finite_domain_trace_mem <;> assumption)
end _root_.GlobalTheory.T
