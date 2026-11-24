-- Prove2me | solution 1 for GlobalTheory.LocalNorm.exists_local_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:49:04.016408+00:00
-- url     : https://prove2.me/submissions/208a45ec-ee7d-4d89-a911-a21859c7fd2a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LocalNorm
namespace GlobalTheory.LocalNorm
theorem _root_.solution {B : Type*} [CommRing B] [IsDedekindDomain B] {I Q : Ideal B}
    (hI : I ≠ ⊥) (hQ : Q ≠ ⊥) :
    ∃ i ∈ I, ∃ r, r - 1 ∈ Q ∧ Ideal.span {r} * I ≤ Ideal.span {i} := by
  obtain ⟨i, hi⟩ := IsDedekindDomain.exists_sup_span_eq (I := Q * I) (J := I) Ideal.mul_le_right
    (mul_ne_zero hQ hI)
  obtain ⟨r, hr, hle⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup (I := Q)
    (N := Ideal.span {i}) (N' := I) (P := I) (IsNoetherian.noetherian I) le_rfl
    (by rw [sup_comm, smul_eq_mul, hi])
  refine ⟨i, ?_, r, hr, ?_⟩
  · rw [← hi]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self i)
  · rw [Ideal.span_singleton_mul_le_iff]
    exact fun z hz => hle (Submodule.smul_mem_pointwise_smul z r I hz)
end GlobalTheory.LocalNorm
