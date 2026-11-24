-- Prove2me | solution 1 for GlobalTheory.LocalFiniteOddFixed.val_of_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:48:55.554491+00:00
-- url     : https://prove2.me/submissions/bb348de9-786f-40b1-8879-8fea1bca4a76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LocalFiniteOddFixed
open GlobalTheory.UnitLemma
namespace GlobalTheory.LocalFiniteOddFixed
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type}
    [Field E] [Algebra O E] [IsFractionRing O E] (x : O) (n : ℕ)
    (h : Ideal.span {x} = IsLocalRing.maximalIdeal O ^ n) : val O (algebraMap O E x) = n := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm : IsLocalRing.maximalIdeal O = Ideal.span {p} := hp.maximalIdeal_eq
  rw [hm, Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
  obtain ⟨u, hu⟩ := h.symm
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).intValuation p = WithZero.exp (-1) :=
    IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ hp.ne_zero hm
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).intValuation (u : O) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    exact fun hmem => (IsLocalRing.mem_maximalIdeal _).1 hmem u.isUnit
  have h3 := (IsDiscreteValuationRing.maximalIdeal O).valuation_of_algebraMap (K := E) x
  unfold val
  rw [h3, ← hu, map_mul, map_pow, h1, h2, mul_one, ← WithZero.exp_nsmul, WithZero.log_exp]
  simp
end GlobalTheory.LocalFiniteOddFixed
