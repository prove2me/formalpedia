-- Prove2me | solution 1 for GlobalTheory.exists_padicInt_algHom_comap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:34:51.739647+00:00
-- url     : https://prove2.me/submissions/164187bd-a198-4eaa-b204-ce4223fc3474

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Theorems.Thm_GlobalTheory_exists_prime_finite_quotient_atPrime
import Theorems.Thm_GlobalTheory_isLocalHom_of_injective_integralClosure
import Theorems.Thm_GlobalTheory_exists_injective_algHom_integralClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing TensorProduct
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory
theorem _root_.solution {A : Type*} [CommRing A] [IsNoetherianRing A]
    [Algebra ℤ_[p] A] (m : Ideal A) [m.IsMaximal] [Finite (A ⧸ m)] (hp : (p : A) ∈ m)
    {q : Ideal A} (hq : q.IsPrime) (hqm : q ≤ m) {f : A} (hf : (p : A) * f ∉ q) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K)
      (y : A →ₐ[ℤ_[p]] integralClosure ℤ_[p] K),
      (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m ∧ y f ≠ 0 := by
  have hm : (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] A) ≤ m := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast,
      Ideal.span_singleton_le_iff_mem]
    exact hp
  have hϖ : (p : ℤ_[p]) ∈ maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  obtain ⟨Q, hQ, hfQ, hfin⟩ := exists_prime_finite_quotient_atPrime m hm hq hqm hϖ (f := f)
    (by rwa [map_natCast])
  set L := Localization.AtPrime m
  have hf0 := mt Ideal.Quotient.eq_zero_iff_mem.mp hfQ
  rw [map_natCast, map_mul, map_mul, map_natCast, map_natCast] at hf0
  obtain ⟨K, hK, g, hg⟩ := exists_injective_algHom_integralClosure (p := p) (L ⧸ Q)
    (left_ne_zero_of_mul hf0)
  haveI : IsLocalRing (L ⧸ Q) :=
    .of_surjective' (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk Q) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  haveI := isLocalHom_of_injective_integralClosure g hg
  refine ⟨K, hK, g.comp ((Ideal.Quotient.mkₐ ℤ_[p] Q).comp (IsScalarTower.toAlgHom ℤ_[p] A L)),
    ?_, fun h => right_ne_zero_of_mul hf0 (hg (h.trans (map_zero g).symm))⟩
  ext a
  rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff L m,
    ← maximalIdeal_comap (Ideal.Quotient.mk Q),
    ← maximalIdeal_comap (g : L ⧸ Q →+* integralClosure ℤ_[p] K)]
  rfl
end GlobalTheory
