-- Prove2me | solution 1 for GlobalTheory.LocalFiniteOddFixed.exists_plus_eta_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:41:30.420711+00:00
-- url     : https://prove2.me/submissions/9f715046-028f-4916-bb3e-61fdc3aeb0c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfFinite
import Theorems.Thm_GlobalTheory_LocalFiniteOddFixed_exists_fixed_odd
import Theorems.Thm_P2M_GlobalTheory_LocalFiniteOddFixed_norm_prod__35ea87ad5dd5

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
theorem _root_.solution (K : UQ) (B : InvAlg K) (f : B.A) (hf : IsIdempotentElem f)
    (hf0 : f ≠ 0) (hfield : ∀ y : B.A, f * y ≠ 0 → ∃ z : B.A, f * y * z = f) (hσ : B.σ f = f) :
    ∃ y : B.A, B.Plus y ∧ y * (1 - f) = 1 - f ∧ K.eta (Algebra.norm K.E y) = -1 := by
  have hff : f * f = f := hf
  let I : Ideal B.A := Ideal.span {1 - f}
  have hI : ∀ y, y ∈ I ↔ f * y = 0 := by
    intro y
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨s, rfl⟩
      linear_combination (-s) * hff
    · intro h
      exact ⟨y, by linear_combination -h⟩
  haveI : I.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨by rw [hI]; simpa using hf0, fun J x hIJ hx hxJ => ?_⟩
    obtain ⟨z, hz⟩ := hfield x (fun h => hx ((hI x).2 h))
    have h1 : 1 - x * z ∈ J := hIJ ((hI _).2 (by linear_combination -hz))
    have := J.add_mem h1 (J.mul_mem_right z hxJ)
    simpa using this
  letI : Field (B.A ⧸ I) := Ideal.Quotient.field I
  have hle : I ≤ I.comap (B.σ : B.A →+* B.A) := by
    intro y hy
    rw [Ideal.mem_comap, hI]
    have := congrArg B.σ ((hI y).1 hy)
    rw [map_mul, hσ, map_zero] at this
    exact this
  let τ : B.A ⧸ I →+* B.A ⧸ I := Ideal.quotientMap I (B.σ : B.A →+* B.A) hle
  have hτ : ∀ x, τ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (B.σ x) := fun x => rfl
  obtain ⟨y, hy0, hyτ, hyN⟩ := exists_fixed_odd K (B.A ⧸ I) τ
    (by
      intro x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [hτ, hτ, B.σ_σ])
    (by
      intro e
      change τ (Ideal.Quotient.mk I (algebraMap K.E B.A e)) = _
      rw [hτ, B.σ_alg]
      rfl)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hy1 : f * y ≠ 0 := fun h => hy0 (Ideal.Quotient.eq_zero_iff_mem.2 ((hI y).2 h))
  obtain ⟨z, hz⟩ := hfield y hy1
  have hy2 : f * (B.σ y - y) = 0 := by
    rw [← hI, ← Ideal.Quotient.eq, ← hτ]
    exact hyτ
  refine ⟨f * y + (1 - f), ⟨?_, ?_⟩, ?_, ?_⟩
  · refine IsUnit.of_mul_eq_one (f * z + (1 - f)) ?_
    linear_combination (y * z - y - z + 1) * hff + hz
  · rw [map_add, map_mul, map_sub, map_one, hσ]
    linear_combination hy2
  · linear_combination (1 - y) * hff
  · let e := AlgEquiv.prodQuotientOfIsIdempotentElem K.E (e := 1 - f) (f := f) hf.one_sub hf
      (by ring) (by linear_combination -hff)
    have he : e (f * y + (1 - f)) = (Ideal.Quotient.mk I y, 1) := by
      refine Prod.ext ?_ ?_
      · change Ideal.Quotient.mk I _ = Ideal.Quotient.mk I y
        rw [Ideal.Quotient.eq, hI]
        linear_combination (y - 1) * hff
      · change Ideal.Quotient.mk (Ideal.span {f}) _ = Ideal.Quotient.mk (Ideal.span {f}) 1
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
        exact ⟨y - 1, by ring⟩
    rw [← Algebra.norm_eq_of_algEquiv e, he, norm_prod', map_one, mul_one]
    exact hyN
end GlobalTheory.LocalFiniteOddFixed
