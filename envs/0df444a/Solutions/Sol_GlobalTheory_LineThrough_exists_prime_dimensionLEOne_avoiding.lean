-- Prove2me | solution 1 for GlobalTheory.LineThrough.exists_prime_dimensionLEOne_avoiding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:12:55.262843+00:00
-- url     : https://prove2.me/submissions/a6ab9580-8bcf-4b61-9723-ddb023334e44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsPrimeDimensionLEOneAvoiding
import Theorems.Thm_GlobalTheory_LineThrough_exists_common_nonroot
import Theorems.Thm_GlobalTheory_LineThrough_eval_zero_lineMap
import Theorems.Thm_GlobalTheory_LineThrough_eval_one_lineMap
import Theorems.Thm_GlobalTheory_LineThrough_isMaximal_of_ker_lineMap_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LineThrough
namespace GlobalTheory.LineThrough
theorem _root_.solution
    (E : Type) [CommRing E] [IsDomain E] [Algebra ℂ E] [Algebra.FiniteType ℂ E]
    (e : E →ₐ[ℂ] ℂ) (T : Set E) (hT : T.Countable) (h0 : (0 : E) ∉ T) :
    ∃ Q : Ideal E, Q.IsPrime ∧ Q ≤ RingHom.ker e ∧ (∀ r ∈ T, r ∉ Q) ∧
      Ring.DimensionLEOne (E ⧸ Q) := by
  obtain ⟨d, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℂ E
  letI : Algebra (MvPolynomial (Fin d) ℂ) E := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) E := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin d) ℂ) E :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have hn : ∀ r : T, ∃ n : MvPolynomial (Fin d) ℂ, n ≠ 0 ∧
      algebraMap _ E n ∈ Ideal.span {(r : E)} := by
    intro r
    have hr : (r : E) ≠ 0 := fun h => h0 (h ▸ r.2)
    have := Ideal.comap_ne_bot_of_integral_mem (R := MvPolynomial (Fin d) ℂ) hr
      (Ideal.mem_span_singleton_self (r : E)) (Algebra.IsIntegral.isIntegral _)
    obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
    exact ⟨n, hn0, hn⟩
  choose n hn0 hn using hn
  haveI : Countable T := hT.to_subtype
  obtain ⟨c, hc⟩ := exists_common_nonroot d (Set.range n) (Set.countable_range n)
    (by rintro ⟨r, hr⟩; exact hn0 r hr)
  let a : Fin d → ℂ := fun i => e (g (MvPolynomial.X i))
  have hea : ∀ f, e (g f) = MvPolynomial.eval a f := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r =>
      have : g (MvPolynomial.C r) = algebraMap ℂ E r := g.commutes r
      simp [this]
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp, a]
  haveI hpp : (RingHom.ker (lineMap a c)).IsPrime := RingHom.ker_isPrime _
  haveI hM : (RingHom.ker e).IsPrime := RingHom.ker_isPrime _
  have hle : RingHom.ker (lineMap a c) ≤ (RingHom.ker e).under (MvPolynomial (Fin d) ℂ) := by
    intro f hf
    change e (g f) = 0
    rw [hea, ← eval_zero_lineMap a c, RingHom.mem_ker.1 hf, eval_zero]
  obtain ⟨Q, hQ, hQp, hQo⟩ := Ideal.exists_ideal_le_liesOver_of_le
    (p := RingHom.ker (lineMap a c)) (RingHom.ker e) hle
  have hQc : Q.comap (algebraMap (MvPolynomial (Fin d) ℂ) E) = RingHom.ker (lineMap a c) :=
    hQo.over.symm
  refine ⟨Q, hQp, hQ, fun r hr hrQ => ?_, ⟨fun {P} hP0 hP => ?_⟩⟩
  · have h1 : n ⟨r, hr⟩ ∈ RingHom.ker (lineMap a c) := by
      rw [← hQc]
      exact (Ideal.span_singleton_le_iff_mem _).2 hrQ (hn ⟨r, hr⟩)
    apply hc _ ⟨⟨r, hr⟩, rfl⟩
    rw [← eval_one_lineMap a c, RingHom.mem_ker.1 h1, eval_zero]
  · have hs : Function.Surjective (Ideal.Quotient.mk Q) := Ideal.Quotient.mk_surjective
    have hlt : Q < P.comap (Ideal.Quotient.mk Q) := by
      refine lt_of_le_of_ne (fun x hx => ?_) (fun h => hP0 ?_)
      · simp [Ideal.Quotient.eq_zero_iff_mem.2 hx]
      · rw [← Ideal.map_comap_of_surjective _ hs P, ← h, Ideal.map_quotient_self]
    have hlt' := Ideal.IsIntegral.comap_lt_comap (R := MvPolynomial (Fin d) ℂ) hlt
    rw [hQc] at hlt'
    have hm := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := MvPolynomial (Fin d) ℂ) _
      (isMaximal_of_ker_lineMap_lt a c _ hlt')
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hs hm with h | h
    · rw [Ideal.map_comap_of_surjective _ hs] at h
      exact absurd h hP.ne_top
    · rwa [Ideal.map_comap_of_surjective _ hs] at h
end GlobalTheory.LineThrough
