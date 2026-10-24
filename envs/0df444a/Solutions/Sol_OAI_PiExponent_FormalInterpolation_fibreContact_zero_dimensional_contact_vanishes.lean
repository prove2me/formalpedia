-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fibreContact_zero_dimensional_contact_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T03:09:10.845523+00:00
-- url     : https://prove2.me/submissions/2512c192-c7e6-4d80-ad7c-5ddcf68c7124

import Mathlib
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

namespace PXFC0

lemma contact_zero {d : ℕ} {E : Type} [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin d → E) (I : Ideal (MvPolynomial (Fin d) Complex))
    (hI : ∀ f ∈ I, MvPolynomial.aeval x f = 0) :
    polynomialCurveIdealContact nu x I = 0 := by
  classical
  unfold polynomialCurveIdealContact
  split_ifs
  · have : {k : Nat | ∃ f : MvPolynomial (Fin d) Complex,
        f ∈ I ∧ nu.1 (MvPolynomial.aeval x f) = ((k : Int) : WithTop Int)} = ∅ := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro f hf hν
      rw [hI f hf, AddValuation.map_zero] at hν
      exact WithTop.top_ne_coe hν
    rw [this, Nat.sInf_empty]
  · rfl

end PXFC0

theorem solution
    {K : Nat} (c : Fin K → Fin 0 → Complex)
    (e : Fin 1 → Nat) (he : ∀ i, 0 < e i)
    (E : Type) [Field E] [Algebra Complex E]
    (nu : PolynomialCurvePlace E) (x : Fin 1 → E)
    (hfibre : x 0 = 1) :
    ∀ j k : Fin K, j ≠ k →
      ¬ (0 < polynomialCurveIdealContact nu x
            (logarithmicCenterIdeal (c j) (fun _ => e 0) e) ∧
         0 < polynomialCurveIdealContact nu x
            (logarithmicCenterIdeal (c k) (fun _ => e 0) e)) := by
  intro j k _ h
  have hz : ∀ (c' : Fin 0 → Complex),
      polynomialCurveIdealContact nu x (logarithmicCenterIdeal c' (fun _ => e 0) e) = 0 := by
    intro c'
    apply PXFC0.contact_zero
    intro f hf
    have hle : logarithmicCenterIdeal c' (fun _ => e 0) e ≤ RingHom.ker (MvPolynomial.aeval x).toRingHom := by
      unfold logarithmicCenterIdeal
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have hi : i = 0 := Fin.fin_one_eq_zero i
      subst hi
      simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow]
      simp [logarithmicCoordinate, hfibre, (he 0).ne']
    exact hle hf
  rw [hz (c j)] at h
  exact lt_irrefl 0 h.1
