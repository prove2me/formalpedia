-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.logarithmicCoordinate_power_order_on_fibre
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T18:13:14.612074+00:00
-- url     : https://prove2.me/submissions/bf63f95e-60c3-454e-a1e3-2d4d1177be39

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib
import Mathlib.FieldTheory.IsAlgClosed.Basic

section

open OAI.PiExponent.FormalInterpolation

namespace PiL26

variable {E : Type} [Field E] [Algebra Complex E]

lemma val_C (nu : PolynomialCurvePlace E) (a : ℂ) : 0 ≤ nu.1 (algebraMap ℂ E a) := by
  by_cases ha : a = 0
  · simp [ha]
  · rw [nu.2.1 a ha]

lemma val_nonneg {d : ℕ} (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)) (f : MvPolynomial (Fin d) ℂ) :
    0 ≤ nu.1 (MvPolynomial.aeval x f) := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.aeval_C]; exact val_C nu a
  | add p q hp hq =>
    rw [map_add]
    exact le_trans (le_min hp hq) (AddValuation.map_add _ _ _)
  | mul_X p i hp =>
    rw [map_mul, MvPolynomial.aeval_X, AddValuation.map_mul]
    exact add_nonneg hp (hchart i)

lemma contact_eq_zero_of {d : ℕ} (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (I : Ideal (MvPolynomial (Fin d) Complex)) (f : MvPolynomial (Fin d) ℂ) (hf : f ∈ I)
    (h0 : nu.1 (MvPolynomial.aeval x f) = 0) : polynomialCurveIdealContact nu x I = 0 := by
  classical
  unfold polynomialCurveIdealContact
  split_ifs
  · apply Nat.eq_zero_of_le_zero
    apply Nat.sInf_le
    exact ⟨f, hf, by simpa using h0⟩
  · rfl

theorem sup_top {d : Nat} (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (I J : Ideal (MvPolynomial (Fin d) Complex))
    (hIJ : I ⊔ J = ⊤) :
    ¬ (0 < polynomialCurveIdealContact nu x I ∧
       0 < polynomialCurveIdealContact nu x J) := by
  classical
  rintro ⟨hI, hJ⟩
  by_cases hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i)
  · have h1 : (1 : MvPolynomial (Fin d) ℂ) ∈ I ⊔ J := hIJ ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    have hv := AddValuation.map_add nu.1 (MvPolynomial.aeval x a) (MvPolynomial.aeval x b)
    rw [← map_add, hab, map_one, AddValuation.map_one] at hv
    rcases min_le_iff.1 hv with h | h
    · have := contact_eq_zero_of nu x I a ha (le_antisymm h (val_nonneg nu x hchart a))
      omega
    · have := contact_eq_zero_of nu x J b hb (le_antisymm h (val_nonneg nu x hchart b))
      omega
  · unfold polynomialCurveIdealContact at hI
    rw [if_neg hchart] at hI
    omega

theorem le_order {d : Nat} (nu : PolynomialCurvePlace E) (x : Fin d → E)
    (I : Ideal (MvPolynomial (Fin d) Complex))
    (f : MvPolynomial (Fin d) Complex)
    (hchart : ∀ i, (0 : WithTop Int) ≤ nu.1 (x i))
    (hf : f ∈ I)
    (hne : MvPolynomial.aeval x f ≠ 0) :
    (polynomialCurveIdealContact nu x I : Real) ≤
      (polynomialCurveOrder nu (MvPolynomial.aeval x f) : Real) := by
  classical
  have h0 := val_nonneg nu x hchart f
  have htop : nu.1 (MvPolynomial.aeval x f) ≠ ⊤ := by
    rwa [Ne, AddValuation.top_iff]
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 htop
  have hk0 : 0 ≤ k := by rw [← hk] at h0; exact_mod_cast h0
  have hord : polynomialCurveOrder nu (MvPolynomial.aeval x f) = k := by
    unfold polynomialCurveOrder; rw [← hk]; rfl
  rw [hord]
  have hle : polynomialCurveIdealContact nu x I ≤ k.toNat := by
    unfold polynomialCurveIdealContact
    rw [if_pos hchart]
    apply Nat.sInf_le
    exact ⟨f, hf, by rw [← hk, Int.toNat_of_nonneg hk0]⟩
  have : ((polynomialCurveIdealContact nu x I : ℕ) : ℤ) ≤ k := by
    have := (Nat.cast_le (α := ℤ)).2 hle
    rwa [Int.toNat_of_nonneg hk0] at this
  exact_mod_cast this

end PiL26

namespace PiL26b

theorem pow_order
    {m K : Nat} (c : Fin m → Complex)
    (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (x : Fin (m + 1) → E) (hfibre : x 0 = 1)
    (hnonconst : ∀ i : Fin m, Transcendental Complex (x i.succ))
    (nu : PolynomialCurvePlace E) (i : Fin m) :
    MvPolynomial.aeval x
        ((logarithmicCoordinate c (fun _ => e 0) i.succ) ^ e i.succ) ≠ 0 ∧
      (polynomialCurveOrder nu
        (MvPolynomial.aeval x
          ((logarithmicCoordinate c (fun _ => e 0) i.succ) ^ e i.succ)) : Real) =
        (e i.succ : Real) *
          (polynomialCurveOrder nu
            (x i.succ - algebraMap Complex E (c i)) : Real) := by
  have hL : MvPolynomial.aeval x (Polynomial.aeval (MvPolynomial.X 0 - 1 : MvPolynomial (Fin (m + 1)) ℂ)
      (OAI.PiExponent.InterpolationMatrix.truncatedLog (e 0))) = 0 := by
    rw [← Polynomial.aeval_algHom_apply]
    simp only [map_sub, MvPolynomial.aeval_X, hfibre, map_one, sub_self]
    rw [← Polynomial.coeff_zero_eq_aeval_zero', OAI.PiExponent.InterpolationMatrix.truncatedLog]
    simp [PowerSeries.coeff_trunc]
  have hev : MvPolynomial.aeval x (logarithmicCoordinate c (fun _ => e 0) i.succ) =
      x i.succ - algebraMap Complex E (c i) := by
    simp only [logarithmicCoordinate, Fin.cases_succ, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    rw [hL, sub_zero]
  have hne : x i.succ - algebraMap Complex E (c i) ≠ 0 := by
    intro h
    apply hnonconst i
    rw [sub_eq_zero.1 h]
    exact isAlgebraic_algebraMap _
  rw [map_pow, hev]
  refine ⟨pow_ne_zero _ hne, ?_⟩
  have htop : nu.1 (x i.succ - algebraMap Complex E (c i)) ≠ ⊤ := by
    rwa [Ne, AddValuation.top_iff]
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 htop
  unfold polynomialCurveOrder
  rw [AddValuation.map_pow, ← hk]
  rw [show (e i.succ) • ((k : ℤ) : WithTop ℤ) = ((e i.succ • k : ℤ) : WithTop ℤ) from
    (WithTop.coe_nsmul _ _).symm]
  simp only [WithTop.untop₀_coe, nsmul_eq_mul]
  push_cast; ring

end PiL26b

end

open OAI OAI.PiExponent OAI.PiExponent.FormalInterpolation

open OAI.PiExponent.FormalInterpolation

theorem solution
    {m K : Nat} (c : Fin m → Complex)
    (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (x : Fin (m + 1) → E) (hfibre : x 0 = 1)
    (hnonconst : ∀ i : Fin m, Transcendental Complex (x i.succ))
    (nu : PolynomialCurvePlace E) (i : Fin m) :
    MvPolynomial.aeval x
        ((logarithmicCoordinate c (fun _ => e 0) i.succ) ^ e i.succ) ≠ 0 ∧
      (polynomialCurveOrder nu
        (MvPolynomial.aeval x
          ((logarithmicCoordinate c (fun _ => e 0) i.succ) ^ e i.succ)) : Real) =
        (e i.succ : Real) *
          (polynomialCurveOrder nu
            (x i.succ - algebraMap Complex E (c i)) : Real) := by
  exact PiL26b.pow_order (K := K) c e E x hfibre hnonconst nu i
