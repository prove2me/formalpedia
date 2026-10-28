-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal_contact_cutoff_invariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T20:53:15.496086+00:00
-- url     : https://prove2.me/submissions/a3a79a1b-293d-4a5a-aed6-39d17e76a873

import Mathlib
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Definitions.Def_OAI_PiExponent_LogarithmicInterpolationNumerics
import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

namespace A3S47CC

variable {E : Type} [Field E] [Algebra ℂ E]

/-- Valuation of a complex constant is nonnegative. -/
lemma val_const (b : PolynomialCurvePlace E) (c : ℂ) : 0 ≤ b.1 (algebraMap ℂ E c) := by
  by_cases hc : c = 0
  · simp [hc]
  · rw [b.2.1 c hc]

lemma val_mv_nonneg {d : ℕ} (b : PolynomialCurvePlace E) (x : Fin d → E)
    (hx : ∀ i, 0 ≤ b.1 (x i)) (f : MvPolynomial (Fin d) ℂ) :
    0 ≤ b.1 (MvPolynomial.aeval x f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa using val_const b a
  | add p q hp hq => rw [map_add]; exact le_trans (le_min hp hq) (b.1.map_add _ _)
  | mul_X p i hp => rw [map_mul, b.1.map_mul, MvPolynomial.aeval_X]; exact add_nonneg hp (hx i)

lemma val_poly_nonneg (b : PolynomialCurvePlace E) (u : E) (hu : 0 ≤ b.1 u)
    (q : Polynomial ℂ) : 0 ≤ b.1 (Polynomial.aeval u q) := by
  induction q using Polynomial.induction_on with
  | C a => simpa using val_const b a
  | add p q hp hq => rw [map_add]; exact le_trans (le_min hp hq) (b.1.map_add _ _)
  | monomial n a _ =>
    rw [map_mul, b.1.map_mul, map_pow, b.1.map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    exact add_nonneg (val_const b a) (nsmul_nonneg hu _)

/-- `c` is the exact order of `I` along `x`. -/
def IsOrd {d : ℕ} (b : PolynomialCurvePlace E) (x : Fin d → E)
    (I : Ideal (MvPolynomial (Fin d) ℂ)) (c : WithTop ℤ) : Prop :=
  (∀ f ∈ I, c ≤ b.1 (MvPolynomial.aeval x f)) ∧ ∃ f ∈ I, b.1 (MvPolynomial.aeval x f) = c

lemma contact_eq_of_isOrd {d : ℕ} (b : PolynomialCurvePlace E) (x : Fin d → E)
    (I J : Ideal (MvPolynomial (Fin d) ℂ)) (c : WithTop ℤ)
    (hI : IsOrd b x I c) (hJ : IsOrd b x J c) :
    polynomialCurveIdealContact b x I = polynomialCurveIdealContact b x J := by
  unfold polynomialCurveIdealContact
  split_ifs with hx
  swap; · rfl
  -- both sInf's equal a value determined by c
  have key : ∀ (K : Ideal (MvPolynomial (Fin d) ℂ)), IsOrd b x K c →
      sInf {k : ℕ | ∃ f : MvPolynomial (Fin d) ℂ, f ∈ K ∧
        b.1 (MvPolynomial.aeval x f) = ((k : ℤ) : WithTop ℤ)} = (c.untop₀).toNat := by
    intro K ⟨hge, f0, hf0K, hf0⟩
    have c0 : 0 ≤ c := hf0 ▸ val_mv_nonneg b x hx f0
    induction c using WithTop.recTopCoe with
    | top =>
      have : {k : ℕ | ∃ f : MvPolynomial (Fin d) ℂ, f ∈ K ∧
          b.1 (MvPolynomial.aeval x f) = ((k : ℤ) : WithTop ℤ)} = ∅ := by
        ext k; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨f, hf, he⟩
        have := hge f hf; rw [he] at this; exact absurd this (by simp)
      rw [this]; simp
    | coe z =>
      have hz : 0 ≤ z := by exact_mod_cast c0
      simp only [WithTop.untop₀_coe]
      apply le_antisymm
      · apply Nat.sInf_le
        exact ⟨f0, hf0K, by rw [hf0]; congr 1; omega⟩
      · apply le_csInf
        · exact ⟨_, f0, hf0K, by rw [hf0]; show ((z : ℤ) : WithTop ℤ) = ((z.toNat : ℤ) : WithTop ℤ); congr 1; omega⟩
        · rintro k ⟨f, hf, he⟩
          have := hge f hf; rw [he] at this
          have : z ≤ (k : ℤ) := by exact_mod_cast this
          omega
  rw [key I hI, key J hJ]

lemma isOrd_span {d : ℕ} {n : ℕ} (b : PolynomialCurvePlace E) (x : Fin d → E)
    (hx : ∀ i, 0 ≤ b.1 (x i)) (g : Fin (n + 1) → MvPolynomial (Fin d) ℂ) :
    IsOrd b x (Ideal.span (Set.range g))
      (Finset.univ.inf' Finset.univ_nonempty (fun i => b.1 (MvPolynomial.aeval x (g i)))) := by
  constructor
  · intro f hf
    induction hf using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Finset.inf'_le _ (Finset.mem_univ i)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact le_trans (le_min hy hz) (b.1.map_add _ _)
    | smul a y _ hy =>
      rw [smul_eq_mul, map_mul, b.1.map_mul]
      calc _ = 0 + Finset.univ.inf' Finset.univ_nonempty
            (fun i => b.1 (MvPolynomial.aeval x (g i))) := (zero_add _).symm
        _ ≤ _ := add_le_add (val_mv_nonneg b x hx a) hy
  · obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun i => b.1 (MvPolynomial.aeval x (g i)))
    exact ⟨g i, Ideal.subset_span ⟨i, rfl⟩, hi.symm⟩

lemma isOrd_mul {d : ℕ} (b : PolynomialCurvePlace E) (x : Fin d → E)
    (I J : Ideal (MvPolynomial (Fin d) ℂ)) (c c' : WithTop ℤ)
    (hI : IsOrd b x I c) (hJ : IsOrd b x J c') : IsOrd b x (I * J) (c + c') := by
  constructor
  · intro f hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro p hp q hq; rw [map_mul, b.1.map_mul]; exact add_le_add (hI.1 p hp) (hJ.1 q hq)
    · intro y z hy hz; rw [map_add]; exact le_trans (le_min hy hz) (b.1.map_add _ _)
  · obtain ⟨p, hp, hpe⟩ := hI.2
    obtain ⟨q, hq, hqe⟩ := hJ.2
    exact ⟨p * q, Ideal.mul_mem_mul hp hq, by rw [map_mul, b.1.map_mul, hpe, hqe]⟩

lemma isOrd_prod {d K : ℕ} (b : PolynomialCurvePlace E) (x : Fin d → E)
    (I : Fin K → Ideal (MvPolynomial (Fin d) ℂ)) (c : Fin K → WithTop ℤ)
    (hI : ∀ j, IsOrd b x (I j) (c j)) (hx : ∀ i, 0 ≤ b.1 (x i)) :
    IsOrd b x (∏ j, I j) (∑ j, c j) := by
  classical
  have : ∀ s : Finset (Fin K), IsOrd b x (∏ j ∈ s, I j) (∑ j ∈ s, c j) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty, Ideal.one_eq_top]
      exact ⟨fun f _ => val_mv_nonneg b x hx f, 1, Submodule.mem_top, by simp⟩
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj]
      exact isOrd_mul b x _ _ _ _ (hI j) ih
  exact this Finset.univ

/-- Polynomials vanishing to order `N` at the origin. -/
lemma val_poly_ge (b : PolynomialCurvePlace E) (u : E) (hu : 0 ≤ b.1 u)
    (q : Polynomial ℂ) (N : ℕ) (hq : ∀ k < N, q.coeff k = 0) :
    N • b.1 u ≤ b.1 (Polynomial.aeval u q) := by
  obtain ⟨r, rfl⟩ := Polynomial.X_pow_dvd_iff.mpr hq
  rw [map_mul, b.1.map_mul, map_pow, Polynomial.aeval_X, b.1.map_pow]
  calc N • b.1 u = N • b.1 u + 0 := (add_zero _).symm
    _ ≤ _ := add_le_add le_rfl (val_poly_nonneg b u hu r)

/-- The key min-comparison. -/
lemma min_cmp (A L L' δ : WithTop ℤ) (e : ℕ) (hL : min L' δ ≤ L) (hδ : A ≤ e • δ) :
    min A (e • L') ≤ min A (e • L) := by
  refine le_min (min_le_left _ _) ?_
  rcases le_total L' δ with h | h
  · have : L' ≤ L := by rw [min_eq_left h] at hL; exact hL
    exact le_trans (min_le_right _ _) (nsmul_le_nsmul_right this e)
  · have : δ ≤ L := by rw [min_eq_right h] at hL; exact hL
    exact le_trans (min_le_left _ _) (hδ.trans (nsmul_le_nsmul_right this e))

end A3S47CC

namespace A3S47CC

variable {E : Type} [Field E] [Algebra ℂ E]

lemma coord_zero {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ) (x : Fin (m + 1) → E) :
    MvPolynomial.aeval x (logarithmicCoordinate c T 0) = x 0 - 1 := by
  simp [logarithmicCoordinate]

lemma coord_succ {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ) (x : Fin (m + 1) → E) (s : Fin m) :
    MvPolynomial.aeval x (logarithmicCoordinate c T s.succ) =
      x s.succ - algebraMap ℂ E (c s) -
        Polynomial.aeval (x 0 - 1) (InterpolationMatrix.truncatedLog (T s)) := by
  simp only [logarithmicCoordinate, Fin.cases_succ, map_sub, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C]
  rw [← Polynomial.aeval_algHom_apply]
  simp

lemma half {m : ℕ} (b : PolynomialCurvePlace E) (x : Fin (m + 1) → E)
    (hx : ∀ i, 0 ≤ b.1 (x i)) (c : Fin m → ℂ) (e : Fin (m + 1) → ℕ)
    (T1 T2 : Fin m → ℕ) (H : ∀ s, e 0 ≤ e s.succ * min (T1 s) (T2 s)) :
    Finset.univ.inf' Finset.univ_nonempty
        (fun i => b.1 (MvPolynomial.aeval x (logarithmicCoordinate c T1 i ^ e i))) ≤
      Finset.univ.inf' Finset.univ_nonempty
        (fun i => b.1 (MvPolynomial.aeval x (logarithmicCoordinate c T2 i ^ e i))) := by
  set u := x 0 - 1
  have hu : 0 ≤ b.1 u := by
    have := b.1.map_sub (x 0) 1
    rw [b.1.map_one] at this
    exact le_trans (le_min (hx 0) le_rfl) this
  refine Finset.le_inf' _ _ (fun i _ => ?_)
  have h0 : Finset.univ.inf' Finset.univ_nonempty
        (fun i => b.1 (MvPolynomial.aeval x (logarithmicCoordinate c T1 i ^ e i))) ≤
      e 0 • b.1 u := by
    refine le_trans (Finset.inf'_le _ (Finset.mem_univ 0)) (le_of_eq ?_)
    show b.1 (MvPolynomial.aeval x (logarithmicCoordinate c T1 0 ^ e 0)) = _
    rw [map_pow, b.1.map_pow, coord_zero]
  have hpow : ∀ (T' : Fin m → ℕ) i, b.1 (MvPolynomial.aeval x (logarithmicCoordinate c T' i ^ e i))
      = e i • b.1 (MvPolynomial.aeval x (logarithmicCoordinate c T' i)) := by
    intro T' i; rw [map_pow, b.1.map_pow]
  refine Fin.cases ?_ (fun s => ?_) i
  · show _ ≤ b.1 (MvPolynomial.aeval x (logarithmicCoordinate c T2 0 ^ e 0))
    rw [hpow, coord_zero]; exact h0
  · show _ ≤ b.1 (MvPolynomial.aeval x (logarithmicCoordinate c T2 s.succ ^ e s.succ))
    rw [hpow]
    have hs := Finset.inf'_le (fun i => b.1 (MvPolynomial.aeval x (logarithmicCoordinate c T1 i ^ e i)))
      (Finset.mem_univ s.succ)
    rw [hpow] at hs
    set L1 := b.1 (MvPolynomial.aeval x (logarithmicCoordinate c T1 s.succ))
    set L2 := b.1 (MvPolynomial.aeval x (logarithmicCoordinate c T2 s.succ))
    set δ := b.1 (MvPolynomial.aeval x (logarithmicCoordinate c T2 s.succ) -
      MvPolynomial.aeval x (logarithmicCoordinate c T1 s.succ))
    have hL : min L1 δ ≤ L2 := by
      have := b.1.map_add (MvPolynomial.aeval x (logarithmicCoordinate c T1 s.succ))
        (MvPolynomial.aeval x (logarithmicCoordinate c T2 s.succ) -
          MvPolynomial.aeval x (logarithmicCoordinate c T1 s.succ))
      rwa [add_sub_cancel] at this
    have hδ : e 0 • b.1 u ≤ e s.succ • δ := by
      have hdiff : MvPolynomial.aeval x (logarithmicCoordinate c T2 s.succ) -
          MvPolynomial.aeval x (logarithmicCoordinate c T1 s.succ) =
          Polynomial.aeval u (InterpolationMatrix.truncatedLog (T1 s) -
            InterpolationMatrix.truncatedLog (T2 s)) := by
        rw [coord_succ, coord_succ, map_sub]; ring
      have hv := val_poly_ge b u hu (InterpolationMatrix.truncatedLog (T1 s) -
          InterpolationMatrix.truncatedLog (T2 s)) (min (T1 s) (T2 s)) (by
        intro k hk
        simp only [InterpolationMatrix.truncatedLog, Polynomial.coeff_sub, PowerSeries.coeff_trunc]
        rw [if_pos (lt_of_lt_of_le hk (min_le_left _ _)),
          if_pos (lt_of_lt_of_le hk (min_le_right _ _)), sub_self])
      rw [← hdiff] at hv
      calc e 0 • b.1 u ≤ (e s.succ * min (T1 s) (T2 s)) • b.1 u :=
            nsmul_le_nsmul_left hu (H s)
        _ = e s.succ • (min (T1 s) (T2 s) • b.1 u) := by rw [mul_nsmul']
        _ ≤ e s.succ • δ := nsmul_le_nsmul_right hv _
    have := min_cmp (e 0 • b.1 u) L2 L1 δ (e s.succ) hL hδ
    calc _ ≤ min (e 0 • b.1 u) (e s.succ • L1) := le_min h0 hs
      _ ≤ min (e 0 • b.1 u) (e s.succ • L2) := this
      _ ≤ e s.succ • L2 := min_le_right _ _

end A3S47CC

open A3S47CC in
theorem solution
    {m : Nat} (c : Fin m → Complex)
    (v : Fin (m + 1) → Rat) (hv : ∀ i, 0 < (v i : Real))
    (R : Rat) (e : Fin (m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, (R : Real) = (e i : Real) * (v i : Real))
    (T : Fin m → Nat)
    (hT : ∀ i, (v i.succ : Real) ≤ (T i : Real) * (v 0 : Real))
    (E : Type) [Field E] [Algebra Complex E]
    (b : OAI.PiExponent.FormalInterpolation.PolynomialCurvePlace E)
    (x : Fin (m + 1) → E) :
    OAI.PiExponent.FormalInterpolation.polynomialCurveIdealContact b x
        (OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal c T e) =
      OAI.PiExponent.FormalInterpolation.polynomialCurveIdealContact b x
        (OAI.PiExponent.FormalInterpolation.logarithmicCenterIdeal c (fun _ => e 0) e) := by
  by_cases hx : ∀ i, 0 ≤ b.1 (x i)
  swap
  · unfold polynomialCurveIdealContact; simp [hx]
  have H : ∀ s : Fin m, e 0 ≤ e s.succ * min (T s) (e 0) := by
    intro s
    have h1 : e 0 ≤ e s.succ * T s := by
      have a1 := hscale 0
      have a2 := hscale s.succ
      have a3 := hT s
      have hv0 := hv 0
      have : (e 0 : ℝ) * (v 0 : ℝ) ≤ ((e s.succ * T s : ℕ) : ℝ) * (v 0 : ℝ) := by
        push_cast
        have hes : (0 : ℝ) ≤ e s.succ := Nat.cast_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left a3 hes]
      exact_mod_cast le_of_mul_le_mul_right this hv0
    have h2 : e 0 ≤ e s.succ * e 0 := Nat.le_mul_of_pos_left _ (he _)
    rcases le_total (T s) (e 0) with h | h
    · rw [min_eq_left h]; exact h1
    · rw [min_eq_right h]; exact h2
  have h1 := isOrd_span b x hx (fun i => logarithmicCoordinate c T i ^ e i)
  have h2 := isOrd_span b x hx (fun i => logarithmicCoordinate c (fun _ => e 0) i ^ e i)
  have heq := le_antisymm (half b x hx c e T (fun _ => e 0) H)
    (half b x hx c e (fun _ => e 0) T (fun s => by rw [min_comm]; exact H s))
  rw [heq] at h1
  unfold logarithmicCenterIdeal
  exact contact_eq_of_isOrd b x _ _ _ h1 h2
